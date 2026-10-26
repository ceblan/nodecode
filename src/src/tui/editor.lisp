;;;; editor.lisp --- the composer's editing engine.
;;;;
;;;; SPDX-License-Identifier: MIT
;;;;
;;;; Copyright (C) 2025  Anthony Green <green@moxielogic.com>
;;;; Derived from cl-tuition's textarea component (src/components/textarea.lisp,
;;;; upstream 6f69592 plus the nodecode fork's readline and soft-wrap work) and
;;;; reduced to the one configuration the shells construct: soft-wrapped at the
;;;; composer's own width, no prompt, no gutter, no painted caret — the shell
;;;; parks the terminal's hardware cursor at EDITOR-CURSOR-SCREEN-POSITION —
;;;; and a height that follows the content up to a cap.
;;;;
;;;; Two authorities the engine leans on instead of carrying its own:
;;;; BREAK-FRAGMENTS (theme) breaks a logical line into visual rows, so the
;;;; caret's visual row is computed by the same rule that paints the row;
;;;; TEXT-DISPLAY-WIDTH (theme) measures the caret's column, so a wide or a
;;;; pictured control glyph parks the cursor where it was painted. A widget
;;;; re-wrapping with its own table could only disagree with the paint.
;;;;
;;;; The engine mutates in place. Every text mutation bumps EPOCH; the joined
;;;; value and the visual-line map are memoized on it (and on the width, for
;;;; the map), so a frame that reads them several times pays the walk once
;;;; per edit rather than once per read. Cursor motion leaves the epoch alone:
;;;; EDITOR-HANDLE-KEY answers whether the text changed, which is what the
;;;; shell's "any real edit ends a history walk" rule asks.

(in-package #:nodecode.evolved)

;;; --- the buffer ----------------------------------------------------------

(nlk:define-record (editor (:constructor make-editor
                               (&key (width 40) (max-height 0) (placeholder "")
                                     (char-limit 0))))
  "The composer's text and caret."
  ;; LINES is the logical lines (a vector of strings, never
  ;; empty), ROW/COL the caret as a logical line index and a character offset
  ;; within it, WIDTH the wrap width in columns, MAX-HEIGHT the cap on visible
  ;; rows (0 = uncapped), OFFSET the first visible visual row, PLACEHOLDER the
  ;; text the shell shows while the buffer is empty, CHAR-LIMIT the total
  ;; character budget (0 = unlimited), EPOCH the edit counter. MAKE-EDITOR
  ;; takes the four the shells choose; an editor starts empty.
  (lines (vector ""))
  (row 0 :type fixnum)
  (col 0 :type fixnum)
  (width 40 :type fixnum)
  (max-height 0 :type fixnum)
  (offset 0 :type fixnum)
  (placeholder "")
  (char-limit 0 :type fixnum)
  ;; The Zig port's, then the two the keymap made worth carrying: UNDO is the
  ;; stack of states an undo returns to, KILL-RING the text the kill commands
  ;; took (newest first), LAST-ACTION what the previous key did — a kill after
  ;; a kill joins the ring entry, a yank-pop after a yank rewrites it — and
  ;; YANK-START/END the span the last yank wrote, which a yank-pop replaces.
  (epoch 0 :type fixnum)
  ;; UNDO-STACK, not UNDO: the record derives EDITOR-<SLOT>, and EDITOR-UNDO
  ;; is the command that pops this one.
  (undo-stack '())
  (kill-ring '())
  (last-action nil)
  (yank-start nil)
  (yank-end nil)
  (value-memo nil)
  (visual-memo nil))

(declaim (inline %editor-touch))
(defun %editor-touch (editor)
  "Mark the text changed: bump the epoch the memos key on."
  (incf editor.epoch)
  editor)

;;; --- undo ----------------------------------------------------------------
;;; One checkpoint per EDIT, not per primitive: the state before an edit's
;;; first mutation, pushed once however many splicings the edit passes
;;; through. A run of typed word characters is one edit (fish's rule), so
;;; Ctrl+- takes back a word and not a letter.

(defparameter *editor-undo-limit* 200
  "How many edits one composer remembers; the oldest fall off. pi keeps every
one, which a shell open for a day cannot afford.")

(defvar *editor-editing* nil
  "How deep the mutation in progress is: the outermost one checkpoints.")

(defun %editor-snapshot (editor)
  "EDITOR's state as a value the buffer cannot mutate through."
  ;; The line vector is copied and the caret is a pair, no cons shared with
  ;; the live record. A line itself is safe to share: every mutation REPLACES
  ;; a line, none writes through one.
  (list (copy-seq editor.lines) editor.row editor.col))

(defun %editor-restore (editor snapshot)
  "Put EDITOR back on SNAPSHOT."
  (destructuring-bind (lines row col) snapshot
    (setf editor.lines lines
          editor.row row
          editor.col col)
    (%editor-touch editor)))

(defun %editor-checkpoint (editor)
  "Remember the state an undo returns to."
  (push (%editor-snapshot editor) editor.undo-stack)
  (when (> (length editor.undo-stack) *editor-undo-limit*)
    (setf (cdr (nthcdr (1- *editor-undo-limit*) editor.undo-stack)) nil))
  editor)

(defmacro %editor-edit ((editor) &body body)
  "BODY mutates EDITOR's buffer as one undoable edit: the outermost mutation
pushes the checkpoint undo returns to, the ones it calls ride on it."
  `(if *editor-editing*
       (progn ,@body)
       (progn (%editor-checkpoint ,editor)
              (let ((*editor-editing* t))
                ,@body))))

(defun %editor-set-lines (editor start end rows &aux (lines editor.lines))
  "Replace logical lines START..END with the strings ROWS."
  (%editor-edit (editor)
    (setf editor.lines (concatenate 'vector (subseq lines 0 start) rows (subseq lines end)))
    editor))

(defun frame-lines (text)
  "TEXT split on newlines, keeping empty rows."
  ;; One empty row for empty TEXT: a frame row exists even when its content is
  ;; blank (UIOP:SPLIT-STRING answers no rows for it).
  (or (uiop:split-string (or text "") :separator '(#\Newline)) (list "")))

(defun split-lines (text)
  "TEXT split on newlines, NIL for empty text rather than the one empty row
FRAME-LINES keeps: a message with no content contributes nothing to a
transcript instead of a blank line."
  ;; The two are one split with two empty conventions, and every newline
  ;; consumer in the shell wants one of them.
  (when (and (stringp text) (plusp (length text)))
    (frame-lines text)))

(defmacro memoized (place (&rest fields) &body body)
  "PLACE's memoized answer while every one of FIELDS is still EQL to what it
was when that answer was made, else BODY, stored back under the fresh fields."
  ;; The one shape every render cache writes by hand, the editor's and
  ;; ui.lisp's: a simple-vector of the inputs the answer is a function of,
  ;; then the answer. The guard and the
  ;; store come from the one FIELDS list, so they cannot read different fields
  ;; or read them in a different order -- that drift is a stale render nothing
  ;; ever invalidates, and it is the reason this is a macro. PLACE is any
  ;; setf-able place read once and written once: a side table's entry, a
  ;; structure slot. Each field is evaluated exactly once, before BODY, and
  ;; anything in PLACE that is not one of these vectors reads as a miss.
  (let ((entry (gensym "ENTRY"))
        (value (gensym "VALUE"))
        (names (loop repeat (length fields) collect (gensym "FIELD"))))
    `(let ((,entry ,place)
           ,@(mapcar #'list names fields))
       (if (and (simple-vector-p ,entry)
                ,@(loop for name in names
                        for index from 0
                        collect `(eql (svref ,entry ,index) ,name)))
           (svref ,entry ,(length fields))
           (let ((,value (progn ,@body)))
             (setf ,place (vector ,@names ,value))
             ,value)))))

(defun editor-value (editor)
  "The whole text, lines joined by newlines. Memoized on the edit epoch."
  (memoized editor.value-memo (editor.epoch)
    (format nil "~{~A~^~%~}" (coerce editor.lines 'list))))

(defun editor-line-count (editor)
  "The number of logical lines."
  (length editor.lines))

(defun %editor-current-line (editor)
  (aref editor.lines editor.row))

(defun editor-reset (editor)
  "Empty the buffer and home the caret."
  (%editor-set-lines editor 0 (length editor.lines) (list ""))
  (setf editor.row 0
        editor.col 0
        editor.offset 0)
  ;; A cleared composer has nothing to undo back to, and nothing to yank-pop
  ;; over: the ring itself is kept, since the line killed before a submit is
  ;; what the next prompt may want.
  (setf editor.undo-stack '()
        editor.last-action nil
        editor.yank-start nil
        editor.yank-end nil)
  (%editor-touch editor))

(defun editor-insert (editor text)
  "Insert TEXT at the caret and leave the caret after it; a newline in TEXT
splits the line."
  ;; Trimmed to CHAR-LIMIT when one is set — the budget counts characters,
  ;; newlines excluded. => EDITOR.
  (let ((text (if (plusp editor.char-limit)
                  (let ((used (reduce #'+ editor.lines :key #'length)))
                    (subseq text 0 (min (length text) (max 0 (- editor.char-limit used)))))
                  text)))
    (when (plusp (length text))
      ;; The caret's line becomes TEXT's lines, the text before the caret
      ;; heading the first and the text after it closing the last.
      (let* ((row editor.row)
             (current (aref editor.lines row))
             (tail (subseq current editor.col))
             (parts (frame-lines text)))
        (setf (first parts) (concatenate 'string (subseq current 0 editor.col) (first parts))
              (car (last parts)) (concatenate 'string (car (last parts)) tail))
        (%editor-set-lines editor row (1+ row) parts)
        (setf editor.row (+ row (length parts) -1)
              editor.col (- (length (car (last parts))) (length tail)))
        (%editor-touch editor))))
  editor)

(defun editor-type-char (editor char &key previous)
  "Insert the typed CHAR as part of the word being typed: a run of word
characters is one undo step (fish's rule, pi's), and a blank starts a new one."
  (if (and (eq previous :type)
           (not (member char '(#\Space #\Tab #\Newline))))
      ;; Riding the previous keystroke's checkpoint is what makes the run one
      ;; step: the edit still happens, it just does not open a new one.
      (let ((*editor-editing* t))
        (editor-insert editor (string char)))
      (editor-insert editor (string char)))
  (setf editor.last-action :type)
  editor)

;;; --- deletion ------------------------------------------------------------

(defun %editor-splice (editor start end &optional (text "") (row editor.row))
  "Replace characters START..END of ROW's line with TEXT."
  (%editor-edit (editor)
    (let ((line (aref editor.lines row)))
      (setf (aref editor.lines row)
            (concatenate 'string (subseq line 0 start) text (subseq line end))))
    (%editor-touch editor)))

(defun editor-delete-char-forward (editor)
  "Delete the character at the caret (Delete, Ctrl+D); at a line end it joins
the next line on."
  (cond ((< editor.col (length (%editor-current-line editor)))
         (%editor-splice editor editor.col (1+ editor.col)))
        ((< editor.row (1- (editor-line-count editor)))
         (%editor-set-lines editor editor.row (+ editor.row 2)
                            (list (concatenate 'string (aref editor.lines editor.row)
                                               (aref editor.lines (1+ editor.row)))))
         (%editor-touch editor)))
  editor)

(defun editor-delete-char-backward (editor)
  "Delete the character before the caret (Backspace): the caret steps left,
then deletes there, so a line start joins the line onto the one above."
  (when (or (plusp editor.col) (plusp editor.row))
    (editor-cursor-left editor)
    (editor-delete-char-forward editor))
  editor)

(defun editor-delete-to-line-end (editor &key accumulate)
  "Kill from the caret to the line end (Ctrl+K)."
  (editor-kill editor editor.col (length (%editor-current-line editor))
               :accumulate accumulate))

(defun editor-delete-to-line-start (editor &key accumulate)
  "Kill from the line start to the caret (Ctrl+U); on a line the caret has
already emptied, take the line itself — never the last one."
  (cond ((plusp editor.col)
         (editor-kill editor 0 editor.col :prepend t :accumulate accumulate))
        ((and (zerop (length (%editor-current-line editor)))
              (> (editor-line-count editor) 1))
         ;; Remove just this empty logical line, not its neighbors.
         (%editor-set-lines editor editor.row (1+ editor.row) nil)
         (when (plusp editor.row)
           (decf editor.row)
           (editor-cursor-end editor))
         (%editor-touch editor)))
  editor)

;;; --- caret motion --------------------------------------------------------

(defun editor-cursor-end (editor)
  "Caret to the end of its line."
  (setf editor.col (length (%editor-current-line editor)))
  editor)

(defun editor-cursor-left (editor)
  "Caret one character left, wrapping to the end of the previous line."
  (cond ((plusp (editor-col editor)) (decf editor.col))
        ((plusp (editor-row editor))
         (decf editor.row)
         (editor-cursor-end editor)))
  editor)

(defun editor-cursor-right (editor)
  "Caret one character right, wrapping to the start of the next line."
  (cond ((< (editor-col editor) (length (%editor-current-line editor)))
         (incf editor.col))
        ((< editor.row (1- (editor-line-count editor))) (incf editor.row) (setf editor.col 0)))
  editor)

;;; --- kills, the ring and undo --------------------------------------------
;;; Readline's kill ring: a delete that takes more than one character
;;; remembers what it took, and Ctrl+Y puts it back. The Zig port had half of
;;; this — Ctrl+K and Ctrl+W killed, and the text was gone for good.

(defparameter *kill-ring-limit* 32
  "How many kills one composer remembers.")

(defun %editor-kill-push (editor text &key prepend accumulate)
  "Remember TEXT as killed from EDITOR. ACCUMULATE joins the newest entry — a
kill right after a kill is one kill, as readline's is — and PREPEND puts TEXT
before it rather than after."
  (when (plusp (length text))
    (cond ((and accumulate editor.kill-ring)
           (setf (first editor.kill-ring)
                 (if prepend
                     (concatenate 'string text (first editor.kill-ring))
                     (concatenate 'string (first editor.kill-ring) text))))
          (t
           (push text editor.kill-ring)
           (when (> (length editor.kill-ring) *kill-ring-limit*)
             (setf (cdr (nthcdr (1- *kill-ring-limit*) editor.kill-ring)) nil)))))
  editor)

(defun editor-kill (editor start end &key prepend accumulate)
  "Delete characters START..END of the caret's line as a kill: the text joins
the ring (joining the kill before it when ACCUMULATE) and the caret stands at
START."
  (let ((text (subseq (%editor-current-line editor) start end)))
    (when (plusp (length text))
      (%editor-splice editor start end)
      (setf editor.col start)
      (%editor-kill-push editor text :prepend prepend :accumulate accumulate)
      (setf editor.last-action :kill)))
  editor)

(defun %editor-delete-span (editor start end)
  "Delete the text between two (ROW . COL) points, joining the lines a span
across lines ends in."
  (destructuring-bind (start-row . start-col) start
    (if (= start-row (car end))
        (progn (%editor-splice editor start-col (cdr end) "" start-row)
               (setf editor.row start-row
                     editor.col start-col))
        (%editor-edit (editor)
          (%editor-set-lines editor start-row (1+ (car end))
                             (list (concatenate 'string
                                                (subseq (aref editor.lines start-row) 0 start-col)
                                                (subseq (aref editor.lines (car end)) (cdr end)))))
          (setf editor.row start-row
                editor.col start-col)
          (%editor-touch editor))))
  editor)

(defun editor-yank (editor)
  "Insert the newest kill at the caret (Ctrl+Y), the caret past it."
  (when editor.kill-ring
    (let ((start (cons editor.row editor.col)))
      (editor-insert editor (first editor.kill-ring))
      (setf editor.yank-start start
            editor.yank-end (cons editor.row editor.col)
            editor.last-action :yank)))
  editor)

(defun editor-yank-pop (editor &key previous)
  "Replace the last yank with the kill before it (Alt+Y), cycling the ring.
PREVIOUS is what the previous key did: a pop follows a yank and nothing else."
  (when (and (eq previous :yank) editor.yank-start (> (length editor.kill-ring) 1))
    ;; A pop refines the yank it follows rather than adding a step of its own,
    ;; so the undo the pair leaves behind takes back the whole yank.
    (let ((*editor-editing* t))
      (%editor-delete-span editor editor.yank-start editor.yank-end)
      ;; The entry just yanked takes the oldest place and the next-newest comes
      ;; up, which is readline's ring turning under one chord.
      (setf editor.kill-ring (append (rest editor.kill-ring) (list (first editor.kill-ring))))
      (let ((start (cons editor.row editor.col)))
        (editor-insert editor (first editor.kill-ring))
        (setf editor.yank-start start
              editor.yank-end (cons editor.row editor.col))))
    (setf editor.last-action :yank))
  editor)

(defun editor-undo (editor)
  "Step back one edit (Ctrl+-): the state a checkpoint remembered."
  (when-let (snapshot (pop editor.undo-stack))
    (%editor-restore editor snapshot)
    (setf editor.last-action nil
          editor.yank-start nil
          editor.yank-end nil))
  editor)

;;; --- words ---------------------------------------------------------------
;;; A word character is alphanumeric, the readline convention.

(defun %prev-word-boundary (line pos &aux (i (min (max 0 pos) (length line))))
  "The start of the word at or before POS, skipping the whitespace first."
  (let ((end (position-if #'alphanumericp line :end i :from-end t)))
    (if end (1+ (or (position-if-not #'alphanumericp line :end end :from-end t) -1)) 0)))

(defun %next-word-boundary (line pos &aux (n (length line)) (i (min (max 0 pos) n)))
  "Past the word at POS and the whitespace after it: the next word's start,
or the line end."
  (let ((end (or (position-if-not #'alphanumericp line :start i) n)))
    (or (position-if #'alphanumericp line :start end) n)))

(defun editor-word (editor direction &key delete accumulate &aux (col editor.col)
                                                       (line (%editor-current-line editor)))
  "Caret to the start of the previous word (DIRECTION -1) or past the current
word, or to the line end (DIRECTION 1); with DELETE, kill that word instead
(readline Ctrl+W / Alt+Backspace, Alt+D / Ctrl+Delete), the caret at its
start and the text on the kill ring — ACCUMULATE joins it to the kill before."
  (let ((to (if (minusp direction)
                (%prev-word-boundary line col)
                (%next-word-boundary line col))))
    (cond ((not delete) (setf editor.col to))
          ((/= to col)
           (let ((text (subseq line (min to col) (max to col))))
             (%editor-splice editor (min to col) (max to col))
             (setf editor.col (min to col))
             (%editor-kill-push editor text
                                :prepend (minusp direction)
                                :accumulate accumulate)
             (setf editor.last-action :kill)))))
  editor)

(defun editor-transpose-chars (editor &aux (line (%editor-current-line editor))
                                           (len (length line))
                                           (col editor.col)
                                           (start (if (>= col len) (- len 2) (1- col))))
  "Swap the characters around the caret (readline Ctrl+T): at the line end
the last two, mid-line the one before and the one at, advancing the caret;
nothing at the line start."
  (when (and (>= len 2) (>= start 0))
    (%editor-splice editor start (+ start 2)
                    (reverse (subseq line start (+ start 2))))
    (when (< col len)
      (incf editor.col)))
  editor)

(defun editor-case-word (editor fn &aux (line (%editor-current-line editor))
                                        (n (length line))
                                        (start (or (position-if #'alphanumericp line
                                                                :start (min editor.col n))
                                                   n)))
  "Apply FN (string -> string) to the word at or after the caret, then move
the caret past it."
  (when (< start n)
    (let ((end (or (position-if-not #'alphanumericp line :start start) n)))
      (%editor-splice editor start end (funcall fn (subseq line start end)))
      (setf editor.col end)))
  editor)

;;; --- visual rows ---------------------------------------------------------
;;; The wrap map: every logical line broken at WIDTH by BREAK-FRAGMENTS, as
;;; a vector of (row start end). Memoized on the epoch and the width.

(defun %editor-visuals (editor &aux (width (max 1 editor.width)))
  (memoized editor.visual-memo (editor.epoch width)
    (coerce (loop for row from 0
                  for line across (editor-lines editor)
                  nconc (loop for (start . end) in (break-fragments line width width)
                              collect (list row start end)))
            'vector)))

(defun %editor-cursor-visual (editor visuals &aux (row editor.row) (col editor.col))
  "Index into VISUALS of the row holding the caret."
  ;; A caret exactly on a break belongs to the row before it: the reserved
  ;; trailing column, not the next row's first cell.
  (or (position-if (lambda (v)
                     (and (= (first v) row) (<= (second v) col (third v))))
                   visuals)
      0))

(defun %editor-visual-step (editor delta &aux (visuals (%editor-visuals editor))
                                              (current (%editor-cursor-visual editor visuals))
                                              (target (+ current delta)))
  "Move the caret DELTA visual rows, keeping its offset within the row."
  ;; => T when it moved.
  (when (and (<= 0 target) (< target (length visuals)))
    (let* ((offset (- editor.col (second (aref visuals current)))) (to (aref visuals target)))
      (setf editor.row (first to)
            editor.col
            (max (second to) (min (+ (second to) offset) (third to))))
      t)))

(defun editor-height (editor &aux (rows (length (%editor-visuals editor))) (cap editor.max-height))
  "Rows the editor shows: the visual row count, at least one, capped at
MAX-HEIGHT when one is set."
  (max 1 (if (plusp cap) (min rows cap) rows)))

(defun %editor-settle (editor &aux (visuals (%editor-visuals editor))
                                   (height (editor-height editor))
                                   (cursor (%editor-cursor-visual editor visuals))
                                   (offset editor.offset))
  "Keep the caret's visual row inside the visible window and the window
inside the content. => the visual map."
  (cond ((< cursor offset) (setf offset cursor))
        ((>= cursor (+ offset height)) (setf offset (1+ (- cursor height)))))
  (setf editor.offset
        (max 0 (min offset (max 0 (- (length visuals) height)))))
  visuals)

(defun editor-visible-lines (editor &aux (visuals (%editor-settle editor)))
  "The visible rows, exactly EDITOR-HEIGHT strings: each visual row's text,
blank past the content. Settles the window around the caret first."
  (loop for i from 0 below (editor-height editor)
        for vi = (+ editor.offset i)
        collect (if (< vi (length visuals))
                    (destructuring-bind (row start end) (aref visuals vi)
                      (subseq (aref editor.lines row) start end))
                    "")))

(defun editor-hidden-lines (editor &aux (visuals (%editor-settle editor))
                                        (top editor.offset)
                                        (bottom (min (1- (length visuals))
                                                     (+ top (editor-height editor) -1))))
  "=> (values ABOVE BELOW): the logical lines that start above the visible
rows and those that end below them -- a line the window cuts in two counts
on the side its hidden part is, so the first line starting in view is line
ABOVE + 1."
  (labels ((line-of (index) (first (aref visuals index)))
           (same-line-p (a b)
             (and (< -1 a (length visuals)) (< -1 b (length visuals)) (= (line-of a) (line-of b)))))
    (if (minusp bottom)
        (values 0 0)
        (values (+ (line-of top) (if (same-line-p (1- top) top) 1 0))
                (+ (- (length editor.lines) 1 (line-of bottom))
                   (if (same-line-p bottom (1+ bottom)) 1 0))))))

(defun editor-cursor-screen-position (editor &aux (visuals (%editor-settle editor))
                                                  (vi (%editor-cursor-visual editor visuals))
                                                  (y (- vi editor.offset)))
  "The caret's cell within the visible rows as (values X Y), zero-based: X
in display columns from the left edge, Y in rows from the top visible row."
  ;; NIL when the caret row is not visible.
  (when (and (<= 0 y) (< y (editor-height editor)) (< vi (length visuals)))
    (let* ((start (second (aref visuals vi)))
           (line (%editor-current-line editor))
           (col (max start (min editor.col (length line)))))
      (values (text-display-width (subseq line start col)) y))))

;;; --- keys ----------------------------------------------------------------

(defun editor-handle-key (editor msg &optional (keymap (resolved-keybinds))
                           &aux (before editor.epoch))
  "Apply the key press MSG to EDITOR under KEYMAP: the composer's motion, kill,
yank, undo and case actions, Enter (and its Ctrl+M / Ctrl+J spellings) as a
newline, and plain characters as text."
  ;; A chord the table does not name is a gesture, not text: it never types its
  ;; base letter. Every key clears LAST-ACTION but the three arms that read it:
  ;; a kill joins the kill before it, a yank-pop follows a yank, and a run of
  ;; typed word characters is one undo step.
  ;; => T when the text changed; motion alone answers NIL.
  (when (nlt:key-press-msg-p msg)
    (let* ((key (nlt:key-event-code msg))
           (mod (nlt:key-event-mod msg))
           (ctrl (nlt:mod-contains mod nlt:+mod-ctrl+))
           (alt (nlt:mod-contains mod nlt:+mod-alt+))
           (last editor.last-action))
      (setf editor.last-action nil)
      ;; The order is the precedence a clash between two actions of this table
      ;; resolves by: what takes a modifier and a longer span first, so a chord
      ;; moved onto a bare key still means what it said.
      (flet ((chord (char) (and (characterp key) (char= key char)))
             (match (action) (keybind-matches-p keymap action key mod)))
        (cond
          ((match :editor-undo) (editor-undo editor))
          ((match :editor-yank-pop) (editor-yank-pop editor :previous last))
          ((match :editor-yank) (editor-yank editor))
          ((match :editor-delete-word-backward)
           (editor-word editor -1 :delete t :accumulate (eq last :kill)))
          ((match :editor-delete-word-forward)
           (editor-word editor 1 :delete t :accumulate (eq last :kill)))
          ((match :editor-delete-to-line-start)
           (editor-delete-to-line-start editor :accumulate (eq last :kill)))
          ((match :editor-delete-to-line-end)
           (editor-delete-to-line-end editor :accumulate (eq last :kill)))
          ((match :editor-delete-char-forward) (editor-delete-char-forward editor))
          ((match :editor-delete-char-backward) (editor-delete-char-backward editor))
          ((match :editor-cursor-word-left) (editor-word editor -1))
          ((match :editor-cursor-word-right) (editor-word editor 1))
          ((match :editor-cursor-doc-start) (setf editor.row 0 editor.col 0))
          ((match :editor-cursor-doc-end)
           (setf editor.row (1- (editor-line-count editor)))
           (editor-cursor-end editor))
          ((match :editor-cursor-line-start) (setf editor.col 0))
          ((match :editor-cursor-line-end) (editor-cursor-end editor))
          ;; Up/Down step one VISUAL row, keeping the caret's offset within it:
          ;; a logical line wider than WIDTH occupies several visual rows, and
          ;; stepping the logical row instead would jump the caret past every
          ;; wrapped row of it.
          ((match :editor-cursor-up) (%editor-visual-step editor -1))
          ((match :editor-cursor-down) (%editor-visual-step editor 1))
          ((match :editor-cursor-left) (editor-cursor-left editor))
          ((match :editor-cursor-right) (editor-cursor-right editor))
          ((match :editor-transpose-chars) (editor-transpose-chars editor))
          ;; readline Alt+C, Alt+L and Alt+U
          ((match :editor-capitalize-word) (editor-case-word editor #'string-capitalize))
          ((match :editor-lowercase-word) (editor-case-word editor #'string-downcase))
          ((match :editor-uppercase-word) (editor-case-word editor #'string-upcase))
          ;; Ctrl+J is the raw LF byte and Ctrl+M the raw CR byte: both are the
          ;; readline newline chord. The shell reads its own newline action
          ;; ahead of this, so what reaches here is a shell that passed Enter on.
          ((or (eq key :enter) (and ctrl (or (chord #\m) (chord #\j))))
           (editor-insert editor (string #\Newline)))
          ((and (characterp key) (not ctrl) (not alt))
           (editor-type-char editor key :previous last))))))
  (/= before editor.epoch))
