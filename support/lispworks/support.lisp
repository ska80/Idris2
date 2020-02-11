;;;; -*- Mode: Lisp; Syntax: ANSI-Common-Lisp; indent-tabs-mode: nil; external-format: utf-8; -*-

(cl:defpackage #:idris
  (:use #:cl)
  (:shadow
   #:time
   #:make-condition)

  (:export
   #:*global-optimize-settings*
   #:*optimize-settings*
   #:*optimize-float-settings*

   #:read-args

   #:int+
   #:int-
   #:int*
   #:int/

   #:cast-string-int
   #:cast-string-double

   #:substring

   #:get-tag

   #:delay
   #:force

   #:box
   #:unbox
   #:set-box

   #:make-buffer
   #:buffer-size
   #:set-buffer-byte
   #:get-buffer-byte
   #:set-buffer-int
   #:get-buffer-int
   #:set-buffer-double
   #:get-buffer-double
   #:set-buffer-string
   #:get-buffer-string
   #:read-buffer
   #:write-buffer

   #:file-op
   #:open-stream
   #:close-stream
   #:put-string
   #:get-line
   #:eofp

   #:make-thread
   #:get-thread-data
   #:set-thread-data
   #:make-mutex
   #:lock
   #:unlock
   #:this-thread
   #:make-condition
   #:condition-wait
   #:condition-wait-timeout
   #:condition-signal
   #:condition-broadcast

   #:sleep
   #:usleep
   #:time

   #:cmd-args
   #:error-quit))

(in-package #:idris)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter *global-optimize-settings*
    '(optimize speed (safety 1) (debug 1)))

  (defparameter *optimize-settings*
    '(optimize speed (safety 0) (debug 1)))

  (defparameter *optimize-float-settings*
    '(optimize speed (safety 0) (debug 1) (float 0))))

(declaim #.*global-optimize-settings*)

(setq *read-default-float-format* 'double-float)

(declaim (ftype (function (simple-vector) list) read-args))
(defun read-args (desc)
  (declare #.*optimize-settings*
           (type simple-vector desc))
  (case (svref desc 0)
    ((0) '())
    ((1) (cons (svref desc 2)
               (read-args (svref desc 3))))))

(define-compiler-macro int+ (&whole form x y &environment env)
  (if (and (constantp x env)
           (constantp y env))
      #-lispworks-64bit `,(sys:int32-to-integer (sys:int32+ x y))
      #+lispworks-64bit `,(sys:int64-to-integer (sys:int64+ x y))
      form))

(declaim (inline int+)
         #-lispworks-64bit (ftype (function ((signed-byte 32) (signed-byte 32)) (signed-byte 32)) int+)
         #+lispworks-64bit (ftype (function ((signed-byte 64) (signed-byte 64)) (signed-byte 64)) int+))
(defun int+ (x y)
  (declare #.*optimize-float-settings*
           #-lispworks-64bit (type (signed-byte 32) x y)
           #+lispworks-64bit (type (signed-byte 64) x y))
  #-lispworks-64bit (sys:int32-to-integer (sys:int32+ x y))
  #+lispworks-64bit (sys:int64-to-integer (sys:int64+ x y)))

(define-compiler-macro int- (&whole form x y &environment env)
  (if (and (constantp x env)
           (constantp y env))
      #-lispworks-64bit `,(sys:int32-to-integer (sys:int32- x y))
      #+lispworks-64bit `,(sys:int64-to-integer (sys:int64- x y))
      form))

(declaim (inline int-)
         #-lispworks-64bit (ftype (function ((signed-byte 32) (signed-byte 32)) (signed-byte 32)) int-)
         #+lispworks-64bit (ftype (function ((signed-byte 64) (signed-byte 64)) (signed-byte 64)) int-))
(defun int- (x y)
  (declare #.*optimize-float-settings*
           #-lispworks-64bit (type (signed-byte 32) x y)
           #+lispworks-64bit (type (signed-byte 64) x y))
  #-lispworks-64bit (sys:int32-to-integer (sys:int32- x y))
  #+lispworks-64bit (sys:int64-to-integer (sys:int64- x y)))

(define-compiler-macro int* (&whole form x y &environment env)
  (if (and (constantp x env)
           (constantp y env))
      #-lispworks-64bit `,(sys:int32-to-integer (sys:int32* x y))
      #+lispworks-64bit `,(sys:int64-to-integer (sys:int64* x y))
      form))

(declaim (inline int*)
         #-lispworks-64bit (ftype (function ((signed-byte 32) (signed-byte 32)) (signed-byte 32)) int*)
         #+lispworks-64bit (ftype (function ((signed-byte 64) (signed-byte 64)) (signed-byte 64)) int*))
(defun int* (x y)
  (declare #.*optimize-float-settings*
           #-lispworks-64bit (type (signed-byte 32) x y)
           #+lispworks-64bit (type (signed-byte 64) x y))
  #-lispworks-64bit (sys:int32-to-integer (sys:int32* x y))
  #+lispworks-64bit (sys:int64-to-integer (sys:int64* x y)))

(define-compiler-macro int/ (&whole form x y &environment env)
  (if (and (constantp x env)
           (constantp y env))
      #-lispworks-64bit `,(sys:int32-to-integer (sys:int32/ x y))
      #+lispworks-64bit `,(sys:int64-to-integer (sys:int64/ x y))
      form))

(declaim (inline int/)
         #-lispworks-64bit (ftype (function ((signed-byte 32) (signed-byte 32)) (signed-byte 32)) int/)
         #+lispworks-64bit (ftype (function ((signed-byte 64) (signed-byte 64)) (signed-byte 64)) int/))
(defun int/ (x y)
  (declare #.*optimize-float-settings*
           #-lispworks-64bit (type (signed-byte 32) x y)
           #+lispworks-64bit (type (signed-byte 64) x y))
  #-lispworks-64bit (sys:int32-to-integer (sys:int32/ x y))
  #+lispworks-64bit (sys:int64-to-integer (sys:int64/ x y)))

(defun destroy-prefix (string)
  (declare #.*optimize-settings*
           (type string string))
  (if (and (< 0 (length string))
           (char= (char string 0) #\#))
      ""
      string))

(defun cast-string-int (x)
  (handler-case
      (values
       (parse-integer (destroy-prefix x)))
    (parse-error ()
      0)))

(defun cast-string-double (x)
  (handler-case
      (hcl:parse-float (destroy-prefix x))
    (parse-error ()
      0.0d0)))

(declaim (ftype (function (fixnum fixnum string) string) substring))
(defun substring (off len s)
  (declare #.*optimize-settings*
           (type fixnum off len)
           (type string s))
  (let* ((l (length s))
         (b (max 0 off))
         (x (max 0 len))
         (end (min l (the fixnum (+ b x)))))
    (declare (type fixnum l b x end))
    (subseq s b end)))

(declaim (ftype (function (simple-vector) t) get-tag))
(defun get-tag (x)
  (declare #.*optimize-settings*
           (type simple-vector x))
  (svref x 0))

(defun either-left (x)
  (declare #.*optimize-settings*)
  (vector 0 nil nil x))

(defun either-right (x)
  (declare #.*optimize-settings*)
  (vector 1 nil nil x))

;;; Delay/Force

(defmacro delay (expr)
  `#'(lambda ()
       (declare #.*optimize-settings*)
       ,expr))

(defun force (thunk)
  (declare #.*optimize-settings*
           (type function thunk))
  (funcall thunk))

;;; Box

(declaim (ftype (function (t) simple-vector) box))
(defun box (v)
  (declare #.*optimize-settings*)
  (make-array 1
              :element-type t
              :initial-element v
              :allocation :static))

(declaim (ftype (function (simple-vector) t) unbox))
(defun unbox (box)
  (declare #.*optimize-settings*
           (type simple-vector box))
  (aref box 0))

(declaim (ftype (function (simple-vector t) t) set-box))
(defun set-box (box v)
  (declare #.*optimize-settings*
           (type simple-vector box))
  (setf (aref box 0) v))

;;; Buffers

(deftype byte-vector (&optional size)
  `(simple-array (unsigned-byte 8) (,size)))

(declaim (ftype (function (fixnum) byte-vector) make-buffer))
(defun make-buffer (size)
  (declare #.*optimize-settings*
           (type fixnum size))
  (make-array size
              :element-type '(unsigned-byte 8)
              :initial-element 0
              :allocation :static))

(declaim (ftype (function (byte-vector) fixnum) buffer-size))
(defun buffer-size (buf)
  (declare #.*optimize-settings*
           (type byte-vector buf))
  (length buf))

(declaim (ftype (function (byte-vector fixnum (unsigned-byte 8)) (unsigned-byte 8)) set-buffer-byte))
(defun set-buffer-byte (buf loc val)
  (declare #.*optimize-settings*
           (type byte-vector buf)
           (type fixnum loc)
           (type (unsigned-byte 8) val))
  (setf (aref buf loc) val))

(declaim (ftype (function (byte-vector fixnum) (unsigned-byte 8)) get-buffer-byte))
(defun get-buffer-byte (buf loc)
  (declare #.*optimize-settings*
           (type byte-vector buf)
           (type fixnum loc))
  (aref buf loc))

(declaim (inline write-8-bytes)
         (ftype (function (byte-vector fixnum (unsigned-byte 64))) write-8-bytes))
(defun write-8-bytes (buf start integer)
  (declare #.*optimize-settings*
           (type byte-vector buf)
           (type fixnum start)
           (type (unsigned-byte 64) integer))
  (setf (aref buf start) (ldb (byte 8 56) integer))
  (setf (aref buf (the fixnum (+ start 1))) (ldb (byte 8 48) integer))
  (setf (aref buf (the fixnum (+ start 2))) (ldb (byte 8 40) integer))
  (setf (aref buf (the fixnum (+ start 3))) (ldb (byte 8 32) integer))
  (setf (aref buf (the fixnum (+ start 4))) (ldb (byte 8 24) integer))
  (setf (aref buf (the fixnum (+ start 5))) (ldb (byte 8 16) integer))
  (setf (aref buf (the fixnum (+ start 6))) (ldb (byte 8 8) integer))
  (setf (aref buf (the fixnum (+ start 7))) (ldb (byte 8 0) integer)))

(declaim (ftype (function (byte-vector fixnum (signed-byte 64)) (signed-byte 64)) set-buffer-int))
(defun set-buffer-int (buf loc val)
  (declare #.*optimize-settings*
           (type byte-vector buf)
           (type fixnum loc)
           (type (signed-byte 64) val))
  (write-8-bytes buf loc
                 (ldb (byte 64 0) val))
  val)

(declaim (inline read-4-bytes)
         (ftype (function (byte-vector fixnum) (unsigned-byte 32)) read-4-bytes))
(defun read-4-bytes (buf start)
  (declare #.*optimize-settings*
           (type byte-vector buf)
           (type fixnum start))
  (let ((1-byte (aref buf start))
        (2-byte (aref buf (the fixnum (+ start 1))))
        (3-byte (aref buf (the fixnum (+ start 2))))
        (4-byte (aref buf (the fixnum (+ start 3)))))
    (declare (type (unsigned-byte 8) 1-byte 2-byte 3-byte 4-byte))
    (logior (the (unsigned-byte 32) (ash 1-byte 24))
            (the (unsigned-byte 24) (ash 2-byte 16))
            (the (unsigned-byte 16) (ash 3-byte 8))
            4-byte)))

(declaim (inline read-8-bytes)
         (ftype (function (byte-vector fixnum) (unsigned-byte 64)) read-8-bytes))
(defun read-8-bytes (buf start)
  (declare #.*optimize-settings*
           (type byte-vector buf)
           (type fixnum start))
  (logior (ash (read-4-bytes buf start) 32)
          (read-4-bytes buf (the fixnum (+ start 4)))))

(declaim (ftype (function (byte-vector fixnum) (signed-byte 64)) get-buffer-int))
(defun get-buffer-int (buf loc)
  (declare #.*optimize-settings*
           (type byte-vector buf)
           (type fixnum loc))
  (let ((byte
          (read-8-bytes buf loc)))
    (declare (type (unsigned-byte 64) byte))
    (logior byte (- (mask-field (byte 1 63) byte)))))

(declaim (ftype (function (double-float) (unsigned-byte 64)) encode-float64))
(defun encode-float64 (float)
  (declare #.*optimize-float-settings*
           (type double-float float))
  (multiple-value-bind (sign significand exponent)
      (multiple-value-bind (significand exponent sign)
          (decode-float float)
        (let ((exponent
                (if (= 0 significand)
                    exponent
                    (+ (1- exponent) 1023)))
              (sign (if (= sign 1.0) 0 1)))
          (unless (< exponent 2048)
            (error "Floating point overflow when encoding ~S." float))
          (if (<= exponent 0)
              (values sign
                      (ash (round (* 4503599627370496
                                     significand))
                           exponent)
                      0)
              (values sign
                      (round (* 4503599627370496
                                (1- (* significand 2))))
                      exponent))))
    (let ((bits 0))
      (declare (type (unsigned-byte 64) bits))
      (setf (ldb (byte 1 63) bits) sign
            (ldb (byte 11 52) bits) exponent
            (ldb (byte 52 0) bits) significand)
      bits)))

(declaim (ftype (function ((unsigned-byte 64)) double-float) decode-float64))
(defun decode-float64 (bits)
  (declare #.*optimize-float-settings*
           (type (unsigned-byte 64) bits))
  (let ((sign (ldb (byte 1 63) bits))
        (exponent (ldb (byte 11 52) bits))
        (significand (ldb (byte 52 0) bits)))
    (if (zerop exponent)
        (setf exponent 1)
        (setf (ldb (byte 1 52) significand) 1))
    (let ((float-significand (float significand 1.0d0)))
      (scale-float (if (zerop sign)
                       float-significand
                       (- float-significand))
                   (- exponent 1075)))))

(declaim (ftype (function (byte-vector fixnum double-float) double-float) set-buffer-double))
(defun set-buffer-double (buf loc val)
  (declare #.*optimize-settings*
           (type byte-vector buf)
           (type fixnum loc)
           (type double-float val))
  (write-8-bytes buf loc (encode-float64 val))
  val)

(declaim (ftype (function (byte-vector fixnum) double-float) get-buffer-double))
(defun get-buffer-double (buf loc)
  (declare #.*optimize-settings*
           (type byte-vector buf)
           (type fixnum loc))
  (decode-float64 (read-8-bytes buf loc)))

(declaim (ftype (function (byte-vector fixnum string) string) set-buffer-string))
(defun set-buffer-string (buf loc val)
  (declare #.*optimize-settings*
           (type byte-vector buf)
           (type fixnum loc)
           (type string val))
  (let ((vec (ef:encode-lisp-string val :utf-8)))
    (replace buf vec :start1 loc :end2 (length vec))
    val))

(declaim (ftype (function (byte-vector fixnum fixnum) string) get-buffer-string))
(defun get-buffer-string (buf loc len)
  (declare #.*optimize-settings*
           (type byte-vector buf)
           (type fixnum loc len))
  (ef:decode-external-string buf :utf-8
                             :start loc
                             :end (the fixnum (+ loc len))))

(declaim (ftype (function (stream byte-vector fixnum fixnum) byte-vector) read-buffer))
(defun read-buffer (h buf loc max)
  (declare #.*optimize-settings*
           (type byte-vector buf)
           (type fixnum loc max))
  (read-sequence buf h :start loc :end (the fixnum (+ loc max)))
  buf)

(declaim (ftype (function (stream byte-vector fixnum fixnum) (values)) write-buffer))
(defun write-buffer (h buf loc max)
  (declare #.*optimize-settings*
           (type byte-vector buf)
           (type fixnum loc max))
  (write-sequence buf h :start loc :end (the fixnum (+ loc max)))
  (values))

;;; I/O

(define-condition file-op-error (file-error)
  ((error-type :reader file-op-error-type
               :initarg :type
               :initform nil)))

(defun file-op-error (type)
  (error 'file-op-error :type type))

(defun error-code (c)
  (case (file-op-error-type c)
    (read-error 1)
    (write-error 2)
    (file-does-not-exist-error 3)
    (file-protection-error 4)
    (otherwise 256)))

;; If the file operation raises an error, catch it and return an appropriate error code
(defun file-op (op)
  (handler-case
      (either-right (funcall op))
    (error (c)
      (either-left (error-code c)))))

(defun open-stream (filename mode bin)
  (let ((args
          (if (= bin 1)
              (list :element-type '(unsigned-byte 8))
              (list :element-type 'character
                    :external-format :utf-8))))
    (cond ((string= "r" mode)
           (setq args
                 (append args
                         (list :direction :input))))
          ((string= "w" mode)
           (setq args
                 (append args
                         (list :direction :output
                               :if-exists :supersede
                               :if-does-not-exist :create))))
          ((string= "wx" mode)
           (setq args
                 (append args
                         (list :direction :output
                               :if-exists :supersede
                               :if-does-not-exist :create))))
          ((string= "a" mode)
           (setq args
                 (append args
                         (list :direction :output
                               :if-exists :append
                               :if-does-not-exist :create))))
          ((string= "r+" mode)
           (setq args
                 (append args
                         (list :direction :io))))
          ((string= "w+" mode)
           (setq args
                 (append args
                         (list :direction :io
                               :if-exists :supersede
                               :if-does-not-exist :create))))
          ((string= "w+x" mode)
           (setq args
                 (append args
                         (list :direction :io
                               :if-exists :supersede
                               :if-does-not-exist :create))))
          ((string= "a+" mode)
           (setq args
                 (append args
                         (list :direction :io
                               :if-exists :append
                               :if-does-not-exist :create))))
          (t
           (file-op-error 'unsupported-error)))
    (handler-case
        (apply #'open filename args)
      (file-error ()
        (if (member mode '("r" "r+") :test #'string=)
            (file-op-error 'file-does-not-exist-error)
            (file-op-error 'file-protection-error)))
      (error ()
        (file-op-error 'other-error)))))

(defun close-stream (s)
  (when (streamp s)
    (close s)))

(defun put-string (s str)
  (when (streamp s)
    (handler-case
        (write-string str s)
      (error ()
        (file-op-error 'write-error))))
  0)

(defun get-line (s)
  (if (streamp s)
      (handler-case
          (let ((str (read-line s nil 'eof)))
            (if (eq 'eof str)
                ""
                str))
        (error ()
          (file-op-error 'read-error)))
      ""))

(defun eofp (s)
  (if (eq 'eof (peek-char nil s nil 'eof)) 1 0))

;;; Threads

(defun make-thread (p)
  (mp:process-run-function (format nil "Idris Process ~A" p) () p (vector 0)))

(defun get-thread-data ()
  (mp:process-private-property :idris-thread-data))

(defun set-thread-data (a)
  (setf (mp:process-private-property :idris-thread-data) a))

(defun make-mutex ()
  (mp:make-lock :name "Idris Lock"))

(defun lock (m)
  (mp:process-lock m))

(defun unlock (m)
  (mp:process-unlock m))

(defun this-thread ()
  (sys:current-thread-unique-id))

(defun make-condition ()
  (mp:make-condition-variable :name "Idris Condition Variable"))

(defun condition-wait (c m)
  (mp:condition-variable-wait c m))

(defun condition-wait-timeout (c m tm)
  (mp:condition-variable-wait c m :timeout tm))

(defun condition-signal (c)
  (mp:condition-variable-signal c))

(defun condition-broadcast (c)
  (mp:condition-variable-broadcast c))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (declaim (inline milliseconds->seconds))
  (defun milliseconds->seconds (usecs)
    (declare #.*optimize-float-settings*
             (type integer usecs))
    (let ((secs (round usecs 1000000))
          (micro (mod usecs 1000000)))
      (declare (type integer secs micro))
      (+ (* 0.000001 micro) secs)))
  (declaim (notinline milliseconds->seconds)))

(define-compiler-macro usleep  (&whole form usecs &environment env)
  (if (constantp usecs env)
      `(cl:sleep ,(milliseconds->seconds usecs))
      form))

(defun usleep (usecs)
  (declare #.*optimize-settings*
           (inline milliseconds->seconds))
  (cl:sleep (milliseconds->seconds usecs)))

(defun time ()
  (declare #.*optimize-settings*)
  (- (get-universal-time)
     #.(encode-universal-time 0 0 0 1 1 1970)))

;;; Command line

(defun cmd-args ()
  (labels ((build-args (args)
             (if (endp args)
                 (vector 0 '())
                 (vector 1 '() (car args) (build-args (cdr args))))))
    (build-args sys:*line-arguments-list*)))

(defun error-quit (msg)
  (format t "~&~A~%" msg)
  (lw:quit :status 1 :ignore-errors-p t))
