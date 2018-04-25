;;a function which creates primitive databases. It takes
;;an assoc-list (db), and returns a list of three closures which query, add, and delete
;;entries
(defun make-dbms (db)
	   (list
	    #'(lambda (key)
		(cdr (assoc key db)))
	    #'(lambda (key val)
		(push (cons key val)db)
		key)
	    #'(lambda (key)
		(setf db (delete key db :key #'car))
		key)))
;;sum all integers from 1 to n, tail-recursive and optimized
(defun triangle (n)
	   (labels ((tri (c n)
		      (declare (type fixnum n c))
		      (if (zerop n)
			  c
			  (tri (the fixnum (+ n c))
			       (the fixnum (- n 1))))))
	     (tri 0 n)))
;;for efficiency 
(proclaim '(inline last1 single append1 conc1 mklist))
;;attach a new element to the end of list
(defun conc1 (lst obj)
  (nconc lst (list obj)))
(defun append1 (lst obj)
  (append lst (list obj)))
;;ensure that something is a list
(defun mklist (obj)
  (if (listp obj) obj (list obj)))
;;test whether something is a lisp of one element
(defun single (lst)
  (and (consp lst) (not (cdr lst))))
;;returnn the last element in a list
(defun last1 (lst)
  (car (last lst)))
;;compare two sequences and return t if the first one is longer
(defun longer (x y)
  (labels ((compare (x y)
	     (and (consp x)
		  (or (null y)
		      (compare (cdr x) (cdr y))))))
    (if (and (listp x) (listp y))
	(compare x y)
	(> (length x) (length y)))))
;;return a list of whatever non-nil values are returned by the function as it is applied
;;to the elements of a list
(defun filter (fn lst)
	   (let ((acc nil))
	     (dolist (x lst)
	       (let ((val (funcall fn x)))
		 (if val (push val acc))))
	     (nreverse acc)))
;;group a list into sublists of length 2, and group the remainder into final sublist
(defun group (source n)
	   (if (zerop n) (error "zero length"))
	   (labels ((rec (source acc)
		      (let ((rest (nthcdr n source)))
			(if (consp rest)
			    (rec rest (cons (subseq source 0 n) acc))
			    (nreverse (cons source acc))))))
	     (if source (rec source nil) nil)))
;;return a list of all the atoms that are elements of a list, or elements of its elements
(defun flatten (x)
	   (labels ((rec (x acc)
		      (cond ((null x) acc)
			    ((atom x) (cons x acc))
			    (t (rec (car x) (rec (cdr x) acc))))))
	     (rec x nil)))
;;recurse down into sublists, every leaf for which the function returns t is removed
(defun prune (test tree)
	   (labels ((rec (tree acc)
		      (cond ((null tree) (nreverse acc))
			    ((consp (car tree))
			     (rec (cdr tree)
				  (cons (rec (car tree) nil) acc)))
			    (t (rec (cdr tree)
				    (if (funcall test (car tree))
					acc
					(cons (car tree) acc)))))))
	     (rec tree nil)))
(defun find2 (fn lst)
	   (if (null lst)
	       nil
	       (let ((val (funcall fn (car lst))))
		 (if val
		     (values (car lst) val)
		     (find2 fn (cdr lst))))))
;;check if x is before y in a sequence
(defun before (x y lst &key (test #'eql))
	   (and lst
		(let ((first (car lst)))
		  (cond ((funcall test y first) nil)
			((funcall test x first) lst)
			(t (before x y (cdr lst) :test test))))))
;;more exact search
(defun after (x y lst &key (test #'eql))
	   (let ((rest (before y x lst :test test)))
	     (and rest (member x rest :test test))))
;;check for duplication of an element in a list
(defun duplicate (obj lst &key (test #'eql))
	   (member obj (cdr (member obj lst :test test))
		   :test test))
;;split list
(defun split-if (fn lst)
	   (let ((acc nil))
	     (do ((src lst (cdr src)))
		 ((or (null src) (funcall fn (car src)))
		  (values (nreverse acc) src))
	       (push (car src) acc))))
;;take a list and a scoring function, return the score and the element with highest score
(defun most (fn lst)
	   (if (null lst)
	       (values nil nil)
	       (let* ((wins (car lst))
		      (max (funcall fn wins)))
		 (dolist (obj (cdr lst))
		   (let ((score (funcall fn obj)))
		     (when (> score max)
		       (setq wins obj
			     max score))))
		 (values wins max))))
;;much more efficient car of sort
(defun best (fn lst)
	   (if (null lst)
	       nil
	       (let ((wins (car lst)))
		 (dolist (obj (cdr lst))
		   (if (funcall fn obj wins)
		       (setq wins obj)))
		 wins)))
;;return a list of all elements for which fn yields the highest score (and the score itself)
(defun mostn (fn lst)
	   (if (null lst)
	       (values nil nil)
	       (let ((result (list (car lst)))
		     (max (funcall fn (car lst))))
		 (dolist (obj (cdr lst))
		   (let ((score (funcall fn obj)))
		     (cond ((> score max)
			    (setq max score
				  result (list obj)))
			   ((= score max)
			    (push obj result)))))
		 (values (nreverse result) max))))
;;mapping functions (apply a function to a sequence of args)
(defun mapa-b (fn a b &optional (step 1))
  (do ((i a (+ i step))
       (result nil))
      ((> i b) (nreverse result))
    (push (funcall fn i) result)))
(defun map0-n (fn  n)
  (mapa-b fn 0 n))
(defun map1-n (fn n)
  (mapa-b fn 1 n))
;;more general map, which works for sequences of objects of any kind
(defun map-> (fn start test-fn succ-fn)
  (do ((i start (funcall succ-fn i))
       (result nil))
      ((funcall test-fn i) (nreverse result))
    (push (funcall fn i) result)))
;;we could define mapa-b in terms of map->:
(defun mapa-b-2 (fn a b &optional (step 1))
  (map-> fn
	 a
	 #'(lambda (x) (> x b))
	 #'(lambda (x) (+ x step))))
;;nondestructive alternative to mapcan
(defun mappend (fn &rest lsts)
  (apply #'append (apply #'mapcar fn lsts)))
;;mapcar on two lists without unneccesary consing
(defun mapcars (fn &rest lsts)
	   (let ((result nil))
	     (dolist (lst lsts)
	       (dolist (obj lst)
		 (push (funcall fn obj) result)))
	     (nreverse result)))
;;more efficient mapcan
(defun our-mapcan (fn &rest lsts)
	   (apply #'nconc (apply #'mapcar fn lsts)))
;;recursive mapcar for working with trees
(defun rmapcar (fn &rest args)
	   (if (some #'atom args)
	       (apply fn args)
	       (apply #'mapcar
		      #'(lambda (&rest args)
			  (apply #'rmapcar fn args))
		      args)))
;;read a line of input and return it as a list
(defun readlist (&rest args)
  (values (read-from-string
	   (concatenate 'string "("
			(apply #'read-line args)
			")"))))
;;print a question and read the answer
(defun prompt (&rest args)
  (apply #'format *query-io* args)
  (read *query-io*))
;;imitate the Lisp toplevel
(defun break-loop (fn quit &rest args)
	   (format *query-io* "Entering break loop.~%")
	   (loop
	      (let ((in (apply #'prompt args)))
		(if (funcall quit in)
		    (return)
		    (format *query-io* "~A~%" (funcall fn in))))))
;;take any number of arguments and concatenate their printed representations into a string
(defun mkstr (&rest args)
	   (with-output-to-string (s)
	     (dolist (a args) (princ a s))))
;;create a symbol by concatenating args
(defun symb (&rest args)
  (values (intern (apply #'mkstr args))))
;;take a series of objects, print and reread them
(defun reread (&rest args)
  (values (read-from-string (apply #'mkstr args))))
;;take a symbol and return a list of symbols made from the characters in its name
(defun explode (sym)
	   (map 'list #'(lambda (c)
			  (intern (make-string 1
					       :initial-element c)))
		(symbol-name sym)))
;;make a destructive version of a function with (def! #'remove-if #'delete-if)
(defvar *!equivs* (make-hash-table))
(defun ! (fn)
  (or (gethash fn *!EQUIVS*) fn))
(defun def! (fn fn!)
  (setf (gethash fn *!EQUIVS*) fn!))
;;generalized memoizing utility. returns a closure containing a hash-table with the results of previous calls to fn
(defun memoize (fn)
	   (let ((cache (make-hash-table :test #'equal)))
	     #'(lambda (&rest args)
		 (multiple-value-bind (val win) (gethash args cache)
		   (if win
		       val
		       (setf (gethash args cache)
			     (apply fn args)))))))

;;(compose #'list #'1+) returns a fn equivalent to (lambda (x) (list (1+ x))
(defun compose (&rest fns)
	   (if fns
	       (let ((fn1 (car (last fns)))
		     (fns (butlast fns)))
		 #'(lambda (&rest args)
		     (reduce #'funcall fns
			     :from-end t
			     :initial-value (apply fn1 args))))
	       #'identity))
;;complement is a special case of compose
(defun my-complement (pred)
  (compose #'not pred))
;;more closures!
(defun fif (if then &optional else)
  #'(lambda (x)
      (funcall if x)
      (funcall then x)
      (if else (funcall else x))))
(defun fint (fn &rest fns)
  "Function intersection"
	   (if (null fns)
	       fn
	       (let ((chain (apply #'fint fns)))
		 #'(lambda (x)
		     (and (funcall fn x) (funcall chain x))))))
(defun fun (fn &rest fns)
  "Union of a set of predicates"
	   (if (null fns)
	       fn
	       (let ((chain (apply #'fun fns)))
		 #'(lambda (x)
		     (or (funcall fn x) (funcall chain x))))))
;;generate most functions that recurse on successive cdrs of a list
;;(lrec #'(lambda (x f) (cons x (funcall f)))) example of copy-list
(defun lrec (rec &optional base)
	   (labels ((self (lst)
		      (if (null lst)
			  (if (functionp base)
			      (funcall base)
			      base)
			  (funcall rec (car lst)
				   #'(lambda ()
				       (self (cdr lst)))))))
	     #'self))
(defun our-copy-tree (tree)
	   (if (atom tree)
	       tree
	       (cons (our-copy-tree (car tree))
		     (if (cdr tree) (our-copy-tree (cdr tree))))))
(defun count-leaves (tree)
  (if (atom tree)
      1
      (+ (count-leaves (car tree))
	 (or (if (cdr tree) (count-leaves (cdr tree)))
	     1))))
;;find-if generalized for trees, we search for just leaves, not whole subtrees
(defun rfind-if (fn tree)
  (if (atom tree)
      (and (funcall fn tree) tree)
      (or (rfind-if fn (car tree))
	  (if (cdr tree) (rfind-if fn (cdr tree))))))
;;function for recursion on trees: (ttrav #'cons) - our-copy-tree,
;;(ttrav #'nconc #'mklist)-flatten, (ttrav #'(lambda (l r) (+ l (or r 1))) 1) - count-leaves
(defun ttrav (rec &optional (base #'identity))
	   (labels ((self (tree)
		      (if (atom tree)
			  (if (functionp base)
			      (funcall base tree)
			      base)
			  (funcall rec (self (car tree))
				   (if (cdr tree)
				       (self (cdr tree)))))))
	     #'self))
;;more general ttrav: (trec #'(lambda (o l r) (nconc (funcall l) (funcall r))) #'mklist)
;;- flatten,
;;(trec #'(lambda (o l r) (or (funcall l) (funcall r)))
;;	       #'(lambda (tree) (and (oddp tree) tree))) - rfind-if for oddp
(defun trec (rec &optional (base #'identity))
	   (labels
	       ((self (tree)
		  (if (atom tree)
		      (if (functionp base)
			  (funcall base tree)
			  base)
		      (funcall rec tree
			       #'(lambda ()
				   (self (car tree)))
			       #'(lambda ()
				   (if (cdr tree)
				       (self (cdr tree))))))))
	     #'self))
