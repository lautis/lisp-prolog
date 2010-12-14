Yet another toy Lisp implementation. Written in Prolog.

Developed on SWI-Prolog.

    run("(defun factorial (a)
      (if (eq 1 a)
        1
        (* a (factorial (- a 1)))))
        (factorial 5)", R).
    R = 120.