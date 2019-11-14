;; This buffer is for text that is not saved, and for Lisp evaluation.
;; To create a file, visit it with C-x C-f and enter text in its buffer.

(*let rec fac_cps n k =
if n = 0
then k = 1
else face_cps (n-1) (fun v -> k (n * v));; *)