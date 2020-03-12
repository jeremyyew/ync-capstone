(defvar jeremy-coq-error-found nil
  "Whether error was found after sending script to Coq shell.")

(defvar jeremy-error-hook-active nil
    "Whether jeremy-error-hook is active.")

(defun jeremy-error-hook ()
     (setq jeremy-coq-error-found t))

(add-hook
 'proof-shell-handle-error-or-interrupt-hook
 'jeremy-error-hook)


(defun jeremy-buffer-content-str ()
  "Get entire buffer contents as string, with no text properties."
  (buffer-substring-no-properties (point-min) (point-max)))

(defun jeremy-parser (s)
  "Call parser program in shell and display program output as message."
  (message (shell-command-to-string
	    (format "python3 /Users/Macintosh/github/ync-capstone/jeremy-parser/parser.py --input \"%s\"" s))))
 


;; Turn on the hook (via the hook-active variable), and process the buffer with the coq shell first.
;; Reset proof buffer to start of document, and process script. 
;; Check if there was error by reading "jeremy-coq-error-found". 
;; If there was an error, display message. Else if there was no error, send to jeremy-parser. 
;; Reset "coq-error-found" and turn off the hook.

(defun jeremy-parse-buffer ()
  (interactive)
  (progn
    (setq jeremy-error-hook-active t)
    (goto-char (point-min))
    (proof-goto-point)
    (proof-process-buffer)
    (if jeremy-coq-error-found
	(message "Coq error raised. Please correct and try again.")
      (jeremy-parser (jeremy-buffer-content-str)))
    (setq jeremy-coq-error-found nil)
    (setq jeremy-error-hook-active nil)
    ))
