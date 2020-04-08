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

(defun jeremy-shell-command-parser (s)
  "Call proof_reader in shell and display program output as message."
  (progn
    (setq c (concat "python3 ~/github/ync-capstone/jeremy-parser/proof_reader.py --input " (shell-quote-argument s)))
    (message (shell-command-to-string c))))


;; Turn on the hook (via the hook-active variable), and process the buffer with the coq shell first.
;; Reset proof buffer to start of document, and process script. 
;; Check if there was error by reading "jeremy-coq-error-found". 
;; If there was an error, display message. Else if there was no error, send to jeremy-parser. 
;; Reset "coq-error-found" and turn off the hook.

(defun jeremy-proof-reader ()
  (interactive)
  (progn
    (setq jeremy-error-hook-active t)
    (goto-char (point-min))
    (proof-goto-point)
    (sit-for 0.03)
    (proof-process-buffer)
    (if jeremy-coq-error-found
	    (message "Coq error raised. Please correct and try again.")
      (jeremy-shell-command-parser (jeremy-buffer-content-str)))
    (setq jeremy-coq-error-found nil)
    (setq jeremy-error-hook-active nil)
  )
)

