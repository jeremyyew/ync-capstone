(defvar jeremy-coq-error-found nil
  "Whether error was found after sending script to Coq shell.")

(defvar jeremy-error-hook-active nil
    "Whether jeremy-error-hook should do anything.")

(defun jeremy-error-hook ()
   (progn
     (print "Uh oh")
     (setq jeremy-coq-error-found t)
  ))

(add-hook
 'proof-shell-handle-error-or-interrupt-hook
 (jeremy-error-hook))

(defun jeremy-buffer-content-str ()
  "Get entire buffer contents as string, with no text properties."
  (buffer-substring-no-properties (point-min) (point-max)))

(defun jeremy-syntax-checker (s)
  "Parse for violations of separate rules."
  (print s))



;; Turn on the hook (via the hook-active variable), and process the buffer with the coq shell first.
;; Check if there was error by reading "jeremy-coq-error-found". 
;; If there was an error, just stop.
;; Else if there was no error, parse the active script buffer.
;; Reset "coq-shell-error-found" and turn off the hook.

(defun jeremy-parse-buffer ()
  (interactive)
  (progn
    (setq jeremy-error-hook-active t)
    (proof-process-buffer)
    (if jeremy-coq-error-found (jeremy-syntax-checker (jeremy-buffer-content-str)))
    (setq jeremy-coq-shell-error-found nil)
    (setq jeremy-error-hook-active nil)
    ))

 ;; (defun run-python-script ()
 ;;  (interactive)
 ;;  (shell-command "python3 parser.py"))



;; (global-set-key "\C-x\C-n" `other-window)
;; (defun other-window-backward ()
;;   "Select the previous window."
;;   (interactive)
;;   (other-window -1))
;; (global-set-key "\C-x\C-p" `other-window-backward)

;; (defun scroll-one-line-ahead ()
;;   "Scroll ahead by one line."
;;   (interactive)
;;   (scroll-ahead 1))
;; (defun scroll-one-line-behind ()
;;   "Scroll behind by one line."
;;   (interactive)
;;   (scroll-behind 1))

;; (defun scroll-n-lines-ahead (&optional n)
;;  "Scroll ahead N lines (1 by default)."
;;  (interactive "P")
;;  (scroll-ahead (prefix-numeric-value n)))
;;  (defun scroll-n-lines-behind (&optional n)
;;  "Scroll behind N lines (1 by default)."
;;  (interactive "P")
;;  (scroll-behind (prefix-numeric-value n)))

;;  (global-set-key "\C-q" 'scroll-n-lines-behind)
;; (global-set-key "\C-z" 'scroll-n-lines-ahead)
;; (global-set-key "\C-x\C-q" 'quoted-insert)

;;  (defvar unscroll-to nil
;;    "Text position for next call to 'unscroll'.")

;; (defadvice scroll-up (before remember-for-unscroll
;; 			     activate compile)
;;   "Remember where we started from, for unscroll."
;;   (if (not (eq last-command 'scroll-up))
;;       (setq unscroll-to (point))))

;; (defun unscroll ()
;;   "Jump to location specified by 'unscroll-to'."
;;   (interactive)
;;   (goto-char unscroll-to))

;;  (defvar unscroll-point nil
;;    "Cursor position for next call to 'unscroll'.")
;;  (defvar unscroll-window-start nil
;;    "Window start for next call to 'unscroll'.")


;;  (defvar unscroll-hscroll nil
;;  "Hscroll for next call to 'unscroll'.")
  


;; (defadvice scroll-up (before remember-for-unscroll
;; 			     activate compile)
;;   "Remember where we started from, for unscroll."
;;   (if (not (or (eq last-command 'scroll-up)
;; 	       (eq last-command 'scroll-down)))
;;       (setq unscroll-to (point)
;; 	unscroll-window-start (window-start)
;; 	unscroll-hscroll (window-hscroll)
;; 	)))

;; (defun unscroll ()
;;   "Revert to location specified by 'unscroll-to' and 'unscroll-window-start'."
;;   (interactive)
;;   (or unscroll-point
;;       unscroll-window-start
;;       unscroll-hscroll
;;       (error "Cannot unscroll yet"))
;;   (goto-char unscroll-point)
;;   (set-window-start nil unscroll-window-start)
;;   (set-window-hscroll nil unscroll-hscroll)
;;   )


;; (defadvice scroll-down (before remember-for-unscroll
;; 			       activate compile)
;;   "Remember where we started from, for 'unscroll'."
;;   (if (not (or (eq last-command 'scroll-up)
;; 	       (eq last-command 'scroll-down)))
;;       (setq unscroll-point (point)
;; 	    unscroll-window-start (window-start)
;; 	    unscroll-hscroll (window-hscroll))))

;; (defvar unscrollable nil
;;    "Property for unscroll-maybe-remember.")

;; (put 'scroll-up unscrollable t)
;; (put 'scroll-down 'unscrollable t)
;; (put 'scroll-left 'unscrollable t)
;; (put 'scroll-right 'unscrollable t)

;; (defun unscroll-maybe-remember ()
;; (if (not (get last-command 'unscrollable))
;; (setq unscroll-point (point)
;; unscroll-window-start (window-start)
;; unscroll-hscroll (window-hscroll))))

;; (defadvice scroll-up (before remember-for-unscroll
;; activate compile)
;;   "Remember where we started from, for 'unscroll'."
;;   (unscroll-maybe-remember))

;; (defadvice scroll-down (before remember-for-unscroll
;; activate compile)
;; "Remember where we started from, for 'unscroll'."
;; (unscroll-maybe-remember))

;; (defadvice scroll-left (before remember-for-unscroll
;; activate compile)
;; "Remember where we started from, for 'unscroll'."
;; (unscroll-maybe-remember))

;; (defadvice scroll-right (before remember-for-unscroll
;; activate compile)
;; "Remember where we started from, for 'unscroll'."
;; (unscroll-maybe-remember))
