;;; jeremy-coq-by.el --- Generated parser support file

;; Copyright (C) 2019 Jeremy

;; Author: Jeremy <Macintosh@Jeremys-MacBook-Pro-279.local>
;; Created: 2019-10-25 11:59:34+0800
;; Keywords: syntax
;; X-RCS: $Id$

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation, either version 3 of
;; the License, or (at your option) any later version.

;; This software is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; PLEASE DO NOT MANUALLY EDIT THIS FILE!  It is automatically
;; generated from the grammar file jeremy-coq.by.

;;; History:
;;

;;; Code:

(require 'semantic/lex)
(eval-when-compile (require 'semantic/bovine))

;;; Prologue
;;

;;; Declarations
;;
(defconst jeremy-coq-by--keyword-table
  (semantic-lex-make-keyword-table
   '(("+" . PLUS)
     ("1" . NUM))
   'nil)
  "Table of language keywords.")

(defconst jeremy-coq-by--token-table
  (semantic-lex-make-type-table 'nil 'nil)
  "Table of lexical tokens.")

(defconst jeremy-coq-by--parse-table
  `(
    (bovine-toplevel 
     (exp)
     ) ;; end bovine-toplevel

    (exp
     (exp
      PLUS
      exp
      ,(semantic-lambda
	(list '+
	      (nth 0 vals)
	      (nth 2 vals)))
      )
     (NUM)
     ) ;; end exp
    )
  "Parser table.")

(defun jeremy-coq-by--install-parser ()
  "Setup the Semantic Parser."
  (setq semantic--parse-table jeremy-coq-by--parse-table
	semantic-debug-parser-source "jeremy-coq.by"
	semantic-debug-parser-class 'semantic-bovine-debug-parser
	semantic-debug-parser-debugger-source 'semantic/bovine/debug
	semantic-flex-keywords-obarray jeremy-coq-by--keyword-table
	))


;;; Analyzers
;;

;;; Epilogue
;;

(provide 'jeremy-coq-by)

;; Local Variables:
;; version-control: never
;; no-update-autoloads: t
;; End:

;;; jeremy-coq-by.el ends here
