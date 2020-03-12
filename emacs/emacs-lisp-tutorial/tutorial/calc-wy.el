;;; calc-wy.el --- Generated parser support file

;; Copyright (C) 2020 Jeremy

;; Author: Jeremy <Macintosh@Jeremys-MacBook-Pro-279.local>
;; Created: 2020-02-13 15:46:46+0800
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
;; generated from the grammar file calc.wy.

;;; History:
;;

;;; Code:

(require 'semantic/lex)
(eval-when-compile (require 'semantic/bovine))

;;; Prologue
;;

;;; Declarations
;;
(defconst calc-wy--keyword-table
  (semantic-lex-make-keyword-table 'nil 'nil)
  "Table of language keywords.")

(defconst calc-wy--token-table
  (semantic-lex-make-type-table
   '(("number"
      (NUM)))
   '(("number" :declared t)))
  "Table of lexical tokens.")

(defconst calc-wy--parse-table
  (progn
    (eval-when-compile
      (require 'semantic/wisent/comp))
    (wisent-compile-grammar
     '((NUM)
       nil
       (line
	((NUM)
	 (string-to-number $1))
	((line NUM)
	 (+ $1 string-to-number
	    ($2)))))
     'nil))
  "Parser table.")

(defun calc-wy--install-parser ()
  "Setup the Semantic Parser."
  (semantic-install-function-overrides
   '((parse-stream . wisent-parse-stream)))
  (setq semantic-parser-name "LALR"
	semantic--parse-table calc-wy--parse-table
	semantic-debug-parser-source "calc.wy"
	semantic-flex-keywords-obarray calc-wy--keyword-table
	semantic-lex-types-obarray calc-wy--token-table)
  ;; Collect unmatched syntax lexical tokens
  (semantic-make-local-hook 'wisent-discarding-token-functions)
  (add-hook 'wisent-discarding-token-functions
	    'wisent-collect-unmatched-syntax nil t))


;;; Analyzers
;;
(define-lex-regex-type-analyzer calc-wy--<number>-regexp-analyzer
  "regexp analyzer for <number> tokens."
  semantic-lex-number-expression
  nil
  'NUM)


;;; Epilogue
;;



(provide 'calc-wy)

;; Local Variables:
;; version-control: never
;; no-update-autoloads: t
;; End:

;;; calc-wy.el ends here
