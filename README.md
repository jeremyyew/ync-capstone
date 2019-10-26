# YNC Capstone Implementation Note
  
# Types of Parsers 
- LL (l2r, leftmost derivation) 
- LALR (look-ahead, l2r)
- LR (l2r, rightmost derivation)

- What type of grammar do we need? 
  - Context-free as opposed to regular, due to recursive definitions.
  - Left to Right? 
  - Do we need to look ahead? 
  - Do we need to obtain leftmost derivation? 
  
# Parser Comparison
- https://medium.com/@chetcorcos/introduction-to-parsers-644d1b5d7f3d
- https://www.gnu.org/software/emacs/manual/html_mono/wisent.html
- https://www.gnu.org/software/emacs/manual/html_node/semantic/Using-Semantic.html#Using-Semantic
- https://www.gnu.org/software/emacs/manual/html_mono/bovine.html

- Semantic/Semantic Bovinator
  - Is a lexer, parser-generator, and parser. A parser framework. Contains wisent, seems to be part of a broader framework for writing advanced language tools/features such as auto-completion, highlighting, etc.
- Wisent (LALR). Supposed to be more advanced. Port of bison. Is this related to Bovine?? 
- Bovine (LL). Supposed to be simple.

# Requirements of grammar
**Primary**
1. Raise exception if there exists a tactic not in subset of allowed tactics.
   1. Needs to check `sentence -> assertion proof -> tactic`.
2. Raise exception if rewrite does not have complete number of args. 
   1. Needs to check `sentence -> assertion proof -> tactic`.

**Secondary**
1. Suggest naming conventions? E.g. hypothesis.  
2. Indentation - consider auto-indenting on user's behalf, especially since it is impossible to detect when indentation level should decrease unless we read the coq shell output.

# Coq BNF 
```
sentence ::= assertion proof 
            | Definition ... . 
            | Inductive ... . 
            | Fixpoint ... . 
            | ... .
assertion ::=  assertion_keyword ident ... .
assertion_keyword ::=  Theorem 
                    | Lemma 
                    | Remark 
                    | Fact 
                    | Corollary 
                    | Proposition 
                    | Definition 
                    | Example
ident ::= string
string := char | char string
char :== a..z ∣ A..Z ∣ 0...9 | _
proof ::= Proof . tactic_invocations Qed . 
        | Proof . tactic_invocations Defined . 
        | Proof . tactic_invocations Admitted .
        | Proof . tactic_invocations Abort .
tactic_invocations ::= tactic_invocation | tactic_invocation tactic_invocations
tactic_invocation ::= [- | + | >] tactic .
tactic ::= intro ident 
        | intros intro_pattern_list 
        | clear
        | exact rule_application 
        | apply term 
        | split 
        | left 
        | right 
        | rewrite_expr
        | Compute ...
        | Check ...
        | reflexivity 
rewrite_expr ::= rewrite -> rule in ...
                | rewrite -> term args
                | rewrite <- term args
```
To be accounted for: 
```
// How to verify number of args? 
intro_pattern_list
term 
bindings
Ltac
Require 
Notation 
Comments
occurence clauses
```
```