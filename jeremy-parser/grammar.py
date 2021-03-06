from constants import *

# TODO:
# Fixpoint ident binders := term
# Warn when tactic used outside proof.
# Factor out collect_arity from check_arity.
# Refactor TERM and check_arity so that first term is parent term.


# RULE: PATTERN, [RULE...RULE]
# PATTERN: A regexp pattern applied to the current string to check if it can return a match for this rule.
# List of RULE: Try matching each child rule (in order) on the contents of the current pattern's captured group. If empty, rule is a terminal and there are no children.

GRAMMAR = {
    LABEL_DOCUMENT:
        (None,
         [
             LABEL_ASSERTION,
             LABEL_CHECK,
             LABEL_COMMENT,
             LABEL_COMPUTE,
             LABEL_FIXPOINT,
             LABEL_INDUCTIVE,
             LABEL_LTAC,
             LABEL_NOTATION,
             LABEL_PROOF,
             LABEL_REQUIRE_IMPORT,
             LABEL_SEARCH,
         ]),

        LABEL_ASSERTION:
            (fr"({REGEXP_ASSERTION} .+?:.+?)\.{REGEXP_DOC_LOOKAHEAD}",
             [LABEL_ASSERTION_KEYWORD,
              LABEL_ASSERTION_IDENT,
              LABEL_FORALL,
              LABEL_ASSERTION_TERM]),

            LABEL_ASSERTION_KEYWORD: (fr"({REGEXP_ASSERTION})", []),

            LABEL_ASSERTION_IDENT: (r"\s*(\S+?)\s*:\s*", []),

            LABEL_FORALL:
                (fr"{KW_FORALL} \(?(.+?)\)?,\s*",
                 [LABEL_BINDER, LABEL_TYPE]),

                LABEL_BINDER: (r"([^:\s]+)\s*", []),

                LABEL_TYPE: (r":\s*(.+)", []),

            LABEL_ASSERTION_TERM: (r"(.+)", []),

        LABEL_CHECK: (fr"({KW_CHECK}\s?\(?.+?\)?\.){REGEXP_DOC_LOOKAHEAD}", []),

        LABEL_CLEAR: (fr"({KW_CLEAR}(?:\s\S+?)+?{REGEXP_TACTIC_END})", []),

        # Note: Will not parse nested comments.
        LABEL_COMMENT: (fr"{REGEXP_COMMENT}", []),

        LABEL_COMPUTE: (fr"({KW_COMPUTE}\s?\(?.+?\)?\.){REGEXP_DOC_LOOKAHEAD}", []),

        LABEL_FIXPOINT: (fr"({KW_FIXPOINT}.+?end\.)", []),

        LABEL_INDUCTIVE: (fr"({KW_INDUCTIVE}.+?:=.+?\.)", []),

        LABEL_LTAC: (fr"({KW_LTAC}\s\S+?(?:\s\S+?)+?\s?:=.+?\.){REGEXP_DOC_LOOKAHEAD}", []),

        LABEL_NOTATION: (fr"({KW_NOTATION}\s?\".+?\"\s?:=\s?.+?\.){REGEXP_DOC_LOOKAHEAD}", []),

        LABEL_PROOF:
            (fr"{KW_PROOF}\.(.*?)(?:{KW_QED}|{KW_ADMITTED}|{KW_ABORT})\.",
             LABEL_GRP_TACTIC),

            LABEL_APPLY:
                (fr"{KW_APPLY}({REGEXP_TERM}){REGEXP_IN_OCCURRENCE}{REGEXP_TACTIC_END}{REGEXP_TACTIC_LOOKAHEAD}",
                 [LABEL_TERM]),

            LABEL_ASSERT: (fr"({KW_ASSERT}\s?\(.+?\){REGEXP_TACTIC_END}){REGEXP_TACTIC_LOOKAHEAD}", []),

            LABEL_BULLET: (fr"{REGEXP_BULLET}", []),

            LABEL_DESTRUCT:
                (fr"{KW_DESTRUCT}({REGEXP_TERM}){REGEXP_AS_INTROPATTERN}{REGEXP_IN_OCCURRENCE}{REGEXP_TACTIC_END}{REGEXP_TACTIC_LOOKAHEAD}",
                 [LABEL_TERM]),

            LABEL_EXACT:
                (fr"{KW_EXACT}({REGEXP_TERM}){REGEXP_TACTIC_END}{REGEXP_TACTIC_LOOKAHEAD}",
                 [LABEL_TERM]),

                LABEL_TERM: (r"\s?(.+)", []),

            LABEL_ENOUGH: (fr"({KW_ENOUGH}\s?\(.+?\){REGEXP_AS_INTROPATTERN}{REGEXP_TACTIC_END}){REGEXP_TACTIC_LOOKAHEAD}", []),

            LABEL_EXISTS:
                (fr"{KW_EXISTS}({REGEXP_TERM}){REGEXP_TACTIC_END}{REGEXP_TACTIC_LOOKAHEAD}",
                 [LABEL_TERM]),

            LABEL_FOCUSED:
                (fr"{REGEXP_FOCUSED}",
                 LABEL_GRP_TACTIC),

            LABEL_FOLD: (fr"({KW_FOLD}\s\S+?{REGEXP_TACTIC_END})", []),


            LABEL_FOLD_UNFOLD: (fr"({KW_FOLD_UNFOLD}\s\S+?{REGEXP_TACTIC_END})", []),

            LABEL_INDUCTION: (
                fr"({KW_INDUCTION}\s?.*?{REGEXP_AS_INTROPATTERN}{REGEXP_USING_TERM}{REGEXP_IN_OCCURRENCE}{REGEXP_TACTIC_END}){REGEXP_TACTIC_LOOKAHEAD}", []),

            LABEL_INTRO: (fr"{KW_INTRO}(?:\s(\S+?)|()){REGEXP_TACTIC_END}", []),

            LABEL_INTROS: (fr"{KW_INTROS}(?:\s?([^\.]+?)|()){REGEXP_TACTIC_END}", []),

            LABEL_LEFT: (fr"({KW_LEFT}{REGEXP_TACTIC_END})", []),

            LABEL_RIGHT: (fr"({KW_RIGHT}{REGEXP_TACTIC_END})", []),

            LABEL_REFLEXIVITY: (fr"({KW_REFLEXIVITY}{REGEXP_TACTIC_END})", []),

            LABEL_RESTART: (fr"({KW_RESTART}{REGEXP_TACTIC_END})", []),

            LABEL_REWRITE:
                (fr"{KW_REWRITE}({REGEXP_REWRITE_ARROW}?{REGEXP_TERM_OPTIONAL_SPACE}){REGEXP_IN_OCCURRENCE}{REGEXP_AT_OCCURRENCE}{REGEXP_TACTIC_END}{REGEXP_TACTIC_LOOKAHEAD}",
                 [LABEL_REWRITE_ARROW,
                  LABEL_TERM]),

                LABEL_REWRITE_ARROW: (fr"({REGEXP_REWRITE_ARROW})", []),

            LABEL_SEARCH:
                (fr"{KW_SEARCH}({REGEXP_TERM})\.{REGEXP_DOC_LOOKAHEAD}",
                 [LABEL_TERM]),

            LABEL_SPLIT: (fr"({KW_SPLIT}{REGEXP_TACTIC_END})", []),

            LABEL_SYMMETRY: (fr"({KW_SYMMETRY}{REGEXP_TACTIC_END})", []),

            LABEL_UNFOLD: (fr"({KW_UNFOLD}(?:\s\S+?)+?{REGEXP_AT_OCCURRENCE}{REGEXP_IN_OCCURRENCE}{REGEXP_TACTIC_END})", []),

        LABEL_REQUIRE_IMPORT: (fr"({KW_REQUIRE_IMPORT}(?:\s\S+?)+?\.){REGEXP_DOC_LOOKAHEAD}", []),

}
