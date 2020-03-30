from terminals import *

# TODO:
# X Define assertion and collect arity signatures.
# X Only collect for those that have been proven. (accept admitted).
# X Emacs command to call program.
# X Send back warning messages and display them.
# - Warnings:
#   rewrite: missing arrow
#   intro/intros: no args.
# - Accept:
# X require
# X  intros
# X rewrite
# X comment
# X Abort
# X Restart
# X Check
# X Compute
# X reflexivity
# X exact (with or without parenthesis)
# split + bullet point
# intro patterns?
# Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.
# symmetry.
# induction
# assert
# destruct
# unfold/fold.
# apply.
# rewrite in _.


# RULE: PATTERN, [RULE...RULE]
# PATTERN: A regexp pattern applied to the current string to check if it can return a match for this rule.
# List of RULE: Try matching each child rule (in order) on the contents of the current pattern's captured group. If empty, rule is a terminal and there are no children.

GRAMMAR = {
    LABEL_DOCUMENT:
        (None,
         [LABEL_REQUIRE_IMPORT,
          LABEL_PROOF,
          LABEL_ASSERTION,
          LABEL_COMMENT,
          LABEL_CHECK,
          LABEL_COMPUTE]),

        LABEL_REQUIRE_IMPORT:
            (r"Require Import (.+?)\.",
             []),

        LABEL_PROOF:
            (fr"{KW_PROOF}\.(.*?)(?:{KW_QED}|{KW_ADMITTED}|{KW_ABORT})\.",
             [LABEL_INTROS,
              LABEL_INTRO,
              LABEL_INDUCTION,
              LABEL_EXACT,
              LABEL_REWRITE,
              LABEL_REFLEXIVITY,
              LABEL_COMMENT,
              LABEL_RESTART,
              LABEL_CHECK,
              LABEL_COMPUTE,
              LABEL_SPLIT]),

            LABEL_INTROS:
                (fr"{KW_INTROS}\s?(.*?){REGEXP_TACTIC_END}",
                 []),

            LABEL_INTRO:
                (fr"{KW_INTRO}\s?(.*?){REGEXP_TACTIC_END}",
                 []),

            LABEL_INDUCTION:
                (fr"{KW_INDUCTION}\s(.*?){REGEXP_TACTIC_END}{REGEXP_TACTIC_LOOKAHEAD}",
                 []),
            LABEL_EXACT:
                (fr"{KW_EXACT}\s?(\(?.+?\)?){REGEXP_TACTIC_END}{REGEXP_TACTIC_LOOKAHEAD}",
                 [LABEL_TERM]),

            LABEL_REWRITE:
                (fr"{KW_REWRITE}\s?((?:->|<-)?\s?\(?.+?\)?){REGEXP_TACTIC_END}{REGEXP_TACTIC_LOOKAHEAD}",
                 [LABEL_REWRITE_ARROW, LABEL_TERM]),

                LABEL_REWRITE_ARROW:
                    (r"(->|<-)\s?",
                     []),
                LABEL_TERM:
                    (r"(.+)",
                        []),

            LABEL_REFLEXIVITY:
                (fr"({KW_REFLEXIVITY}){REGEXP_TACTIC_END}",
                 []),

            LABEL_RESTART:
                (fr"({KW_RESTART}\.)", []),

            LABEL_SPLIT:
                (fr"({KW_SPLIT}\.)", []),

        LABEL_ASSERTION:
            (fr"({REGEXP_ASSERTION} .+?:.+?)\.(?={REGEXP_ASSERTION}|{REGEXP_DOCUMENT}|$)",
             [LABEL_ASSERTION_KEYWORD,
              LABEL_ASSERTION_IDENT,
              LABEL_FORALL,
              LABEL_ASSERTION_TERM]),

            LABEL_ASSERTION_KEYWORD:
                (fr"({REGEXP_ASSERTION})",
                 []),

            LABEL_ASSERTION_IDENT:
                (r"\s*([^\s]+?)\s*:\s*",
                 []),

            LABEL_FORALL:
                (fr"{KW_FORALL} \(?(.+?)\)?,\s*",
                 [LABEL_BINDER, LABEL_TYPE]),

                LABEL_BINDER:
                    (r"([^:\s]+)\s*",
                     []),

                LABEL_TYPE:
                    (r":\s*(.+)",
                     []),

            LABEL_ASSERTION_TERM:
                (r"(.+)",
                 []),

        LABEL_CHECK:
            (fr"{KW_CHECK}\s?(\(?.+?\)?)\.(?={REGEXP_TACTIC}|{REGEXP_ASSERTION}|$)",
             []),

    LABEL_COMPUTE:
        (fr"{KW_COMPUTE}\s?(\(?.+?\)?)\.(?={REGEXP_TACTIC}|{REGEXP_ASSERTION}|$)",
         []),
    LABEL_COMMENT:
        # Note: Will not parse nested comments.
        (r"\s?(\(\*.+?\*\))\s?",
         [])
}
