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
#  induction
#   assert
#   destruct
# X reflexivity
# X exact (with or without parenthesis)
#   unfold
#   apply.
# - Line number would be nice.
# - Fold-unfold lemmas?


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
            (r"Proof\.(.*?)(?:Qed|Admitted|Abort)\.",
             [LABEL_INTROS,
              LABEL_INTRO,
              LABEL_INDUCTION,
              LABEL_EXACT,
              LABEL_REWRITE,
              LABEL_REFLEXIVITY,
              LABEL_COMMENT,
              LABEL_RESTART,
              LABEL_CHECK,
              LABEL_COMPUTE]),

            LABEL_INTROS:
                (r"intros\s?(.*?){}".format(REGEXP_TACTIC_END),
                 []),

            LABEL_INTRO:
                (r"intro\s?(.*?){}".format(REGEXP_TACTIC_END),
                 []),

            LABEL_INDUCTION:
                (r"{}\s(.*?){}(?={}|$)".format(KW_INDUCTION,
                                               REGEXP_TACTIC_END,
                                               TACTIC_KEYWORDS),
                 []),
            LABEL_EXACT:
                (r"{}\s?(\(?.+?\)?){}(?={}|$)".format(KW_EXACT,
                                                      REGEXP_TACTIC_END,
                                                      TACTIC_KEYWORDS),
                 [LABEL_TERM]),

            LABEL_REWRITE:
                (r"{}\s?((?:->|<-)?\s?\(?.+?\)?){}(?={}|$)".format(KW_REWRITE,
                                                                   REGEXP_TACTIC_END,
                                                                   TACTIC_KEYWORDS),
                 [LABEL_REWRITE_ARROW, LABEL_TERM]),

                LABEL_REWRITE_ARROW:
                    (r"(->|<-)\s?",
                     []),
                LABEL_TERM:
                    (r"(.+)",
                        []),

            LABEL_REFLEXIVITY:
                (r"({}){}".format(KW_REFLEXIVITY,
                                  REGEXP_TACTIC_END),
                 []),

            LABEL_RESTART:
                (r"({}\.)".format(KW_RESTART), []),

        LABEL_ASSERTION:
            ("(" + ASSERTION_KEYWORDS + r" .+?)\.",
             [LABEL_ASSERTION_KEYWORD,
              LABEL_ASSERTION_IDENT,
              LABEL_FORALL,
              LABEL_ASSERTION_TERM]),

            LABEL_ASSERTION_KEYWORD:
                ("(" + ASSERTION_KEYWORDS + ")",
                 []),

            LABEL_ASSERTION_IDENT:
                (r"\s*([^\s]+?)\s*:\s*",
                 []),

            LABEL_FORALL:
                (r"forall \(?(.+?)\)?,\s*",
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
        (r"{}\s?(\(?.+?\)?)\.(?={}|{}|$)".format(KW_CHECK,
                                                 TACTIC_KEYWORDS,
                                                 ASSERTION_KEYWORDS),
         []),
    LABEL_COMPUTE:
        (r"{}\s?(\(?.+?\)?)\.(?={}|{}|$)".format(KW_COMPUTE,
                                                 TACTIC_KEYWORDS,
                                                 ASSERTION_KEYWORDS),
         []),
    LABEL_COMMENT:
        # Note: Will not parse nested comments properly!
        (r"\s?(\(\*.+?\*\))\s?",
         #  r"(?:\s?\(\*.+?\*\)\s?)"
         [])
}
