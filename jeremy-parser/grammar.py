from terminals import *
# RULE: PATTERN, [RULE...RULE]
# PATTERN: A regexp pattern applied to the current string to check if it can return a match for this rule.
# List of RULE: Try matching each child rule (in order) on the contents of the current pattern's captured group. If empty, rule is a terminal and there are no children.


GRAMMAR = {
    LABEL_DOCUMENT:
        (None,
         [LABEL_PROOF,
          LABEL_ASSERTION]),

        LABEL_PROOF:
            (r"Proof\.(.*?)(?:Qed|Admitted)\.",
             [LABEL_INTRO,
              LABEL_EXACT]),

            LABEL_INTRO:
                (r"intro (.+?)\.",
                 []),

            LABEL_EXACT:
                (r"exact (\(.+?\))\.",  # We disambiguate the module separator period from sentence period by matching on parenthesis, it is required. This is a bug for Check, since Coq will accept Check <term> without parenthesis.
                 [LABEL_TERM]),

                LABEL_TERM:
                    (r"(.+)",
                     []),

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
                 [])
}
