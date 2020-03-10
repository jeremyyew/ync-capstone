# LABELS
LABEL_DOCUMENT = "DOCUMENT"
LABEL_PROOF = "PROOF"
LABEL_ASSERTION = "ASSERTION"
LABEL_ASSERTION_KEYWORD = "ASSERTION_KEYWORD"
LABEL_ASSERTION_TERM = "ASSERTION_TERM"
LABEL_FORALL = "FORALL"
LABEL_ASSERTION_IDENT = "ASSERTION_IDENT"
LABEL_INTRO = "INTRO"
LABEL_EXACT = "EXACT"
LABEL_TERM = "TERM"
LABEL_TYPE = "TYPE"
LABEL_BINDER = "BINDER"
# LABEL_REWRITE = "REWRITE"

# KEYWORDS
KW_PROOF = "Proof"
KW_QED = "Qed"
KW_LEMMA = "Lemma"
KW_THEOREM = "Theorem"
KW_REMARK = "Remark"
KW_FACT = "Fact"
KW_COROLLARY = "Corollary"
KW_PROPERTY = "Property"
KW_PROPOSITION = "Proposition"
KW_DEFINITION = "Definition"
KW_EXAMPLE = "Example"

ASSERTION_KEYWORDS = "(?:" + "|".join([
    KW_THEOREM,
    KW_LEMMA,
    KW_REMARK,
    KW_FACT,
    KW_COROLLARY,
    KW_PROPERTY,
    KW_PROPOSITION,
    KW_DEFINITION,
    KW_EXAMPLE
]) + ")"