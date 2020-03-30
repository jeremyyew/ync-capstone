import re

# LABELS
LABEL_DOCUMENT = "DOCUMENT"
LABEL_PROOF = "PROOF"
LABEL_ASSERTION = "ASSERTION"
LABEL_ASSERTION_KEYWORD = "ASSERTION_KEYWORD"
LABEL_ASSERTION_TERM = "ASSERTION_TERM"
LABEL_FORALL = "FORALL"
LABEL_ASSERTION_IDENT = "ASSERTION_IDENT"
LABEL_INTRO = "INTRO"
LABEL_INTROS = "INTROS"
LABEL_EXACT = "EXACT"
LABEL_TERM = "TERM"
LABEL_TYPE = "TYPE"
LABEL_BINDER = "BINDER"
LABEL_REQUIRE_IMPORT = "REQUIRE_IMPORT"
LABEL_REWRITE = "REWRITE"
LABEL_REWRITE_ARROW = "REWRITE_ARROW"
LABEL_REFLEXIVITY = "REFLEXIVITY"
LABEL_COMMENT = "COMMENT"
LABEL_RESTART = "RESTART"
LABEL_CHECK = "CHECK"
LABEL_COMPUTE = "COMPUTE"
LABEL_INDUCTION = "INDUCTION"
LABEL_SPLIT = "SPLIT"
LABEL_BULLET = "BULLET"

# KEYWORDS
KW_PROOF = "Proof"
KW_QED = "Qed"
KW_ADMITTED = "Admitted"
KW_ABORT = "Abort"
KW_LEMMA = "Lemma"
KW_THEOREM = "Theorem"
KW_REMARK = "Remark"
KW_FACT = "Fact"
KW_COROLLARY = "Corollary"
KW_PROPERTY = "Property"
KW_PROPOSITION = "Proposition"
KW_DEFINITION = "Definition"
KW_EXAMPLE = "Example"
KW_FORALL = "forall"

KW_INTRO = "intro"
KW_INTROS = "intros"
KW_INDUCTION = "induction"
KW_REWRITE = "rewrite"
KW_RESTART = "Restart"
KW_EXACT = "exact"
KW_REFLEXIVITY = "reflexivity"
KW_CHECK = "Check"
KW_COMPUTE = "Compute"
KW_SPLIT = "split"

REGEXP_COMMENT = r"\(\*.+?\*\)"

KW_GRP_TACTIC = [
    KW_INTRO,
    KW_INTROS,
    KW_INDUCTION,
    KW_REWRITE,
    KW_RESTART,
    KW_EXACT,
    KW_REFLEXIVITY,
    KW_CHECK,
    KW_COMPUTE,
    KW_SPLIT,
    REGEXP_COMMENT
]

KW_GRP_DOCUMENT = [
    KW_PROOF,
    KW_CHECK,
    KW_COMPUTE
]

KW_GRP_ASSERTION = [
    KW_THEOREM,
    KW_LEMMA,
    KW_REMARK,
    KW_FACT,
    KW_COROLLARY,
    KW_PROPERTY,
    KW_PROPOSITION,
    KW_DEFINITION,
    KW_EXAMPLE
]

# REGEXPs


def regx_non_capture_alt(grp):
    return f"(?:{'|'.join(grp)})"


REGEXP_BULLET = r"[\+\-\*]+\s*"
REGEXP_TACTIC_END = r"[\.;]"
REGEXP_TACTIC = regx_non_capture_alt(KW_GRP_TACTIC)
REGEXP_TACTIC_LOOKAHEAD = f"(?={REGEXP_TACTIC}|$)"
REGEXP_DOCUMENT = regx_non_capture_alt(KW_GRP_DOCUMENT)
REGEXP_ASSERTION = regx_non_capture_alt(KW_GRP_ASSERTION)

# EXCEPTIONS


class UnmatchedTactic(Exception):
    def __init__(self, remaining):
        self.remaining = remaining
        self.tactic = None
        match = re.match(fr"(.+?){REGEXP_TACTIC_END}{REGEXP_TACTIC_LOOKAHEAD}",
                         self.remaining)
        if match:
            self.tactic = match.group(1)


class UnmatchedToken(Exception):
    def __init__(self, remaining):
        self.remaining = remaining
