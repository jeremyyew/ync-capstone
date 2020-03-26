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

KW_INTRO = "intro"
KW_INTROS = "intros"
KW_REWRITE = "rewrite"
KW_RESTART = "Restart"
KW_EXACT = "exact"
KW_REFLEXIVITY = "reflexivity"
KW_CHECK = "Check"
KW_COMPUTE = "Compute"
KW_INDUCTION = "induction"

# REGEXPs
REGEXP_COMMENT = r"\(\*.+?\*\)"
REGEXP_TACTIC_END = r"[\.;]"

ASSERTION_KEYWORDS = r"(?:" + "|".join([
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

TOPLEVEL_KEYWORDS = r"(?:" + "|".join([
    KW_PROOF,
    KW_CHECK,
    KW_COMPUTE
]) + ")"


TACTIC_KEYWORDS = r"(?:" + "|".join([
    KW_INTRO,
    KW_INTROS,
    KW_INDUCTION,
    KW_REWRITE,
    KW_EXACT,
    KW_REFLEXIVITY,
    REGEXP_COMMENT,
    KW_RESTART,
    KW_CHECK,
    KW_COMPUTE
]) + r"(?:\s|\(|\.|;|\s?<-|/s?->|$)?)"

# EXCEPTIONS


class UnmatchedTactic(Exception):
    def __init__(self, remaining):
        self.remaining = remaining
        self.tactic = None
        match = re.match(r"(.+?){}(?={}|$)".format(REGEXP_TACTIC_END,
                                                   TACTIC_KEYWORDS),
                         self.remaining)
        if match:
            self.tactic = match.group(1)


class UnmatchedToken(Exception):
    def __init__(self, remaining):
        self.remaining = remaining
