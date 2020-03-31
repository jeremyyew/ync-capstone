import re

# LABEL CONSTANTS.
# Toplevel labels.
LABEL_DOCUMENT = "DOCUMENT"
LABEL_REQUIRE_IMPORT = "REQUIRE_IMPORT"
LABEL_PROOF = "PROOF"
LABEL_ASSERTION = "ASSERTION"

# Toplevel subcomponent labels.
LABEL_ASSERTION_KEYWORD = "ASSERTION_KEYWORD"
LABEL_ASSERTION_TERM = "ASSERTION_TERM"
LABEL_FORALL = "FORALL"
LABEL_ASSERTION_IDENT = "ASSERTION_IDENT"

# Tactic command labels (alphabetically sorted).
LABEL_APPLY = "APPLY"
LABEL_ASSERT = "ASSERT"
LABEL_BULLET = "BULLET"
LABEL_CHECK = "CHECK"
LABEL_COMMENT = "COMMENT"
LABEL_COMPUTE = "COMPUTE"
LABEL_DESTRUCT = "DESTRUCT"
LABEL_EXACT = "EXACT"
LABEL_INDUCTION = "INDUCTION"
LABEL_INTRO = "INTRO"
LABEL_INTROS = "INTROS"
LABEL_REFLEXIVITY = "REFLEXIVITY"
LABEL_RESTART = "RESTART"
LABEL_REWRITE = "REWRITE"
LABEL_SPLIT = "SPLIT"
LABEL_SYMMETRY = "SYMMETRY"

# Tactic subcomponent labels.
LABEL_REWRITE_ARROW = "REWRITE_ARROW"
LABEL_TERM = "TERM"
LABEL_TYPE = "TYPE"
LABEL_BINDER = "BINDER"

# KEYWORD CONSTANTS.
# Toplevel keywords.
KW_PROOF = "Proof"
KW_QED = "Qed"
KW_ADMITTED = "Admitted"
KW_ABORT = "Abort"

# Assertion and subcomponent keywords (alphabetically sorted).
KW_COROLLARY = "Corollary"
KW_DEFINITION = "Definition"
KW_EXAMPLE = "Example"
KW_FACT = "Fact"
KW_FORALL = "forall"
KW_LEMMA = "Lemma"
KW_PROPERTY = "Property"
KW_PROPOSITION = "Proposition"
KW_REMARK = "Remark"
KW_THEOREM = "Theorem"

# Tactic command keywords (alphabetically sorted).
KW_APPLY = "apply"
KW_ASSERT = "assert"
KW_CHECK = "Check"
KW_COMPUTE = "Compute"
KW_DESTRUCT = "destruct"
KW_EXACT = "exact"
KW_INDUCTION = "induction"
KW_INTRO = "intro"
KW_INTROS = "intros"
KW_REFLEXIVITY = "reflexivity"
KW_RESTART = "Restart"
KW_REWRITE = "rewrite"
KW_SPLIT = "split"
KW_SYMMETRY = "symmetry"

# REGULAR EXPRESSION CONSTANTS (need to be included in keyword groups, so defined first).
REGEXP_COMMENT = r"\(\*.+?\*\)"
REGEXP_BULLET = r"[\+\-\*]+\s*"

# KEYWORD GROUPS.
KW_GRP_TACTIC = [
    KW_APPLY,
    KW_ASSERT,
    KW_CHECK,
    KW_COMPUTE,
    KW_DESTRUCT,
    KW_EXACT,
    KW_INDUCTION,
    KW_INTRO,
    KW_INTROS,
    KW_REFLEXIVITY,
    KW_RESTART,
    KW_REWRITE,
    KW_SPLIT,
    KW_SYMMETRY,
    REGEXP_BULLET,
    REGEXP_COMMENT,
]

KW_GRP_DOCUMENT = [
    KW_PROOF,
    KW_CHECK,
    KW_COMPUTE
]

KW_GRP_ASSERTION = [
    KW_COROLLARY,
    KW_DEFINITION,
    KW_EXAMPLE,
    KW_FACT,
    KW_LEMMA,
    KW_PROPERTY,
    KW_PROPOSITION,
    KW_REMARK,
    KW_THEOREM,
]

# REGULAR EXPRESSION CONSTANTS.


def regx_non_capture_alt(grp):
    return f"(?:{'|'.join(grp)})"


REGEXP_TACTIC_END = r"[\.;]"
REGEXP_TACTIC = regx_non_capture_alt(KW_GRP_TACTIC)
REGEXP_TACTIC_LOOKAHEAD = f"(?={REGEXP_TACTIC}|$)"
REGEXP_DOCUMENT = regx_non_capture_alt(KW_GRP_DOCUMENT)
REGEXP_ASSERTION = regx_non_capture_alt(KW_GRP_ASSERTION)
REGEXP_IN_OCCURRENCE = r"(?:\sin\s\S+?)?"
REGEXP_AT_OCCURRENCE = r"(?:\sat(?:\s\d)+?)?"
REGEXP_AS_INTROPATTERN = r"(?:\s?as\s?\[[^\.]+?\])?"
