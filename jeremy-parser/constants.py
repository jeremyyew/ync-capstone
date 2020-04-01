import re

# LABEL CONSTANTS.
# Toplevel labels.
LABEL_ASSERTION = "ASSERTION"
LABEL_DOCUMENT = "DOCUMENT"
LABEL_LTAC = "LTAC"
LABEL_PROOF = "PROOF"
LABEL_REQUIRE_IMPORT = "REQUIRE_IMPORT"

# Toplevel subcomponent labels.
LABEL_ASSERTION_IDENT = "ASSERTION_IDENT"
LABEL_ASSERTION_KEYWORD = "ASSERTION_KEYWORD"
LABEL_ASSERTION_TERM = "ASSERTION_TERM"
LABEL_FORALL = "FORALL"

# Tactic command labels (alphabetically sorted).
LABEL_APPLY = "APPLY"
LABEL_ASSERT = "ASSERT"
LABEL_BULLET = "BULLET"
LABEL_CHECK = "CHECK"
LABEL_COMMENT = "COMMENT"
LABEL_COMPUTE = "COMPUTE"
LABEL_DESTRUCT = "DESTRUCT"
LABEL_EXACT = "EXACT"
LABEL_FOLD = "FOLD"
LABEL_INDUCTION = "INDUCTION"
LABEL_INTRO = "INTRO"
LABEL_INTROS = "INTROS"
LABEL_REFLEXIVITY = "REFLEXIVITY"
LABEL_RESTART = "RESTART"
LABEL_REWRITE = "REWRITE"
LABEL_SPLIT = "SPLIT"
LABEL_SYMMETRY = "SYMMETRY"
LABEL_UNFOLD = "UNFOLD"

# Tactic subcomponent labels.
LABEL_BINDER = "BINDER"
LABEL_REWRITE_ARROW = "REWRITE_ARROW"
LABEL_TERM = "TERM"
LABEL_TYPE = "TYPE"

# KEYWORD CONSTANTS.
# Toplevel keywords.
KW_ABORT = "Abort"
KW_ADMITTED = "Admitted"
KW_LTAC = "Ltac"
KW_PROOF = "Proof"
KW_QED = "Qed"
KW_REQUIRE_IMPORT = "Require Import"

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
KW_FOLD = "fold"
KW_INDUCTION = "induction"
KW_INTRO = "intro"
KW_INTROS = "intros"
KW_REFLEXIVITY = "reflexivity"
KW_RESTART = "Restart"
KW_REWRITE = "rewrite"
KW_SPLIT = "split"
KW_SYMMETRY = "symmetry"
KW_UNFOLD = "unfold"

# REGULAR EXPRESSION CONSTANTS (need to be included in keyword groups, so defined first).
REGEXP_COMMENT = r"\s*\(\*.+?\*\)\s*"
REGEXP_BULLET = r"[\+\-\*]+\s*"

# KEYWORD GROUPS.
KW_GRP_TACTIC = [
    KW_APPLY,
    KW_ASSERT,
    KW_CHECK,
    KW_COMPUTE,
    KW_DESTRUCT,
    KW_EXACT,
    KW_FOLD,
    KW_INDUCTION,
    KW_INTRO,
    KW_INTROS,
    KW_REFLEXIVITY,
    KW_RESTART,
    KW_REWRITE,
    KW_SPLIT,
    KW_SYMMETRY,
    KW_UNFOLD,
    REGEXP_BULLET,
    REGEXP_COMMENT,
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

KW_GRP_DOCUMENT = [
    KW_CHECK,
    KW_COMPUTE,
    KW_LTAC,
    KW_PROOF,
    KW_REQUIRE_IMPORT,
    REGEXP_COMMENT,
] + KW_GRP_ASSERTION

# REGULAR EXPRESSION CONSTANTS.


def regx_non_capture_alt(grp):
    return f"(?:{'|'.join(grp)})"


REGEXP_ASSERTION = regx_non_capture_alt(KW_GRP_ASSERTION)
REGEXP_DOCUMENT = regx_non_capture_alt(KW_GRP_DOCUMENT)
REGEXP_TACTIC_END = r"[\.;]"
REGEXP_TACTIC = regx_non_capture_alt(KW_GRP_TACTIC)
REGEXP_TACTIC_LOOKAHEAD = f"(?={REGEXP_TACTIC}|$)"
REGEXP_OR_AND_INTROPATTERN = r"(?:\[[^\.]+?\]|\S+?)"
REGEXP_IN_OCCURRENCE = r"(?:\sin\s\S+?)?"
REGEXP_AT_OCCURRENCE = r"(?:\sat(?:\s\d)+?)?"
REGEXP_AS_INTROPATTERN = fr"(?:\s?as\s?{REGEXP_OR_AND_INTROPATTERN})?"
REGEXP_USING_TERM = fr"(?:\susing\s\S+?)?"

REGEXP_DOC_LOOKAHEAD = f"(?={REGEXP_TACTIC}|{REGEXP_DOCUMENT}|$)"
