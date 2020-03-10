from terminals import *
from parser import logger


def pretty(node, _prefix="", _last=True):
    logger.info("".join((_prefix,
                         "|- " if _last else "|- ",
                         node.label,
                         ":",
                         (f"\n   {_prefix}\"{node.val}\""
                          if node.val else "")
                         )))
    _prefix += "      "
    child_count = len(node.children)
    for i, child in enumerate(node.children):
        _last = i == (child_count - 1)
        pretty(child, _prefix, _last)
