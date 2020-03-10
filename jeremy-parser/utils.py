from terminals import *


def pretty(node, _prefix="", _last=True):
    print(_prefix,  "|- " if _last else "|- ", node.label,
          ":", (f"\n   {_prefix}\"{node.val}\"" if node.val else ""), sep="")
    _prefix += "      "
    child_count = len(node.children)
    for i, child in enumerate(node.children):
        _last = i == (child_count - 1)
        pretty(child, _prefix, _last)
