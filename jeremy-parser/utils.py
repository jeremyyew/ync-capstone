def pretty_log(node, logger):
    def helper(node, _prefix="", _last=True):
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
            helper(child, _prefix, _last)
    helper(node)


def pretty2str(node):
    output = []

    def helper(node, _prefix="", _last=True):
        output.append("".join((_prefix,
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
            helper(child, _prefix, _last)
    helper(node)
    return "\n".join(output)


def warning_format(parent_tactic_label, parent_term, first_term, arity_expected, arity, arg_strings):
    return (
        f"WARNING: In tactic invocation {parent_tactic_label} on parent term ({parent_term}):\n Term \"{first_term}\" with arity {arity_expected} incorrectly applied to {arity} terms {arg_strings}.\n")

