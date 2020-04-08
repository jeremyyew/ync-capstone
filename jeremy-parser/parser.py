import argparse
from constants import *
import re
from typing import List, Dict
import logging
import sys
import datetime
import os
import utils
import grammar
import pickle

# Change directory so we can write log files in the correct folder, instead of from where emacs calls the shell command.
os.chdir(os.path.dirname(os.path.abspath(__file__)))

# Set logging config.
logging.basicConfig(
    filename=f'logs/log_{datetime.datetime.now().strftime("%H-%M-%S_%d-%m")}.txt', level=logging.DEBUG)
logger = logging.getLogger()


class Node:
    def __init__(self, label, val=None, children=None):
        # We label every node by its 'type', for evaluation purposes.
        self.label = label
        # The node's actual value (e.g. the identifier of a term) is not needed for evaluation, but is used for logging and displaying warning messages.
        self.val = val
        # Each node has a list of children, or subcomponents.
        self.children = children or []

# Custom exceptions.


class UnmatchedTactic(Exception):
    def __init__(self, remaining):
        self.remaining = remaining
        self.tactic = None
        match = re.match(fr"(.+?){REGEXP_TACTIC_END}{REGEXP_TACTIC_LOOKAHEAD}",
                         self.remaining)
        if match:
            self.tactic = match.group(1)
        # self.parent = parent


class UnmatchedToken(Exception):
    def __init__(self, remaining):
        self.remaining = remaining


def preprocess(s: str) -> str:
    # Remove tab, FF, CR, LF.
    s = s.strip()
    s = re.sub(r"\t|\f|\r|\n", "", s)
    s = re.sub(r"\s{2,}", " ", s)
    s = re.sub(r"\.\s+", ".", s)
    return s


def get_next_subterm(s: str) -> str:
    k = 0
    term = ""
    remaining = ""
    for i, c in enumerate(s):
        if c in [" "] and k == 0:
            return term, s[i+1:]
        if term == "S" and c == "(":
            return term, s[i:]
        elif c == '(':
            k += 1
        elif c == ')':
            k -= 1
        term += c
    if k != 0:
        logger.info("Invalid parentheses.")
        raise Exception("Invalid parentheses.")
    return term, remaining


def construct_term(term: str) -> Node:
    def construct_subterms(s: str, acc: list) -> List[Node]:
        if s == "":
            return acc
        subterm, remaining = get_next_subterm(s)
        child = construct_term(subterm)
        logger.info(
            f"Constructing other children of {s} with \"{remaining}\"...")
        return construct_subterms(remaining, acc + [child])
    logger.info(f"Constructing node TERM:{term}...")
    if term and term[0] == "(" and term[-1] == ")":
        term = term[1:-1]
    node = Node(LABEL_TERM, term)
    if re.fullmatch(r"[^\s]+", term):
        logger.info("Arrived at terminal.")
        return node
    node.children = construct_subterms(term, [])
    return node


def construct_node(s: str, rule: str) -> Node:
    def construct_children(s: str, parent: str, acc: list) -> List[Node]:
        if not s:
            return None, acc, ""
        _, expected = grammar.GRAMMAR[parent]
        if expected == []:
            return s, acc, ""
        logger.info(
            f"\n\nWith node {parent}, at:\n\"{s if len(s) < 100 else s[:100]}\"...")
        logger.info(
            "Attemping matches, expecting: [" + ", ".join(expected) + "]")
        exception = None
        for item in expected:
            pattern, _ = grammar.GRAMMAR[item]
            match = re.match(pattern, s)
            if not match:
                continue
            logger.info(
                f"Matched: {item} on \"{match.group(0)}\" with pattern: \n{pattern}\n")
            if item == LABEL_TERM:
                term_s, remaining_s = get_next_subterm(match.group(1))
                term = construct_term(term_s)
                return term_s, acc+[term], remaining_s
            try:
                child, remaining_s = construct_node_helper(
                    match.group(1), item)
                remaining_s = remaining_s + s[match.end():]
                remaining_log = remaining_s if len(
                    remaining_s) < 100 else remaining_s[:100]
                logger.info(
                    f"Constructing other children of {parent} on \"{remaining_log}\"...")
                return construct_children(remaining_s, parent, acc + [child])
            except (UnmatchedToken, UnmatchedTactic) as e:
                exception = e
                logger.info(
                    f"""Failed constructing node {item} or children. Backtracking from {rule}...""")
        if exception:
            raise exception
        if parent == LABEL_PROOF:
            raise UnmatchedTactic(s)
        raise UnmatchedToken(s)

    def construct_node_helper(s, rule):
        logger.info(f"Constructing node {rule}...")
        term_s, children, remaining_s = construct_children(s, rule, [])
        node = Node(rule, term_s or s)
        node.children = children
        return node, remaining_s

    node, _ = construct_node_helper(s, rule)
    # assert remaining is empty
    return node


def collect_arity(t: Node, arity_db : dict) -> dict:
    assert(t.label == LABEL_DOCUMENT)
    for child in t.children:
        if child.label != LABEL_ASSERTION:
            continue
        assertion = child
        ident = assertion.children[1]
        forall = assertion.children[2]
        if ident.label != LABEL_ASSERTION_IDENT or forall.label != LABEL_FORALL:
            continue
        binders = [c for c in forall.children if c.label == LABEL_BINDER]
        arity = len(binders)
        arity_db[ident.val] = arity
        logger.info(f"New term {ident.val} arity added in db: {arity_db}.")
    return arity_db


def check_arity(t: Node, arity_db: dict) -> dict:
    warnings = []
    warnings_output = []

    def check_subterms(subterms, parent_term):
        if not subterms:
            return
        first_term = subterms[0]
        if first_term.val in arity_db:
            arity_expected = arity_db[first_term.val]
            arity = len(subterms) - 1
            args = [term.val for term in subterms[1:]]
            arg_strings = ",".join([f"({arg})" for arg in args])
            if arity != arity_expected:
                warnings.append([parent_term.val, first_term.val,
                                 arity_expected, arity, args])
                warning_str = utils.warning_format(
                    parent_term.val, first_term.val,
                    arity_expected, arity, arg_strings)
                warnings_output.append(warning_str)
                logger.info(warning_str)

        if not first_term.children and first_term.val not in arity_db:
            # Primitive term, but can't tell if its unregistered or its a value (arity zero).
            logger.info(
                f"In {parent_term.val},direct term {first_term.val} not seen or registered.")

        assert((not first_term.children or len(subterms) == 1))

        check_subterms(first_term.children, parent_term)
        for subterm in subterms[1:]:
            if not subterm.children:
                # Primitive term. Check arity by itself.
                check_subterms([subterm], parent_term)
            else:
                check_subterms(subterm.children, parent_term)

    def traverse(t):
        logger.info(f"TRAVERSING {t.label}")
        if t.label in [LABEL_DOCUMENT, LABEL_PROOF]:
            for child in t.children:
                traverse(child)
        elif t.label in [LABEL_EXACT, LABEL_REWRITE, LABEL_APPLY]:
            # There should be exactly one child in a well-formed syntax tree.
            # It is either a parent term with child subterms to be verified, or a single term with zero arguments.
            if t.children[0].label == LABEL_REWRITE_ARROW:
                t.children = t.children[1:]
            check_subterms(t.children, t.children[0])
    arity_db = collect_arity(t, arity_db)
    traverse(t)
    return warnings, "\n".join(warnings_output)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", help="string input")
    args = parser.parse_args()
    if args.input:
        s = preprocess(args.input)
        with open(f'theory-lib/arity_db', 'rb') as f:
            arity_db = pickle.load(f)
            logger.info(f"Loaded arity_db with {len(arity_db)} entries.")
        try:
            t = construct_node(s, LABEL_DOCUMENT)
            logger.info("\n"+utils.pretty2str(t))
            _, warnings_output = check_arity(t, arity_db)
            print(warnings_output or "No warnings.")
        except UnmatchedToken as e:
            print(
                f"""Parser error: Could not parse the substring \"{e.remaining}\". This syntax may not be currently supported.""")
        except UnmatchedTactic as e:
            if e.tactic:
                print(
                    f"""Parser error: Could not parse the substring \"{e.remaining}\". \"{e.tactic}\" may be an unpermitted tactic, please only use tactics that have been introduced in the course.""")
            else:
                print(
                    f"""Parser error: Could not parse the substring\"{e.remaining}\".\n This syntax may not be currently supported.""")
