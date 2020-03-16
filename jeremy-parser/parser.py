import argparse
from terminals import *
import re
from typing import List, Dict
import logging
import sys
import datetime
import os
import utils
import grammar

# Change directory so we can write log files in the correct folder, instead of from where emacs calls the shell command.
os.chdir(os.path.dirname(os.path.abspath(__file__)))
logging.basicConfig(
    filename=f'logs/log_{datetime.datetime.now().strftime("%H-%M-%S_%d-%m")}.txt', level=logging.DEBUG)
logger = logging.getLogger()

# TODO:
# X Define assertion and collect arity signatures.
# X Only collect for those that have been proven. (accept admitted).
# X Emacs command to call program.
# X Send back warning messages and display them.
# - Warnings:
#   rewrite: missing arrow
#   intro/intros: no args.
# - Accept:
# X require
# X  intros
#   rewrite
#   comment
#   abort
#   check
#   compute
#   induction
#   assert
#   destruct
# X reflexivity
# X exact (with or without parenthesis)
#   unfold
#   apply.
# - Line number would be nice.
# - Fold-unfold lemmas?


class Node:
    def __init__(self, label, val=None, children=None):
        self.label = label
        self.val = val
        self.children = children or []


def preprocess(s: str) -> str:
    # Remove tab, FF, CR, LF.
    s = s.strip()
    s = re.sub(r"\t|\f|\r|\n", "", s)
    s = re.sub(r"\.\s+", ".", s)
    return s


def get_next_subterm(s: str) -> str:
    k = 0
    term = ""
    remaining = ""
    for i, c in enumerate(s):
        if c == " " and k == 0:
            remaining = s[i+1:]
            break
        elif c == '(':
            k += 1
        elif c == ')':
            k -= 1
        term += c
    if k != 0:
        raise Exception("Invalid parentheses.")
    return term, remaining


def construct_term(term: str) -> Node:
    def construct_subterms(s: str) -> List[Node]:
        if s == "":
            return []
        subterm, remaining = get_next_subterm(s)
        child = construct_term(subterm)
        logger.info(
            f"Constructing other children of {s} with \"{remaining}\"...")
        children = [child] + construct_subterms(remaining)
        return children
    logger.info(f"Constructing node TERM:{term}...")
    if term and term[0] == "(" and term[-1] == ")":
        term = term[1:-1]
    node = Node(LABEL_TERM, term)
    if re.fullmatch(r"[^\s]+", term):
        logger.info("TERMINAL")
        return node
    node.children = construct_subterms(term)
    return node


def construct_node(s: str, rule) -> Node:
    def construct_children(s: str, expected) -> List[Node]:
        if not s:
            return []
        logger.info(f"\n\nWith node {rule}, at:\n\"{s}\"")
        logger.info(
            "Attemping matches, expecting: [" + ", ".join(expected) + "]")
        for item in expected:
            pattern, _ = grammar.GRAMMAR[item]
            match = re.match(pattern, s)
            if match:
                logger.info(f"Matched: {item} on \"{match.group(0)}\".")
                if item == LABEL_TERM:
                    child = construct_term(s)
                    return [child]
                try:
                    child = construct_node(match.group(1), item)
                    logger.info(
                        f"Constructing other children of {rule} on \"{s[match.end():]}\"...")
                    children = [child] + construct_children(
                        s[match.end():],
                        expected
                    )
                    return children
                except Exception as e:
                    if str(e) != "No match":
                        raise e
                    logger.info(
                        f"""Failed constructing node {item} or children.
                        Backtracking from {rule}...""")
        raise Exception("No match")
    logger.info(f"Constructing node {rule}...")
    _, expected = grammar.GRAMMAR[rule]
    node = Node(rule, s)
    if expected == []:
        return node
    children = construct_children(s, expected)
    node.children = children
    return node


def check_arity(t, arity_db):
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

    def collect_arity(assertion):
        ident = assertion.children[1]
        assert(ident.label == LABEL_ASSERTION_IDENT)
        forall = assertion.children[2]
        assert(forall.label == LABEL_FORALL)
        binders = [c for c in forall.children if c.label == LABEL_BINDER]
        arity = len(binders)
        arity_db[ident.val] = arity
        logger.info(f"New term {ident.val} arity added in db: {arity_db}.")

    def traverse(t):
        logger.info(f"TRAVERSING {t.label}")
        if t.label in [LABEL_DOCUMENT, LABEL_PROOF]:
            for child in t.children:
                traverse(child)
        elif t.label in [LABEL_EXACT]:
            # There should be exactly one child in a well-formed syntax tree.
            # It is either a parent term with child subterms to be verified, or a single term with zero arguments.
            check_subterms(t.children, t.children[0])
        elif t.label == LABEL_ASSERTION:
            collect_arity(t)
    traverse(t)
    return warnings, "\n".join(warnings_output)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", help="string input")
    args = parser.parse_args()
    if args.input:
        s = preprocess(args.input)
        try:
            t = construct_node(s, LABEL_DOCUMENT)
            # print(utils.pretty2str(t))
            _, warnings_output = check_arity(t, {})
            print(warnings_output or "No warnings.")
        except Exception as e:
            if str(e) == "No match":
                print("Parser error: Unrecognized tokens found.")
