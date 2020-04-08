
import pickle
import re
import sys
import proof_reader
from constants import *
import logging

# collect_arity_from_str allows us to collate the library theory methods. This is done once only, or when new modules are added. 

# The tree for Nat is huge and our function is not tail recursive.
sys.setrecursionlimit(10000)
# The library modules from which we register assertion arity signatures.
LIB_MODULES = ["Bool", "Nat", "Peano"]
# Processing is faster without the standard info logging.
proof_reader.logger.level = logging.ERROR


def collect_arity_from_str(s: str, arity_db: dict) -> dict:
    print(f"Creating document from string....")
    s = re.findall(r"[^\s]+?:\n[\s\S]+?(?=\n[^\s]+?:\n|$)", s)
    s = "".join([f"Lemma {a}." for a in s])
    s = proof_reader.preprocess(s)
    print(f"Constructing syntax tree...")
    t = proof_reader.construct_node(s, LABEL_DOCUMENT)
    utils.pretty_log(t, proof_reader.logger)
    print(f"Number of assertion nodes:{len(t.children)}.")
    print(f"Collecting arity...")
    arity_db = proof_reader.collect_arity(t, arity_db)
    print(
        f"Number of entries so far (assertions with forall):{len(arity_db)}.")
    return arity_db


# Run from ync-capstone/parser: `python3 -m parse_lib_arity`.
if __name__ == "__main__":
    arity_db = {}
    for filename in LIB_MODULES:
        print(f"Parsing {filename}...")
        with open(f"theory-lib/{filename}.txt", 'r') as f:
            # print(f.read())
            arity_db = collect_arity_from_str(f.read(), arity_db)
    with open(f'theory-lib/arity_db', 'wb') as f:
        pickle.dump(arity_db, f)
    with open(f'theory-lib/arity_db', 'rb') as f:
        arity_db = pickle.load(f)
        print(
            f"Total number of entries in arity_db (assertions with forall):{len(arity_db)}.")
sys.setrecursionlimit(1000)
