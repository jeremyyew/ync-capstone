# Learning Support for Writing Proofs in Coq
This repository contains all my MCS Capstone AY19/20 project source code and submission files. 

## Setup 
1. Make sure you have the file [jeremy-parser/jeremy-parser.el](jeremy-parser/jeremy-parser.el) - it is included in the binary download, but you can also copy or download it directly from here.
2. Navigate to your Emacs initialization file, which might be one of three options: `~/.emacs`, `~/.emacs.el`, or `~/.emacs.d/init.el`.
3. Insert this line anywhere in the init file: `load ("path/to/jeremy-parser.el")` . The file can be named and located as you like. 
4. Restart Emacs. 

# Usage
To run as a Python program...
To run from emacs...

# Testing
To run the test suite...

Each test run will generate a time-stamped log text file in
[jeremy-parser/logs](jeremy-parser/logs), with low-level information on the parser execution and diffs from expected results.

# Implementation
For the parser implementation, please see [jeremy-parser/parser.py](jeremy-parser/parser.py), which uses the BNF-like definitions in [jeremy-parser/grammar.py](jeremy-parser/grammar.py). 


# To do: 
- [X] **Usability: Add arity of Nat, Bool, Peano modules.**
- [X] **Usability: Write setup instructions for Mac**.
- [ ] **Development: Accept remaining syntax.**
- [X] **Feature: Warn user of unpermitted tactics (currently ignores them).**
- [ ] **Usability: ‘Freeze’ Python files into binary for interoperable usage. Test on Windows machine.**
- [ ] Report: Shorten Context and Motivation.
- [ ] Report: Migrate to Latex.
- [ ] Feature: Warn user of missing unfold lemmas when appropriate, and verifies the form of existing unfold lemmas.
- [ ] **Report overview**
  - [X] Context
  - [X] Motivation
  - [ ] Solution
    - [X] Setup 
    - [X] Usage
    - [ ] Examples
    - [X] Possible errors
  - [ ] Design and implementation
    - [X] Parsing input to generate a syntax tree
      - [ ] Example syntax tree
    - [ ] BNF grammars  
    - [X] BNF-like grammar module
    - [ ] Feature 1
    - [X] Feature 2
    - [ ] Feature 3
    - [X] Extending the parser  
    - [X] Unit tests
    - [ ] Acceptance tests
  - [ ] Discussion
    - [X] Time and space complexity
      - [X] Regular expression matching in construct_node
      - [X] The recursive construct_node function
      - [X] Traversing the syntax tree in check_arity
      - [X] String slicing
      - [X] Overall complexity
    - [ ] Performance
    - [ ] Limitations of the grammar module 
    - [ ] Alternative approaches
      - [ ] Parsing techniques  
      - [X] Modifying Coqtop source code
      - [X] Using a parser generator
    - [ ] Potential improvements
    - [ ] Reflections
  - [ ] Acknowledgements
  - [ ] References 
  - [ ] Appendix 
    - [ ] Supported syntax  