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
- [X] Development: Accept about 70% of syntax used in first half of the course.
- [X] Development: Added testing apparatus and detailed unit test cases for all existing syntax.
- [X] Feature: Generate warnings for incorrect arity in terms supplied to “rewrite” and “exact” tactics.
- [X] Usability: Provide Emacs command (via some elisp functions to be evaluated) that:
  - first sends the current buffer to Coqtop for evaluation (halts if there is a coq error), 
  - then sends the buffer text as input to the Python program
  - then prints the warnings returned by the program in the Emacs response window.
- [ ] **Usability: Add arity of Nat.**
- [ ] **Development: Accept remaining syntax (need more sample files).**
- [ ] **Feature: Warn user of missing unfold lemmas and validate existing ones.**
- [ ] **Usability: ‘Freeze’ Python files into binary for installation-free, interoperable usage. Test on Windows machine.**
- [ ] U**sability: Write setup instructions for Mac and Windows (e.g. how to include the Elisp ).**
- [ ] Feature: Warn user of missing arrow in “rewrite” statements.
- [ ] Feature: Warn user of inconsistent naming choices in “intro" and "intros".