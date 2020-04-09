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
- [ ] Migrate to latex.
- [ ] Declaration!
- [ ] References. 
- [ ] ‘Freeze’ Python files into binary. Installation instructions.
- [ ] Appendix.
- [ ] Testimonials.
- [ ] Feature: Warn user of missing unfold lemmas when appropriate, and verify the form of existing unfold lemmas.
- [ ] Performance!!

Notes to self:

"Capstone reports cannot exceed 40 pages excluding references (this means that everything else except the references must be contained in the 40 pages)."


## Feedback
- Delineate assumptions and contribution
- Explain unfold 
- Explain recursive structure
- Muscle memory
- Testimonials
