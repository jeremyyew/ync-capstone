# Capstone

Jeremy Yew 

[TOC]

## Chapter 1
The goal of this research project is to assist the learning experience of students enrolled in YSC3216: Functional Programming and Proving (FPP). FPP is a course in Yale-NUS College that introduces students to mechanized proofs. Students exercise equational reasoning by constructing logical proofs, using the formal language provided by the Coq proof assistant (referred to as Coq). 

To this end, I implement a tool to specify a subset of Coq, its libraries, and certain style rules, and to enforce their use. The tool parses text files containing Coq proofs submitted by students, and output messages about transgressions. The idea is for students to check that their code adheres to the specification before submitting. 

Lastly, the tool is designed as an extension of the GNU Emacs text editor, potentially integrated in the Proof General interface. It should be easy to install, configure, and use, so that it can be useful for other courses using Coq as well.   

### Context

#### YSC3216: Functional Programming & Proving (FPP)

FPP is a Mathematical, Computational and Statistical Sciences (MCS) course taught by Professor Olivier Danvy. Through the course, students gain an appreciation for the deep relationship between computer programs and logical proofs - two domains which have hitherto been presented to them separately and independently.

Weekly assignments consist of progressive exercises involving:
    - writing programs,
    - reasoning and writing proofs about the properties of programs,
    - reflecting on the structure and properties of both the programs and the proofs.

#### Functional programming (FP)

FP is a programming paradigm that models programs as mathematical functions. That is, a program denotes a well-defined mapping of every possible input to exactly one output value. Functional programming is partly characterized by its 'declarative' style, in which the programmer directly expresses the desired output, derived from the input.

This model contrasts with the other ubiquitous paradigm, imperative programming. 

> Section on Turing Machine and global state

Imperative programs can therefore be understood simply as a series of explicit statements or instructions to change a program's state in order to obtain some desired output. The output thus depends on external - and thus implicit - parameters, i.e. the global state, and this program is described as 'impure'.

In contrast, a 'pure' FP program (or function, or method, or language) only has explicit parameters, and 
it is obvious that it will always returns the same output given the same inputs. 

> Line about Turing completeness
However, at the low level, declarative programming still compiles into imperative read-write commands that modify state; the translation of declarations into commands is safely abstracted by the compiler. 

Students taking FPP are expected to have completed Intro to Computer Science taught in Yale-NUS, which trains them in functional programming with the language OCaml (Coq has a language of programs that is very similar to OCaml, and is in fact written in OCaml). 

#### Proving

In mathematics, a proposition is a statement that either holds or does not hold; a proposition is also sometimes called a theorem or lemma. Proofs can be defined as an argument about whether a proposition holds. 

Mathematical proofs use logical rules to demonstrate that what we are sure of implies the truth of something we weren't sure of. Therefore we can understand a proof as a functions which takes propositions we know or assume to hold (known as "axioms") as input; the output is a theorem that has been proven true. This theorem may then also be used as an input proposition to other proofs. 

Often, propositions contain equations, which are statements asserting the equality of two expressions which contain variables (unknown values). In equational reasoning, we apply axioms to equations in order to incrementally transform them into something that is clearly true. 


#### Coq proof assistant

- Why
  - shortcomings of informal proofs 
  - other proof assistants 
- What 
  - Proofs that can be encoded and machine-verified, in particular proofs about the properties of computer programs. Examples: satisfaction of specification, equivalence…what else? 
  - " the *logical language* in which we write our axiomatizations and specifications, the *proof assistant* which allows the development of verified mathematical proofs, and the *program extractor* which synthesizes computer programs obeying their formal specifications, written as logical assertions in the language."
- How: 
  - Declare: specifications, programs, propositions.  Write proofs step by step, and execute them. 
  - Interactive mode. Subgoals, tactics, etc.
- What is unique: Program synthesis. 
- Who: main contributors 

Certified OCaml programs may be extracted from Coq proofs. 

#### GNU Emacs Editor

- History: "For those curious about Emacs history: Emacs was originally implemented in 1976 on the [MIT](http://www.mit.edu/) AI Lab's Incompatible Timesharing System (ITS), as a collection of TECO macros. The name “Emacs” was originally chosen as an abbreviation of “Editor MACroS”. This version of Emacs, GNU Emacs, was originally written in 1984."
- shortcuts
- Extensible, customizable, self-documenting
  - <https://www.gnu.org/software/emacs/emacs-paper.html>
- Use in Intro CS, Algos and DS, FPP

#### Proof General

- Generic, Adaptable 
- Three buffers: "The script buffer holds input, the commands to construct a proof. The goals buffer displays the current list of subgoals to be solved. The response buffer displays other output from the proof assistant. By default, only two of these three buffers are displayed. This means that the user normally only sees the output from the most recent interaction, rather than a screen full of output from the proof assistant. Proof General does not commandeer the proof assistant shell: the user still has complete access to it if necessary."
- Other features: simplified interaction, script management, multiple file scripting, a script editing mode, proof by pointing, proof-tree visualization, toolbar and menus, syntax highlighting, real symbols, functions menu, tags, and finally, adaptability."
- Coq without Proof General? CoqIDE, JSCoq. Coq in Jupyter?
  - Do the buffers look the same in CoqIDE? 
- <https://proofgeneral.github.io/>
- <https://proofgeneral.github.io/doc/master/userman/Introducing-Proof-General/#Quick-start-guide>

#### References

- <https://coq.inria.fr/distrib/current/refman/credits.html>
- https://www.quora.com/What-is-the-difference-between-predicate-logic-first-order-logic-second-order-logic-and-higher-order-logic>
- <https://www.gnu.org/software/emacs/further-information.html>
- <https://en.wikipedia.org/wiki/Higher-order_function>
- <https://en.wikipedia.org/wiki/Higher-order_logic>

### Problem
There are two main problems in the current learning process of FPP. 

1. Coq proofs contain 'magic' tactics.
    - Students discover (via documentation or Googling) tactics that have not been introduced to class, and use them indiscriminately. Almost always, they do not understand what the tactic is doing under the hood and is satisfied as long as "it works". 
    - This results in a lack of understanding about the proof. 
2. Coq proofs contain undesirable code style. 
    - Students. 

These two problems correspond to a lack of 'guiding rails' in terms of concrete syntax (what tactics are allowed) and abstract syntax (how code should be styled).

Furthermore, they seem to persist across iterations of the module, regardless of verbal and written reminders and repeated feedback. Indeed, the idea is for the tool to cut down on the amount of 'superficial' feedback ('don't use this tactic, because...', 'this is bad style, please correct it in this way', etc.) that the Professor must give repeatedly to individual students, and instead automatically lead students towards solutions that only require substantive feedback (ideas to pursue, possible restructuring of the proof, etc). 

### Motivating assumptions: 

### Solution: parsing syntax specifications

### Implementation: specifying a grammar of grammars

