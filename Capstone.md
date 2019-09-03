# Capstone

Jeremy Yew 

[TOC]

## Chapter 1

The goal of this research project is to improve the learning experience of students enrolled in YSC3216: Functional Programming and Proving, a course in Yale-NUS College that introduces students to mechanized proofs. Students exercise equational reasoning by constructing logical proofs as executable programs, using the formal language provided by the Coq proof assistant (referred to as Coq). 

To this end, I implement a tool that enforces the use of a subset of Coq; it will enforce certain style rules, and allow only a specified subset of libraries to be used. 

The tool will parse text files containing Coq proofs submitted by students, and will output warning messages that inform the user of any any transgressions. Students will use to tool to check their code before submitting.  

Lastly, the tool will be designed as an extension of the GNU Emacs text editor, potentially integrating with the Proof General interface. It should be easy to install, configure, and use, so that it may be useful for other courses using Coq as well.   

### YSC3216: Functional Programming & Proving (FPP)

FPP is a Mathematical, Computational and Statistical Sciences (MCS) course taught by Professor Olivier Danvy. Through the course, students gain an appreciation for the deep relationship between computer programs and logical proofs - two domains which have hitherto been presented to them as completely isolated. 

Weekly assignments consist of progressive exercises involving reasoning and writing proofs about the properties of programs, and reflecting on the structure and properties of the proofs themselves. 

#### Higher-order logic (HOL)

To understand functional programming and proving, we must first describe their shared foundation: higher-order logic. 

- In propositional logic, we can state propositions such as "P and Q implies R". A proposition is simply a statement, and a statement can be true or false. Here, P, Q and R are also propositions that can be be modified or connected by logical operators such as "not", "and", "or",  "implies", and "if and only if"  to form new propositions. 
- In predicate logic, we extend propositional logic, and can state predicates, i.e. propositions that depend on (are predicated on) some input, such as "F(x)". Here, F is the predicate and x is a variable, and F could be a statement like "x is green". We may also quantify over variables as such: "for all x, F(x) holds", or "there exists some x for which F(x) holds".  
- In first-order predicate logic, we can only have predicates that take input variables representing objects that are not predicates, and we can only quantify over such variables. 
- In second-order predicate logic, we may have second-order predicates, which basically take first-order predicates as inputs. We may also quantify over these input predicates. For example: for all predicates P and values x, P(x) is true. 
  - Third-order predicate logic involves third-order predicates, which may take second-order predicates as inputs, and can also quantify over those predicates. 

>  note: better example.

- Higher order logic, then, allows for predication and quantification over n-th order (arbitrarily deeply nested) predicates. 
- HOL in computer science and mathematics allows us to express certain programs and proofs. 
- In computer science, HOL allows us to be more expressive in the context of functional programming, and allows us to write higher-order functions (see FP). 

> If a predicate only returns true or false, how do we explain functions (that may return various values) from logic?  

- In math, …? 

> How does HOL fit in Coq? Is it because  there are propositions that rely on HOL and proofs that only rely on FOL? 

- More: 
  - Lambda calculus?? 
  - Type theory?? 
- Other logics and the context of their use? 

> Is most of college-level math dependent on HOL, or any other types? 

#### Functional programming (FP)

FP is a programming paradigm that expresses programs as mathematical functions. That is, a program is a well-defined mapping of every possible input to exactly one output value. Functional programming is partly characterized by its 'declarative' style, in which the programmer directly expresses the desired output, derived from the input.

This puts it in contrast with another ubiquitous paradigm, imperative programming. Imperative programs may be understood simply as a series of explicit statements or instructions to change a program's state in order to obtain some implictly desired state. In FP, a function always returns the same output given the same inputs; in imperative programming, programs still have input and output,  but output likely depends on 'external' (quite unpredictable) context or state. 

However, it is important to understand that at the low level, declarative programming still compiles into imperative read-write commands that modify state; the translation of declarations into commands is safely abstracted by the compiler. 

- Section on higher-order functions: 

  - Higher-order logic is the foundation of FP. The predicates of HOL are the functions of FP; that is to say, functions don't just take input variables representing values, they can also take other functions as input. 
  - They can also return functions rather than values as outputs. 

  >  How does this relate to HOL? 

  - Furthermore, we quantify over all inputs (including functions) by relying on them being of a specific 'type'. 
  - Type theory?? 

Students taking FPP are expected to have completed Intro to Computer Science taught in Yale-NUS, which trains them in functional programming with the language OCaml (Coq has a language of programs that is very similar to OCaml, and is in fact written in OCaml). 

#### Proving

A proof may be defined as an argument about the truth of a proposition. A proposition is simply an assertion, and is sometimes called a theorem or lemma in the context of mathematics. 

Mathematical proofs use logical rules to demonstrate that what we are sure of implies the truth of something we weren't sure of. Therefore they may be understood as functions which take axioms, i.e. the propositions we know or assume to be true, as inputs; the outputs then are theorems that have been proven true, and which may also then be used as inputs to other proofs. 

Often the propositions in these proofs contain equations, which are statements asserting the equality of two expressions which contain variables (unknown values). In equational reasoning, we apply axioms to equations in order to transform them into something that is clearly true. 

### Coq proof assistant

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

### GNU Emacs Editor

- History: "For those curious about Emacs history: Emacs was originally implemented in 1976 on the [MIT](http://www.mit.edu/) AI Lab's Incompatible Timesharing System (ITS), as a collection of TECO macros. The name “Emacs” was originally chosen as an abbreviation of “Editor MACroS”. This version of Emacs, GNU Emacs, was originally written in 1984."
- shortcuts
- Extensible, customizable, self-documenting
  - <https://www.gnu.org/software/emacs/emacs-paper.html>
- Use in Intro CS, Algos and DS, FPP

### Proof General

- Generic, Adaptable 
- Three buffers: "The script buffer holds input, the commands to construct a proof. The goals buffer displays the current list of subgoals to be solved. The response buffer displays other output from the proof assistant. By default, only two of these three buffers are displayed. This means that the user normally only sees the output from the most recent interaction, rather than a screen full of output from the proof assistant. Proof General does not commandeer the proof assistant shell: the user still has complete access to it if necessary."
- Other features: simplified interaction, script management, multiple file scripting, a script editing mode, proof by pointing, proof-tree visualization, toolbar and menus, syntax highlighting, real symbols, functions menu, tags, and finally, adaptability."
- Coq without Proof General? CoqIDE, JSCoq. Coq in Jupyter?
  - Do the buffers look the same in CoqIDE? 
- <https://proofgeneral.github.io/>
- <https://proofgeneral.github.io/doc/master/userman/Introducing-Proof-General/#Quick-start-guide>

### References

- <https://coq.inria.fr/distrib/current/refman/credits.html>
- https://www.quora.com/What-is-the-difference-between-predicate-logic-first-order-logic-second-order-logic-and-higher-order-logic>
- <https://www.gnu.org/software/emacs/further-information.html>
- <https://en.wikipedia.org/wiki/Higher-order_function>
- <https://en.wikipedia.org/wiki/Higher-order_logic>

# Other ideas so far

- Proof tree visualization: <http://askra.de/software/prooftree/>
- Translating formal proofs back into coherent informal, plain English ones (and doing so in an extensible and customizable manner). For pedagogical and communication purposes. 
- Searching within a subset of rules (simple arithmetic) in order to achieve a multi-step transformation from the current equation to a desired equation. 
  - What do `trivial` or `auto` do under the hood? Do they only work on the current subgoal? Do they output the steps? 