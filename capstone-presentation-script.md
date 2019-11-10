# Learning Support for Mechanizing Proofs in Coq
Jeremy Yew 
Advised by Prof Danvy 

# Intro 
Good morning everyone, thanks __ for your presentation. Today I will present my Capstone, titled: (look at the screen) Learning Support for Mechanizing Proofs in Coq. My presentation will explain each part of the title. 

# Coq
- **Natural Language Proofs vs Mechanical Proofs**
  - *Display a NL proof.*
  - A natural language proof is written in a human language, for example, English. Even with the use of conventions and formal notation, natural language proofs are still unstructured and informal, which might sometimes introduce ambiguity.
  - When I say unstructured what I mean is there is no explicit system for organizing various parts of the proof.
  - What I mean by informal is that the use of formal notation is not consistent or strictly enforced. 
  - Also, since natural language proofs must be verified by other people, it is still susceptible to human error.
  - Furthermore, there are some aspects of verifying a proof that are fairly mechanical. For example, the process of modifiying an equation one step at a time in order to satisfy some equality. And as computer scientists and software developers we would like to automate whatever can be automated.
  - Mechanical proofs attempt to address the two issues of informality and fallible human reasoning. 
  - Just as there are programming languages that encode instructions for a computer to execute, there are also languages that encode logical arguments that can be mechanically verified by a computer.
  - By necessity, languages intended for a computer to interpret have to follow a clear structure and adhere to formal rules.  
  - A proof that has been formally encoded and mechanically verified therefore reduces ambiguity and human error. We could still make mistakes in the specification of a theorem or lemma, but if all the specifications are correct, and every proof step is correct, the conclusion must be true. 
  - We therefore have a tool that gives us a stronger confidence in a logical argument, whether it is a theorem about a mathematical property, or a proof about a program. 
  - In summary, a mechanical proof is not foolproof, but it gives us a tool to deal with abstraction and complexity by introducing structure, eliminating ambiguity, and automating reasoning. 
  - Coq is one such tool. 
- **Coq**
  - Coq is also known as the Coq Proof Assistant, or the Coq Interactive Theorem Prover. It is a program that verifies mechanical proofs, and one interesting feature as suggested by its name is that it can be used interactively, in the process of constructing a proof.  
  - Here is an example of a Coq proof. 
  - *Display a NL proof alongside a Coq Proof.*
  - So here is the interface that we are using to interact with Coq. The user will specify a theorem. Once that is accepted by Coq, a goal will be displayed in the buffer on the right. The user will type lines of code to apply logical rules, or tactics, to specific arguments in the current goal. Executing the tactic will apply the rule to the goal and transform it. The aim is to obtain sometime that is clearly true, for example an equation where the RHS is equal to the LHS. 
  - Coq is just one of many proof assistants, each with their own syntax and features, some of them encode other logical systems.
- **Functional Programming and Proving**
-  FPP is a MCS course taught by Professor Olivier Danvy. Through the course, students gain an appreciation for the deep relationship between computer programs and logical proofs.
-  FPP introduces students to mechanized proofs - proofs that can be verified automatically by a machine. Students exercise logical and equational reasoning by programming proofs in Coq. 
- Weekly assignments consist of progressive exercises involving:
    - writing proofs about mathematical and logical properties  
    - writing programs, and proofs about the properties of their programs

# Mechanizing Proofs
- **Learning to mechanize proofs: what could go wrong?**
  - The thing about programming languages is that there are usually many ways to write programs that are equivalent. For example, you can name variables differently, you can manipulate data in a different order, or you can use a different API.
  - This flexibility allows programmers to program things in a way that fits their own mental model, and also allows them to make the program more human readable. 
  - In the same way, there are many equivalent representations of a proof in Coq. It allows for variation in structure, it is flexible in the application of its rules, and it lets you take shortcuts. 
  - The flexibility that Coq provides can be counterproductive for a new learner. 
- Let me explain three issues that come up. 
- First, students might not adhere to structural conventions. 
  - For example, notice that a Coq proof usually begins with the definition of a lemma, then the "Proof" keyword, and ending with QED. This is useful because it delineates which lines of code are part of the actual proof. 
```
Lemma disjunction_is_commutative :
  forall A B : Prop,
    A \/ B -> B \/ A.
Proof.
  intros A B.
  intros [H_A | H_B].
  - right.
    exact H_A.

  - left.
    exact H_B.
Qed.
```
However, Coq doesn't enforce that these keywords are used, or even that they are used in a sensible way. For example, this proof would also be accepted: 
```
Lemma disjunction_is_commutative :
  forall A B : Prop,
    A \/ B -> B \/ A.
  intros A B.
  intros [H_A | H_B].
Proof.
  - right.
    exact H_A.

  - left.
    exact H_B.
Qed.
```
Or, even this: 
```
Proof.
Lemma disjunction_is_commutative :
  forall A B : Prop,
    A \/ B -> B \/ A.
  intros A B.
  intros [H_A | H_B].
  - right.
    exact H_A.

  - left.
    exact H_B. 
Qed.
```
  - Students actually do make these sorts of mistakes in the beginning, even if the intended use of each keyword is explained in class, simply because Coq raises no error, and it's a mistake because it reveals a lack of understanding of the structure of a proof, and reduces readability by breaking convention.  
  - The Professor has to manually spot these issues and specify them in the feedback. 
- **Abuse of tactics**
  - Second, students might abuse tactics they have not been taught.
- **Misuse of tactics**
- Third, students might misuse tactics they have been taught. 
- **Motivating Assumptions**
  - Why is it important to address these issues? 
  - Bad style reflects disorganized thoughts, and sometimes lack of understanding. 
  - Bad style make proofs harder to read and also harder to complete. 
  - Programming and proving at the beginner level should be generally prescriptive. 
    - Students beginning to learn how to program and to write proofs often develop certain bad habits (such as those described in the 'Problem' section). These habits, if left unchecked, will affect their future endeavors. 
    - For example, inappropriate indentation makes any code less readable, regardless of domain or language. 
    - Relying on implicit logic too often also makes written proofs harder to understand. 
   - Therefore, we should reinforce good habits at an early stage, in the same way that training in many sports or disciplines begin with prescriptive routine and repetition. 

# Learning Support
- The solution
  - How do we provide learning support for students facing these issues? 
  - The goal of my project is to write a program that will parse a Coq file and detect syntax issues I've described. It will output warnings about instances where a syntax rule has been violated.  
  - I will write the program as an extension of the Emacs editor, so that students can execute a command within Emacs to parse the current file. Thus, they can verify that their program meets the required syntax rules throughout the process of editing their proof.  
- **Current progress**
  - Research on types of parsers, and how to write a parser.
  - Learning how to write extensions and interact with Emacs. 
    - Run Coq shell and check for syntax errors. 
  - Explore various approaches. 
  - Custom syntax parser: Other language vs emacs-lisp
    - Pros: can use any language. 
    - Cons: might be slower/less interoperable due to system call. 
  - Custom syntax parser vs Parser generator
    - Identified parser generators intended to be run within Emacs, and written in emacs-lisp.
    - Pros: In theory, no need to write code. Just declare syntax rules. 
      - Easier to add new rules. 
      - Don't reinvent the wheel. 
      - Written in emacs-lisp. 
      - Easier for other emacs developers to build upon. 
    - Cons: 
      - Need to learn grammar notation. 
      - People who want to add new rules also need to learn the notation, but it should be simpler than. 
      - Documentation is not very well written. 
- Nice-to-have features
# Summary
In summary...

# Questions 
- Can Coq prove anything? 
- Is there a way to configure Coq so that we disable the features that provide flexibility?
- Does your project make any academic contributions? 
- Would your tool be used elsewhere? 