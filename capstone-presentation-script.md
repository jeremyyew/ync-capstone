# Learning Support for Writing Proofs in Coq
Jeremy Yew 
Advised by Prof Danvy 

# Intro 
Alright, let's begin. 
Learning Support for Writing Proofs in Coq. 

# Coq (1min)
- **First, What is Coq?**
  - The Coq proof assistant is a system for writing and verifying formal proofs. 
- **Coq is introduced within the context of Functional Programming and Proving, a Yale-NUS MCS course taught by Professor Danvy.** 
  - The target audience of my project is thus FPP students who would be new to Coq - this includes not only Yale-NUS students but also PHD and post-doctoral students from the school of computing. 
- **The teaching philosophy of FPP is that programming and proving is similar to training in any skilled discipline such as martial arts, cooking, or dance.**
  - Beginner training should be prescriptive, and it should build muscle memory for basic skills and habits. 
  - For example, if you are training to be a chef, but you don't develop proper knife skills early on, this will hurt you for the rest of your career. 
- **Therefore, in the first half of the course, students complete rigorous, progressive exercises in order to practice specific proof techniques and programming habits.** 
  - Only in the second half of the course, having developed the proper muscle memory, will students begin writing proofs with more creativity and efficiency.  
  - By the end of the course, students will have independently written more proofs than they have ever written in their lives, and all of these proofs would have been verified by Coq. 
  
# Writing Proofs (2min)
- **Next. Writing proofs. What could go wrong?**
  - With programming languages, there are usually many ways to write the same program.
  - In the same way, there are many equivalent representations of a proof in Coq. 
  - Coq is flexible and allows you to take shortcuts. 
  - However, this flexibility can be counterproductive for a new learner. 
  - In the context of FPP, there are several issues that arise. Let me explain two of them.
- **First, students may abuse tactics they have not learned before**. 
  - So a tactic is a deduction rule that decomposes the current conclusion into its required premises.
  - When students get stuck on a proof, they sometimes end up Googling for related solutions or exploring the documentation for anything that will push the proof through. 
  - For instance, they might end up using a magical shortcut like this. 
  - In this case, the "trivial" tactic uses some heuristics under the hood to automatically try various strategies to prove the current formula. 
  - In the first half of the course the focus is for students to understand every single proof step they write, because if you can't explain what you do, you don't really understand it.
  - So using a tactic like "trivial" goes completely against the objective of the exercise. 
  - Yet students still submit exercises with random tactics, even when they have been warned not to, because to them, "it just works". 
  - So time is wasted because the Prof has to give feedback and repeatedly explain why those tactics are not allowed in the context of the course, and students waste time on a solution they thought was acceptable and now they have to redo it. 
- **Second, even when students use tactics that they have been taught, they may misuse them by taking shortcuts.**
  - For instance, the rewrite tactic is used to apply a rule to the current formula. 
  - It is a function that expects specific terms in the formula as arguments; Coq will apply the rule to those terms. 
  - However, Coq is flexible with the number of arguments you give it. 
  - In this example, you could give it 3, 2, 1 or zero of the rewrite rule arguments, and Coq will simply pick the first terms in the formula that it can apply to rule to. 
  - However, another objective of the exercises in the first half of FPP is for students to realize that proof steps in a Coq proof are equivalent to proof steps in a mathematical proof done in detail by hand.
  - So again, this goes against the objective of the exercise. 
  - So it would be nice to have a system that can anticipate these issues, save time for both the students and the professor, and help achieve the learning goals of the course.   

# Learning Support (2min)
- **So here is where my project comes in to provide learning support.**
  - The goal of my project is to write a program that can enforce explicit tactic application within a subset of Coq. 
  - It will take as input student's Coq files as well as a grammar specification provided by the Prof. 
  - It will output warnings about instances where a syntax rule has been violated.  
  - I will write the program as an extension of the Emacs editor, so that students can execute a command within Emacs to parse the current file, and they can use the tool interactively. 
  - As a result, students will have earlier, automated intervention on syntactical issues in their assignments, and the Prof can spend more time on substantive rather than superficial feedback. 
  - Therefore, in the spirit of FPP's learning philosophy, this program will function as 'safety rails' for the first half of the course in order to help students build muscle memory.
  
- **Current progress**
  - Research on types of parsers, and how to write a parser.
  - Learning how to write extensions and interact with Emacs. 
    - Run Coq shell and check for syntax errors. 
  - Custom syntax parser vs Parser generator
    - A parser generator is a program that accepts a grammar specification as input, and automatically generates a parser that applies the grammar to your code. 
    - I have identified parser generators intended to be run within Emacs, and written in emacs-lisp.
    - Pros: In theory, no need to write code. Just declare syntax rules. 
      - Don't reinvent the wheel. 
      - Written in emacs-lisp. 
      - More extensible - easier to add new rules, since declarative grammar notation as opposed to hard-coded program branches. 
    - Cons: 
      - Need to learn grammar notation. 
      - Documentation is not very well written. 
- **In terms of my progress so far**, 
  - Here are the key topics that I've had to do research on, as implied by my previous points.
- The challenges ahead for me would be to decide on an implementation strategy.
- After implementing the two rules, I can explore other rules that I've discussed with Prof Danvy. 
- The overall success of the tool can be measured by feedback on the real-world usability and effectiveness from both the Professor and the students of FPP.

# Questions 
- Can Coq prove anything? 
- Is there a way to configure Coq so that we disable the features that provide flexibility?
- Does your project make any academic contributions? 
- Would your tool be used elsewhere? 

