# Learning Support for Writing Proofs in Coq
Jeremy Yew 
Advised by Prof Danvy 

# Intro 
Alright, let's begin. 
Learning Support for Writing Proofs in Coq. 

# Coq (1min)
- **First, What is Coq?**
  - Coq is a system for writing and verifying formal proofs. 
- **Coq is introduced within the context of Functional Programming and Proving, a Yale-NUS MCS course taught by Professor Danvy.** 
  - The target audience of my project is thus FPP students who would be new to Coq - this includes not only Yale-NUS students but also PHD and post-doctoral students from the School of Computing. 
- **The learning philosophy of FPP is that programming and proving is similar to training in any skilled discipline such as martial arts, cooking, or dance.**
  - Beginner training should build muscle memory for basic skills and habits. 
  - For example, if you are training to be a chef, but you don't develop proper knife skills early on, this will hurt you for the rest of your career. 
- **Therefore, in the first half of the course, students complete rigorous, progressive exercises in order to practice specific proof techniques and programming habits.** 
  - In the second half of the course, students can then rely on this muscle memory to write proofs with greater creativity and efficiency.  
  - By the end of the course, students will have independently written more proofs than they have ever written in their lives, 
  - and all of these proofs would have been verified by Coq. 
  
# Writing Proofs (2min)
- **Next. Writing proofs. What could go wrong?**
  - With programming languages, there are usually many ways to write the same program.
  - In the same way, there are many equivalent representations of a Coq proof, because Coq is flexible and allows you to take shortcuts. 
  - However, for new learners, this flexibility can be counterproductive.
  - In the context of FPP, several issues arise. Let me explain two of them.
- **First, students may ab*use* tactics that have *not* been introduced in the course**. 
  - So a tactic is a deduction rule that we apply to the current formula.
  - When students get stuck on a proof, they might Google for related solutions or search the Coq documentation for anything that will 'solve' the proof. 
  - They might end up using a magical tactic like 'trivial'. 
  - Under the hood, the "trivial" tactic uses some heuristics to automatically try various strategies to solve the current formula. 
  - Now, in the first half of the course the focus is for students to understand every single proof step they write, because if you can't explain what you're doing, you don't really understand it.
  - So using a tactic like "trivial" completelely goes against the objective of the exercise. 
  - Yet these tactics still appear in student submissions, because they might still have the bad programmer mindset of "if it works, its fine". 
  - So a lot of time in between resubmissions is wasted on superficial feedback. 
- **Second, even when students use tactics that *have* been introduced, they may *mis*use them by taking shortcuts.**
  - For instance, the rewrite tactic is used to apply a rule to the current formula. 
  - A rewrite rule a function that expects specific terms in the formula as arguments; and Coq will then apply the rule to those terms. 
  - However, Coq is flexible with the number of arguments you give it. 
  - In this example, you could give it 3, 2, 1 or zero of the arguments required, and Coq will simply pick the first terms in the formula that it can apply the rule to. 
  - However, students need to be aware of exactly which terms they have changed at every step. 
  - So again, taking advantage of this shortcut goes against the spirit of the exercise. 
  - And this isssue is not easy to check manually, especially with assignments that are hundreds of lines long.
  - So it would be nice to have a system that can anticipate these issues and help achieve the learning goals of the course.   

# Learning Support (2min)
- **So here is where my project comes in to provide learning support.**
  - The goal is to write a program that can enforce explicit tactic application within a subset of Coq, amongst other rules.
  - It will take as input the student's Coq files as well as a grammar specification provided by the Lecturer. 
  - It will output warnings about instances where a syntax rule has been violated.  
  - The program will be writen as an extension of the Emacs editor, so students can execute a command within Emacs to parse the current file.
  - The program will thus act as a set of safety rails for students to develop the right habits.
  - As a result, students will have earlier, automated intervention on syntactical issues in their assignments, 
  - And the Lecturer can spend more time on substantive rather than superficial feedback. 
 - **So, one of the implementation tradeoffs I'm considering right now is whether to write my own custom parser by hand or use a parser generator, which would be ideal.**  
- **In terms of my progress so far**, 
  - These are some the topics that I've had to do research on, which have been implied by my presentation so far.
  - The challenges ahead would be to implement the two rules, and then explore the other rules that I've discussed with Prof Danvy. 
- I will also be iterating on the tool based on usability feedback from both the Lecturer and FPP students, and the feedback will also be the measure of success for my project.

# Questions 
- What other rules? Enforcing consistency in indentation, structural conventions, variable naming.
- Is there a way to configure Coq so that we disable the features that provide flexibility?
- Does your project make any academic contributions? 
- Would your tool be used elsewhere? 

# Notes 