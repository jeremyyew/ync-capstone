# Capstone Presentation Script: *Editorial Support for the Coq Proof Assistant*
Jeremy Yew 
261019

# Critique of working title
- "Editorial" emphasizes a property about the efficient cause, i.e. the fact that the syntax checker program is integrated into a text editor, without being specific about the tool itself ('something that supports the editing process in some way'). 
- Efficient cause may not be essential anyway since the project wouldn't be very different if the syntax checker wasn't integrated with the editor. 
- Also anyone unfamiliar with proof assistants will not make the link between Coq Proof Assistant and 'editorial' - who knows how a proof assistant works, or what it produces? 
- Although, 'Editorial' is also nice since it highlights the fact that the support happens throughout the editing (proof-writing) process. 
- 'Support' is good because it conveys the secondary nature of the assistance. 
- But 'Support for the Coq Proof Assistant' places emphasis on the (specific) tool as opposed to the activity/learning process - most listeners might be unfamiliar with the variety of proof assistants/the concept of mechanical proofs, so the specificity is missing context. 
- Also, we are not really supporting Coq, but supporting Coq users.

# Possible new title
It is not easy to squeeze all aspects/causes of the project into the title, while keeping it succinct and interesting. That means the title will have missing information, and probably cause readers to ask certain questions, which is okay - we just want it to be the right questions. For example, it feels more natural for readers to ask, "How did you accomplish this?" than "in what context, and to what end are you doing this?", or worse, "What are you actually doing?" which might be asked of the current working title. 

Therefore, we want something that highlights the final cause and material cause. Probably a subtitle can help with highlighting the other aspects.

- *Training students to write well-formed Coq proofs* 
  - Mentioning students is good, since it is their learning process that is important, not the improved proof submissions. 
  - 'Training students' is good, emphasizes the final cause i.e. long term educational benefits, as opposed to 'Enforcing good habits in individual submissions'.
  - 'Students' also helps to hint at the context - 'students' implies 'students taking some course', or at least some specialization, as opposed to any Coq user. 
  - I'm not sure if including FPP is useful - yes it sets the exact context, but most people won't recognize the course, or know what it entails, and the inclusion of the non-abbreviated title might be to lengthy, so it just becomes something to unpack, without adding any information to the title. 
  - The same goes for the Coq proof assistant itself, but it is kind of important since it is not any proofs but formal proofs in Coq, and it does matter what kind of formal proof.
  - 'Well-formed' captures the syntactical properties we are trying to encourage, with just the right level of prescriptivity (as opposed to 'better proofs'). 
  - A little boring.
  - How about: *Training students to program well-formed Coq proofs*? For those unfamiliar with mechanical proofs, the juxtaposition of 'program' and 'proof' helps introduce the idea. 
  - Questions a reader might then ask:
    - What are Coq proofs, and why do they exist? How can one program a proof?
    - Why do we want to train students to write formal proofs at all, let alone well-formed ones? 
    - What makes a Coq proof well-formed? 
    - How do you accomplish this? 

Other, discarded ideas: 
- *Enforcing good form in proof-writing* (Too much assonance. The material cause here is proof-writing, but maybe it should be the students instead.)

# Coq Proof (Material) 
- Explain Coq proofs. 
- Explain FPP. 
- Explain the point of formalized proofs and how Coq assists the construction of formal proofs.
- Explain the overall structure of a Coq proof. May not have time to describe the elements of the Coq interface. Just what a Coq proof looks like. 

# Well-formed (Formal)
- Explain the two main problems with student's Coq proofs: using tactics they don't know, and misusing tactics they do know. Show examples of mis-formed proofs. 
- Perhaps mention other style issues (mis-ordering of 'Proof' statement).

# Training (Efficient)
- The syntax checker program, which identifies lines of code that do not meet certain syntax rules. 

# Students (Final)
- To train students to write proofs with greater mindfulness and understanding, ultimately equipping them to tackle logical problems with clarity and confidence. 
- This comes naturally at the end. The formal section already introduces part of the motivation (since it would explain why misformed proofs are not good), so this is just a conclusive re-emphasis of the importance of discipline and training. 
- Alternatively, it could come right after the material section, since we can align it with the learning goals (and teaching methods) of FPP. 