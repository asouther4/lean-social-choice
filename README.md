# Social Choice Theory in Lean

Authors: Andrew Souther, Benjamin Davidson

## Introduction

This is a library of noteworthy proofs from Social Choice Theory formalized in Lean. 

### What is Lean? 

Lean is a proof assistant and a programming language. A [proof assistant](https://en.wikipedia.org/wiki/Proof_assistant) is a software tool that allows you to define mathematical objects and prove facts about these objects.  Lean's system checks that these proofs are correct down to the logical foundations. 

Lean's main library of pure mathematics, called [Mathlib](https://github.com/leanprover-community/mathlib), currently has over 50,000 theorems formally verified in this way. 

For more information on Lean and its community, see [here](https://leanprover-community.github.io/).


### What is Social Choice Theory? 

[Social Choice Theory](https://en.wikipedia.org/wiki/Social_choice_theory) is a theoretical framework at the intersection of philosophy, political science, and welfare economics. It studies methods for aggregating individual preferences into collective social welfare functions. 

## Library Structure

This library is in early development. Right now, we have two main files: 

- `basic` is a collection of simple definitions and theorems modelled off of Chapter 1 from [Collective Choice and Social Welfare](https://www.hup.harvard.edu/catalog.php?isbn=9780674919211) by Amartya Sen. Notably, we incldue Sen's Theorem on the necessary and sufficient condition for the existence of a choice function. 
- `arrows_theorem` contains a proof of [Arrow's Impossibility Theorem](https://en.wikipedia.org/wiki/Arrow%27s_impossibility_theorem). 