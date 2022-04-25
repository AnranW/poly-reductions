# Title for the docu #
## Introduction## 
This is a short explanation of the "IMP- to Turing Machine" project. It is meant for people who continue with the project and wish to quickly have an overview. 
It first gives a shallow introduction of the project, then goes into the part that I modified and explain why the modification was sensible and necessary. 
<!-- and help beginners to get a quicker start while attempting to further the project.  -->

## Preliminaries ## 
To encode IMP- to a Turing Machine(TM), we start by encoding it to IMP-- and prove its correctness and soundness. IMP- is a "shrunk" version of IMP that does not have boolean values, as can be seen in their respective *com* definitions: 
![Untitled](https://s3-us-west-2.amazonaws.com/secure.notion-static.com/f6cfae33-266c-4e3b-a1f3-5ac777019189/Untitled.png) 
![Untitled](https://s3-us-west-2.amazonaws.com/secure.notion-static.com/8e279b9f-b8f2-4037-b51c-a6c26f97a894/Untitled.png)

IMP-- is furthur shrunk by removing arithmetic expressions and restricting its datatype to *bit = Zero | One* in ./IMP_Minus_Minus_Com.thy. 

The reduction and the proof is in folder ./IMP-_To_IMP-- .

Next step is to reduce IMP-- to TM, by reducing IMP-- to SAS+ then to TM, with intermediate steps, of course.

SAS+ is a formalism often used in AI planning. Roughly speaking, an SAS+ *problem* is defined in Isabelle as a *record* with variables, operators, initial state, goal state, and variable ranges. 
An operator, if its *preconditions* are fulfilled in the current state, takes the system to the next state via its *effects*. 

A list of operators solves the SAS+ problem by taking the system fron the initial state to the goal state in the obvious way (sequantially). It is then called a *solution* to the problem. 

SAS++ is an "expanded" version of SAS+ by allowing uninitialised variables in the initial state. 
This is reflected by the definition for *is_serial_solution_for_problem_sas_plus_plus* in SAS_Plus_Plus.thy, where the initial state *I* is expanded by finding *∃I'. I ⊆⇩m I' ∧ dom I' = set ((Ψ)⇩𝒱⇩+* and consequently *I'* is treated as the usual initial state in SAS+. Here, if a variable is assigned in *I*, then it has the same value in *I'*; if it is not assigned in *I* then it is assigned in *I'* by some value. 
In the counterpart definition in SAS_Plus_Representation.thy, we have something in the line of *map_of (precondition_of op) ⊆⇩m I* where the initial state should define all variables, considering operator *op* could require any variable in its precondition. 

IMP-- is first reduced to SAS++, then SAS++ is reduced to SAS+, see the corresponding folders in this project. SAS+ is reduced(equivalent) to STRIPS, as shown in the afp project *Verified_SAT_Based_AI_Planning*. STRIPS in turn is to be reduced to/proven equivalent to TM. 

The step from IMP-- to SAS++