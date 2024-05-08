# WebAPISpec: an Extensible, Machine Checked Model of Secure Browser Specifications

Browsers are implemented based on specifications written by disjoint groups of people.
Specifications for different components of the browser can end up being contradictory in a way that introduces security bugs because of the complexity of the software.
One way to reduce the likelihood of such specification bugs is to build a formal model of the browser that can be mechanically checked for clashes instead of relying on people to examine informal written descriptions for potential problems.

We propose a new browser specification model that uses refinement types to check that all provided API functions maintain our defined security invariant.
The model is a transition system in which the state is the browser internals and trace of events and the state transitions are the API functions.
If all API functions are safe, then any script which only interacts with the browser using those functions cannot violate the invariant.
The invariant is a conjunction of existing component security invariants from the literature, which we refer to as subinvariants.

This approach allows us to prove that scripts are safe without modeling the contents of the scripts themselves.
We are also able to model unbound traces without the exponential blow up of more traditional state space exploration approach.
In addition, we were able to prioritize extensibility by using Coq's module system and minimizing proof rewrites as new components are introduced.
As presented in our main findings, we were able to mostly automate proof search using the Hammer library for a given component's functions with regards to proofs of other components' subinvariants.
