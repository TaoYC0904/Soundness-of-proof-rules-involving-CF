# Extended Proof Rules
Proof soundness of some extended proof rules

# Installation
0. The project requires Coq 8.15.2.
1. Run ```coq_makefile -f _CoqProject -o Makefile``` to generate a Makefile that will work on your machine.
2. Run ```make``` to compile the project.

# Table of Content
- Imp.v: Basic imperative language
- ImpCF.v: Extension of the imperative language with control flow support
- Embeddings.v: Definitions of three shallow embeddings (big-step based embedding, weakest precondition based embedding, and continuation based embedding)
- BigSProof.v: Proofs of extended rules in big-step based embedding
- SmallSProof.v: Proofs of extended rules in weakest precondition based embedding
- ContProof.v: Proofs of extended rules in continuation based embedding
