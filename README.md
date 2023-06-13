# Formalizations and Proofs about Wasm Semantics

This repository contains formalizations and proofs regarding the programming semantics of WebAssembly (Wasm) using the Agda language.

# Implementations

The implementations can be found in the `src` directory.
## Main Formalization

- `OperationalSemantics.agda`: Formalization of small-step and big-step operational semantics of Wasm.
- `DenotationalSemantics0.agda`: Denotational semantics of Wasm, which refines its type system. This is based on the paper "A Type System with Subtyping for WebAssembly's Stack Polymorphism" by McDermott, D., Morita, Y., Uustalu, T. (2022).
- `DenotationalSemantics.agda`: Denotational semantics with different assignments of meaning from the above formalization.

## Main Proofs

- `Equivalence.agda`: Proof of equivalence between the small-step and big-step semantics.
- `Adequacy0.agda` and `Adequacy.agda`: Proof of adequacy of the denotational semantics with respect to the operational semantics.

# Getting Started

To read through the formalization, you can use any text editor with interactive support for Agda. We recommend using Emacs.

# Prerequisites

This implementation requires the following:

- Agda version 2.6.22
- The Agda standard library version 1.7.1