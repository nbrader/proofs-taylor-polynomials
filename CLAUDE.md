# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Coq formal verification project that proves Taylor polynomials must have their usual form when specified with certain properties. The project is organized as a learning exercise for proving theorems in Coq.

**Note**: This is a practice project. For production-quality Taylor theorem proofs, see Coquelicot: http://coquelicot.saclay.inria.fr/html/Coquelicot.Derive.html

## Repository Structure

The repository contains three main directories:

- **Coq/TaylorPolynomials/** - Core Taylor polynomial proofs and theorems
- **Coq/FreeMonoid/** - Free monoid library (git submodule from https://github.com/nbrader/proofs-free-monoid-lib)
- **Coq/CoqUtilLib/** - Utility library with helper functions (git submodule from https://github.com/nbrader/proofs-coq-util-lib)
- **Haskell/** - Test files for validating mathematical assertions

## Development Environment

The project requires:
- Visual Studio Code (1.94.2)
- VsCoq extension (v2.1.2)
- Coq toolchain with `coq_makefile`

**Important workspace note**: Coq .v files can only find other Coq .v files when you've opened in VS Code the folder that directly contains that file, not a parent folder containing multiple folders of .v files.

## Build Commands

All build commands should be run from the `Coq/` directory.

### Standard build:
```bash
./build_coq.sh
```

This script performs:
1. `make clean` - Removes old build artifacts
2. `coq_makefile -f _CoqProject -o Makefile` - Generates Makefile from project configuration
3. `make` - Builds all .v files

### Line ending issues:
If the build script isn't readable, run:
```bash
dos2unix build_coq.sh
```

### Manual build:
If needed, you can run the individual steps:
```bash
cd Coq
make clean
coq_makefile -f _CoqProject -o Makefile
make
```

## Submodules

This repository uses git submodules for two dependency libraries (CoqUtilLib and FreeMonoid). When first cloning, you may need to run a "Submodule Update" (e.g., via TortoiseGit context menu or `git submodule update --init --recursive`).

## Key Architectural Components

### TaylorPolynomials Module

The main proofs are structured around proving that Taylor polynomials must have specific implementations given certain axioms:

- **Taylor_0_implem**: Proves degree 0 Taylor polynomial is constant `F a`
- **Taylor_1_implem**: Proves degree 1 Taylor polynomial is the linearization `(D F a)*(x-a) + F a`
- **Maclaurin_implem**: Proves Maclaurin series (Taylor at 0) has the summation form
- **Taylor_implem**: Main theorem proving general Taylor polynomial implementation
- **Taylor_a_equiv**: Proves equivalence between Taylor polynomial at `a` and translated Maclaurin series

Key supporting files in TaylorPolynomials/:
- **Differentiation.v** - Derivative properties and lemmas (nth_pow_deriv, D_additive_over_summation, D_chain_of_linear)
- **Summation.v** - Summation functions and properties
- **Combinatorics.v** - Factorial and combinatorial functions
- **IteratedDifferentiation.v** - Iterated derivative operations
- **Integration.v** - Integration properties
- **Lemmas.v** - General mathematical lemmas
- **Product.v** - Product operations
- **Examples.v** - Example applications

### Dependency Libraries

**CoqUtilLib/** provides:
- FunctionLemmas.v - General function theory
- Iteration.v - Iteration utilities
- ListFunctions.v - List manipulation
- OptionFunctions.v - Option type utilities

**FreeMonoid/** provides category theory and algebraic structures:
- Monoid, Semigroup, Magma, Group structures
- Free monoid construction
- Homomorphism definitions
- Category theory basics

## Testing Approach

Haskell files in `Haskell/` are used to test mathematical assertions before attempting formal proofs. For example:
- `Taylor_a_equiv tester 1.hs` - Tests divisibility properties related to factorials
- These use QuickCheck for property-based testing
- Run with stack: `stack --resolver lts-20.5 ghci --package QuickCheck`

## Proof Strategy

The proofs use a bottom-up approach:
1. Establish basic derivative properties (linearity, homogeneity, product rule, chain rule)
2. Prove properties of iterated derivatives
3. Prove special cases (degree 0, degree 1)
4. Build up to general Taylor polynomial form via integration properties
5. Use functional extensionality to prove equality of functions

## Common Patterns

- Heavy use of `functional_extensionality` to prove function equality
- `iter D n` represents the n-th derivative
- Proofs often proceed by cases on natural numbers
- Algebra is simplified using `ring` and `field` tactics
- Real number scope (`R_scope`) is used throughout

## Proof Sketches for Specific Lemmas

### summation_R_triangular (Summation.v)

**Statement** (LaTeX):
```latex
\sum_{i=0}^{n} \sum_{j=0}^{n-i} f(i,j) = \sum_{k=0}^{n} \sum_{i=0}^{k} f(i, k-i)
```

**Proof Strategy via Bijection**:

The LHS can be shown equal to the RHS by way of a bijection between pairs of points enumerated row-by-row and pairs of points enumerated diagonal-by-diagonal.

1. **Define the bijection**:
   - Row-by-row enumeration: (i, j) where 0 ≤ i ≤ n and 0 ≤ j ≤ n-i
   - Diagonal enumeration: (k, i) where 0 ≤ k ≤ n and 0 ≤ i ≤ k, with j = k-i
   - Bijection: (i, j) ↔ (k=i+j, i)

2. **Bijection lemma for finite sums**:
   There should exist a lemma stating that such a bijection can be used to convert a finite sum into one in a different order, and that this reordering can be undone by way of associativity and commutativity. This shows that the sum itself is preserved.

3. **Proof structure**:
   - Prove the index sets are in bijection via k = i + j
   - Use the finite sum reordering lemma with this bijection
   - Apply commutativity and associativity of addition to show both orderings yield the same sum

**Implementation notes**:
- May need to first prove or find a general lemma about reordering finite sums via bijection
- The monoid structure (commutativity + associativity) of (R, +, 0) is key
- Alternatively, could prove directly by induction, expanding both sides and showing they match

## Proof Development Strategy

**CRITICAL**: When working on complex proofs, use computational verification at each step:
1. **Write fresh Python scripts** to test each intermediate goal before attempting Coq proof
2. **Never trust existing Python scripts** - they may not test what you currently intend to prove
3. **Test each subgoal independently** with targeted computational verification
4. **Incrementally build proofs** only after Python verification confirms the goal is viable
5. **Create new verification scripts** for each proof attempt to ensure accuracy

## Interactive Proof Debugging

**IMPORTANT**: When working on complex Coq proofs and unsure of goal structure:
1. **Ask the user to show intermediate goals** - The user has GUI access to VSCode with VsCoq extension that shows goals at every tactic step
2. **Be specific about which step** - Ask to see the goal "after applying tactic X but before tactic Y"
3. **Don't guess goal structure** - If unsure what the goal looks like after `simpl`, `rewrite`, etc., ask rather than assume
4. **Verify rewrite targets match** - Many proof failures occur because rewrite patterns don't match the actual goal structure
5. **Use this for debugging failed tactics** - When tactics fail with "no subterm matching" errors, ask to see the actual goal

**Example**: "Could you show me what the goal looks like after `simpl fold_left` but before the `rewrite` step? I want to make sure I understand the exact structure."
