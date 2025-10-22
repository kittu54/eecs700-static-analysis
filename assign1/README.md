# Assignment: Extending the Hoare Logic Prover with Arrays and Procedures

-----

## Overview

You will extend the existing **Hoare Logic automatic prover** developed in class to support two new language features:

1.  **Arrays** — add read and write operations using Z3's theory of maps.
2.  **Procedures (with recursion)** — add functions with contracts (requires/ensures) and recursive calls.

The baseline prover supports assignments, sequencing, conditionals, and while loops with invariants. Your extensions must integrate with the existing VCGen (weakest precondition generator) and Z3 backend.

To verify a procedure call using its contract, we use two key concepts:

* **Havoc:** This is the act of **forgetting** the value of a variable. We model the execution of the function by assuming that all variables listed in the procedure's $\mathbf{modifies}$ clause *could* have any arbitrary new value. This is typically implemented in a VCGen by substituting the variable with a fresh, unconstrained Z3 variable.
* **Frame Condition:** This is the logical guarantee that all variables $\mathbf{V}$ (the set of all program variables) that are **not** in the $\mathbf{modifies}$ set $\mathbf{M}$ *must* retain their pre-call value. The frame condition ensures that the procedure only affects the state within its specified "frame," allowing us to reason about the rest of the program state.

-----

## Learning Objectives

  * Understand Hoare-style rules for arrays and function calls.
  * Implement verification condition generation for new constructs.
  * Encode program semantics using Z3's theories for arrays and quantifiers.
  * Explore recursion via specification-based induction.

-----

## Arrays

### Syntax

```python
x = a[i]      # read
a[i] = e      # write
```

Extend the parser to produce AST forms such as:

```
['select', A, I]     # array read
['tastore', A, I, E]  # array write (or desugar to assign)
```

### Hoare Rules

$$
\text{WP}(a[i] := e, Q) = Q[\text{store}(a,i,e)/a]
$$

### Z3 Encoding

Use Z3's built-in array theory:

* Declare arrays as `Array(Int, Int)`.
* Encode reads and writes as `Select(a, i)` and `Store(a, i, e)`.
* Optional: add bounds checks (`0 <= i < len(a)`).

-----

## Procedures and Recursion

### Syntax

```python
def inc(x):
  requires(x >= 0)
  ensures(ret == x_old + 1)
  x = x + 1
  return x
```

AST form:

```
['proc', name, params, body, requires, ensures, modifies]
['call', fname, actuals, lhs]
['return', expr]
```

### Hoare Rules

**Procedure Definition.** To verify a function body:

$$\text{requires}\_f \\Rightarrow WP(\\text{body}', \\text{ensures}\_f)$$

where `body'` replaces `return e` with `ret := e`.

**Handling Old Variables:** When verifying the function body, the prover must capture the **initial value** of every variable $v$ referenced as $\text{old}(v)$ in the $\text{ensures}_f$ clause.

* For each $\text{old}(v)$ in $\text{ensures}_f$, introduce a fresh variable $v_{\text{old}}$ (e.g., $x_{\text{old}}$) into the pre-state.
* The $\text{requires}_f$ formula must be augmented with the assumption $v_{\text{old}} = v$ for all such variables.

**Call Rule.** At a call site $x = f(e_1, e_2)$ with `modifies` list $M$:

1. **Precondition Check (VC1):** Verify that the current pre-state $\text{Pre}$ implies the procedure's requirement, substituting formals with actuals:

$$\text{Pre} \Rightarrow \text{requires}_f[\text{actuals}/\text{formals}]$$

2. **Havoc (VCGen step):** Assume a new, arbitrary value for all program variables $v \in M$ (the **modifies** list). Variables *not* in $M$ are assumed to be unchanged.

3. **Postcondition Assumption (WP step):** Introduce a fresh formula $\text{Ensures}'$ defined by the postcondition and the **Frame Condition**:

$$\text{Ensures}' = \text{ensures}_f[\text{actuals}/\text{formals}][x/\text{ret}] \land \bigwedge_{v \notin M} (v = \text{old}(v))$$

Then, continue VC generation from $Q$ by assuming $\text{Ensures}'$. (The $\text{WP}$ is effectively $\text{Pre} \land \text{Ensures}' \Rightarrow Q$.)

The set of variables $\mathbf{V} \setminus \mathbf{M}$ being unchanged is the $\mathbf{Frame\ Condition}$.


**Recursion.** Recursive calls are handled by **assuming the procedure’s own specification** at call sites (no inlining). This corresponds to verification by induction on the spec.

-----

## Implementation Tasks

### Changes to `parser.py`

  * Add support for Python `FunctionDef` nodes: extract `requires`, `ensures`, and `modifies`.
  * Add `Subscript` nodes for array read/write.
  * Support calls as `['call', f, args, lhs]`.

### Changes to `prover.py`

  * Extend `expr_to_z3` with `select/store`.
  * Implement WP rules for array assignments.
  * Maintain a procedure environment mapping names to (spec, body).
  * Add WP rules for procedure definition, call, and recursion.
  * **Handle old variables and ret substitutions.** Specifically, implement the mechanism to introduce $\mathbf{v_{old}}$ variables for the initial state when verifying a procedure definition, and handle the substitution of $\text{old}(v)$ references in $\text{ensures}$ with these fresh variables.

-----

## Deliverables

1.  Updated `parser.py` and `prover.py` implementing arrays and procedures.
2.  At least **8 test programs**:
      * 3 array tests (read/write, store-select law, aliasing).
      * 3 procedure tests (return, modifies, frame).
      * 2 recursive tests (factorial, array sum).
3.  A **2-page design note** as a PDF summarizing Hoare rules, encodings, and one counterexample.

-----

## Sample Programs

### Array Store/Select

```python
# { i != j }

a[i] = v

# { a[j] == old(a)[j] }
```

### Procedure with Return

```python
def bump(x):
  requires(True)
  ensures(ret == x_old + 1)
  return x + 1

  y = bump(x)

# { y == x + 1 }
```

### Recursive Factorial

```python
def fact(n):
  ensures((n == 0 and ret == 1) or (n > 0 and ret > 0))
  requires(n >= 0)
  if n == 0:
    return 1
  else:
    t = fact(n - 1)
    return n * t
```

-----

## Grading Rubric (100 pts)

  * Arrays implementation — 30 pts
  * Procedures (non-recursive) — 25 pts
  * Recursion support — 20 pts
  * Tests — 15 pts
  * Design write-up — 10 pts
