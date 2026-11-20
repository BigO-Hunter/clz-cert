# Lean-verified bounds for simple zeros of the Riemann zeta function

This repository develops two complementary seven-point extensions of
Anthropic's [`zeta-23-lean`](https://github.com/anthropics/zeta-23-lean).
Both are complete Lean proofs of lower bounds for the proportion of nontrivial
zeros of the Riemann zeta function that are simple and lie on the critical
line. Neither result is a proof of the Riemann hypothesis.

| Directory | Result | Role |
|---|---:|---|
| [`zeta23/`](zeta23/) | `67.2500703679...%` | Imported analytic-number-theory foundation |
| [`ZetaSimpleZero673/`](ZetaSimpleZero673/) | **`673 / 1000 = 67.3%`** | First complete seven-point Lean extension |
| [`frontier/`](frontier/) | **`6734 / 10000 = 67.34%`** | Corrected-window extension of the same program |

## Two stages of the contribution

### `ZetaSimpleZero673`: making the seven-point certificate formalizable

[`ZetaSimpleZero673.headline`](ZetaSimpleZero673/ZetaSimpleZero673/Headline.lean)
is the first completed result in this repository. It keeps the
Montgomery--Taylor window from Zeta23 and formalizes the retained-spectral-
defect strategy at seven consecutive zeros.

The difficult finite step has six gap variables and 21 pair distances. A
direct interval subdivision produces a certificate with hundreds of thousands
to millions of cases and is impractical to elaborate as a Lean proof term.
`ZetaSimpleZero673` identifies a sparse phase-affine structure instead:

- a nonnegative 15-edge sub-objective drawn from the 21 pair distances;
- twelve reusable one-dimensional kernel phases;
- exact rational LP and Farkas witnesses at every terminal case; and
- a certificate tree with 1,063 nodes and 532 leaves.

Python proposes the finite data, while Lean checks the analytic enclosures,
phase coverage, rational identities, block counting, spectral-defect
elimination, and final zeta deduction. The result is a complete dyadic and
cumulative theorem at `673 / 1000`, not merely a checked local inequality.

See [`ZetaSimpleZero673/README.md`](ZetaSimpleZero673/README.md) for its exact
calibration and proof chain.

### `Frontier`: coupling the window to the retained-defect certificate

[`Frontier.Assembly.Endgame.dyadic_target`](frontier/Frontier/Assembly/Endgame.lean)
is the second completed result. It retains the same seven-point research
program but jointly treats the analytic window, local pair energy, positioned
gap pressure, and the canonical spectral defect.

Its main additions are:

- a Zeta23 realization of a window with 16 exact rational Fourier
  corrections;
- an explicit window--energy--pressure--defect formal interface;
- a 132-point cap-one block assembly in which the local and trace sides use
  the same canonical Gram defect;
- a hybrid exact certificate combining affine LP/Farkas leaves with
  interval-Hessian/LDL basins and reflection reuse; and
- a complete dyadic and cumulative Lean theorem at `6734 / 10000`.

`Frontier` is not a replacement for the `673 / 1000` development. The first
project contributes the compact certificate architecture that made a
six-dimensional seven-point proof feasible; the second uses that experience
to formalize a more tightly coupled window and defect calculation. They are
kept as separate Lean libraries, and `frontier` does not import
`ZetaSimpleZero673`.

See [`frontier/README.md`](frontier/README.md) for the mathematical interface,
frozen constants, contribution boundaries, and certificate statistics.

## Shared mathematical spine

Both developments preserve a nonnegative spectral defect `D` that the
baseline rank--trace estimate can discard. In schematic form, the trace side
gives

\[
rN+D\le S,
\]

while a seven-point local certificate, translated through finite blocks,
gives

\[
GS\le mD+PN+o(N).
\]

Because the two inequalities refer to the same Gram defect, it can be
eliminated to obtain

\[
S\ge\frac{mr-P}{m-G}N-o(N).
\]

The two projects differ in how they construct the window-coupled local
certificate and make this common structure computationally tractable.

## Build and audit

Build the `673 / 1000` development with:

```bash
cd ZetaSimpleZero673
lake build ZetaSimpleZero673
lake env lean Audit.lean
```

The `6734 / 10000` certificate is split into resumable modules because some
exact rational checks are memory-intensive. Use its resource-aware builder:

```bash
cd frontier
python3 scripts/build_lean.py
lake env lean Frontier/Audit.lean
```

## Provenance

The analytic foundation comes from Anthropic's Zeta23 project. The retained
spectral defect and seven-consecutive-zero strategy originate in
[`ainta/zeta-simple-zeros`](https://github.com/ainta/zeta-simple-zeros).
Position-dependent and exact shifted pressure were developed in
[`sxuff/zeta-positioned-pressure`](https://github.com/sxuff/zeta-positioned-pressure)
and
[`AMTOPA/zeta-exact-pressure-673262`](https://github.com/AMTOPA/zeta-exact-pressure-673262).
The corrected-window data used by `frontier` were discovered in
[`AMTOPA/zeta-exact-pressure`](https://github.com/AMTOPA/zeta-exact-pressure).

Relative to that lineage, this repository contributes two successive pieces:
the compact exact-certificate method and first complete seven-point Lean
extension at `67.3%`, followed by the unified corrected-window formal assembly
at `67.34%`.

Apache-2.0; see [`LICENSE`](LICENSE).
