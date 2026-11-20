# CLZ Certification landscape (2026-11-07)

## What "certified" can mean here

| Tier | Meaning | Who audits |
|---|---|---|
| T1 kernel | Lean 4, standard axioms only (propext/Classical.choice/Quot.sound), exact statement vs frozen Challenge surface, kernel replay | Lean kernel + (at riemann.fail) nanoda second kernel |
| T2 kernel+axiom | Lean 4 but with extra axioms asserting "a search program returned true" | kernel checks everything EXCEPT the numeric search run |
| T3 verifier | reproducible interval-arithmetic verifier (Python/Arb/C++), no kernel | you, on rerun |
| T4 claim | preprint or repo statement | nobody |

## The venues

**anthropics/zeta-23-lean + anthropics/formal-math/zeta23 (T1, the board's bar).**
Alpöge–Furman κ\* ≥ H = 2 − 1/cMT = 0.6725007036794116…, sorry-free, Mathlib-only.
Third-party audits exist: hydra-dynamix/zeta23-verification (21 Aug 2026: independent
build rc=0, 9,015 jobs on Lean v4.33.0-rc2 / Mathlib 51e6992e; PrintAxioms for all 17
headline theorems = 3 standard axioms, no sorryAx; statement-fidelity audit), plus
stevemoraco/qs PR#363 (kernel rebuild + axiom audit) and teal-sea/zeta-lab PR#12
(ceiling-data reproduction). The bar is real but it is **5 months stale as a record**.

**Riemann.fail / riemannzeta.fun (josusanmartin/riemann) (T1, ACTIVE).**
Automated arena: exact rational p/q + one Solution.lean; server-derived manifest;
exact statement comparison against pinned zeta-23 ChallengeDeps; permitted-axiom audit;
Lean AND nanoda kernel replay; immutable evidence commits; 3 uploads/day/account.
Record started at κ₀ = 0.6725007 (Anthropic). 50 submissions in repo history.
Per Knausgård: entries to **0.67348** — Lavery attempt-014 (0.6734812, 4 Oct) whose
proof he says obtains the bound for N₀ˢ first; dani-ani0 (0.6734824, 6 Oct, distinct-
on-line). Later entries incl. lixiang90 nine-point work (Oct 18–21) and
shi-anchor-variance-refinement-2026 — the site record **0.6735480 on 12 Oct 2026,
for DISTINCT-ON-LINE zeros** (Palomar-registered; does not transfer to κ\*).
Caveat: we read Knausgård's citation of the κ\*-at-0.67348 entry, not Lavery's proof.

**Zhaoyi-Tian/zeta-simple-zeros-lean (T1, unrefereed repo).** Two complete Lean
extensions of zeta23 for κ\* exactly: 673/1000 and **6734/10000** (frontier/,
corrected-window 7-point). Cited by Knausgård [51] as "complete formal proofs in Lean".

**Knausgård arXiv:2610.08965 (T2).** Lean proof-of-record for 0.6735382 and 0.8390046
with exactly 3 added axioms, one per finite inequality, each recording a search-program
return; kernel does not check the run. Full artifacts + C++ verifier published
(github.com/kristianmk/839, ancillary files on arXiv). An honest T2 — the strongest
bound, one trust-notch below the bar.

**ainta/zeta-simple-zeros (T3).** OUR NUMBER (0.673008527927, 7-point, 11 Aug 2026).
Python/Arb verifier, certificates recorded; the new step is NOT Lean — it leans on
Anthropic's Theorem D + test family as base. So even our own lane was never kernel-
certified; it was always a verifier-tier artifact.

**bigospeedrun/verifier route (the "official race"): CLOSED to outsiders.**
Issue #146 (4 Nov 2026), nmamano for BOS: "We plan this route ourselves, so it does
not open to outside submissions now. We will write the trusted statement from the
Challenge surface of anthropics/formal-math (zeta23), choose the pins, and rerun
Anthropic's own Lean proof first. That row will credit Anthropic." Board state there:
four Claimed rows, zero Lean Verified — they will replay zeta23 first (H = 0.6725007).
darkhipo/zeta-zeros-submission is a packaged draft waiting for that route to open.

## What certifying 0.6730085 would take

Formalizing ainta's 7-point finite step (6 gap variables, 21 pair distances,
Arb-exhaustive bound ≥ 19/5000) into Lean on top of zeta23 — exactly what
Zhaoyi-Tian already did at 6734/10000 > 0.6730085. The kernel-formalization
problem is solved *above* our number; ours adds nothing.
