# Erdős #195: one permutation of ℤ with finitely many monotone 4-term APs of each 2-adic depth

> **Status: PARTIAL result. This is NOT a solution of [Erdős Problem #195](https://www.erdosproblems.com/195), which is still open.** The repository proves, and formally verifies in Lean 4, two theorems about monotone 4-term arithmetic progressions in permutations of ℤ. The permutations constructed here **do** contain monotone 4-term progressions, so these theorems say nothing about the answer to #195.

## The results

A *permutation of ℤ* is a bijection $f:\mathbb N\to\mathbb Z$, read as the sequence $f(0),f(1),\dots$, as in formal-conjectures. A *monotone 4-term AP* is a choice of indices $i<j<k<l$ with $(f(i),f(j),f(k),f(l))=(a,a+d,a+2d,a+3d)$ for some $d\ne0$; a negative $d$ gives a decreasing progression.

**Theorem H (finitely many progressions of each 2-adic depth).** There is one explicit permutation $E$ of ℤ such that, for every $v\ge0$, only finitely many monotone 4-term APs of $E$ have $\nu_2(d)=v$.

```lean
theorem Erdos195Bands.main_result :
    ∃ f : ℕ ≃ ℤ, ∀ v : ℕ, Set.Finite {p : ℤ × ℤ | p.2 ≠ 0 ∧ padicValInt 2 p.2 = v ∧
      ∃ i j k l : ℕ, i < j ∧ j < k ∧ k < l ∧ f i = p.1 ∧ f j = p.1 + p.2 ∧
        f k = p.1 + 2 * p.2 ∧ f l = p.1 + 3 * p.2}
```

**Theorem G (every finite depth).** For every $t\ge1$ there is a permutation of ℤ with no monotone 4-term AP whose difference is not divisible by $2^t$. There is one permutation for each $t$, not one permutation for all $t$.

```lean
theorem Erdos195Bands.finite_depth :
    ∀ t : ℕ, 1 ≤ t → ∃ f : ℕ ≃ ℤ, ∀ i j k l : ℕ, i < j → j < k → k < l → ∀ a d : ℤ,
      ¬ ((2 : ℤ) ^ t ∣ d) → ¬ (f i = a ∧ f j = a + d ∧ f k = a + 2 * d ∧ f l = a + 3 * d)
```

For $t=1$ and $t=2$, Theorem G gives statements equivalent to those of the earlier repositories [erdos-195-odd-difference](https://github.com/Alex-lop/erdos-195-odd-difference) and [erdos-195-difference-not-div-4](https://github.com/Alex-lop/erdos-195-difference-not-div-4), which use different constructions. The permutation of Theorem H also has no monotone 4-term AP with $4\nmid d$: in the instance used here every progression has $4\mid d$ (`Erdos195Bands.E_main_four_dvd`). Erdős #195 asks for the largest $k$ such that every permutation of ℤ contains a monotone $k$-term AP. The answer is 3 or 4 (Davis–Entringer–Graham–Simmons; Geneson; Adenwalla).

**Credit.** The construction is J. Geneson's block construction from [arXiv:2608.12604](https://arxiv.org/abs/2608.12604) (August 2026), §5. Geneson uses a truncation constant $c>2+1/a$ and obtains a 4-permutable *subset* of ℤ. With $c=1$ (no truncation), the stages started one step earlier and $0$ listed first, the blocks cover all of ℤ, and the $m\nmid d$ branches of his Lemmas 5.1–5.5 give Theorem G. **Theorem G is an immediate corollary of Geneson's §5**, which he does not state. The new ingredient of Theorem H is a modulus $2^{t_s}$ that grows with the stage $s$. The proofs are written out afresh in [`docs/proof.md`](docs/proof.md), because Geneson's lemmas assume an integer $a\ge4$ and $2+1/a<c<a$.

## The construction

Fix the base $a=3$ and a sequence $t_1,t_2,\dots$ ($t_s=s+1$ for Theorem H, $t_s=t$ for Theorem G); put $m_s=2^{t_s}$.

* **2-adic order.** $x\prec_2y$ iff digit $\nu_2(y-x)$ of $x$ is $0$. The digits are two's-complement digits, so a negative number has its true residues (`Int.emod`), not those of $|x|$; with $|x|\bmod m$ the construction fails. $\rho_n(x)$ is the residue of $x$ mod $2^n$ with its $n$ binary digits reversed. Ordering residues by $\rho_n$ is ordering them by $\prec_2$.
* **Bands.** Put $L_0=0$ and $L_{k+1}=L_k+2m_{k+1}$. The top exponent of $x$ in stage $k$ is $T_k(x)=L_k+m_{k+1}-\rho_{t_{k+1}}(x)$ for $x<0$ and $L_k+m_{k+1}+1+\rho_{t_{k+1}}(x)$ for $x>0$. It lies in $(L_k,L_{k+1}]$. The stage of $x$ is the least $k$ with $|x|<3^{T_k(x)}$. Each band is finite. Its bottom depends on $x\bmod m_k$ and its top on $x\bmod m_{k+1}$, so when $m_{k+1}>m_k$ the band tops are *ragged*.
* **The permutation.** List $0$ first. Then, stage by stage, list the negative elements in increasing $\prec_2$ order and then the positive elements in decreasing $\prec_2$ order. For $t_s=s+1$ it begins

```
0, -64, -32, -48, -80, -16, -56, -24, -40, -72, -8, -60, -28, -44, -76, -12, -52, -20, -36, -68, ...
```

Stage 0 here has 2459 elements: the negatives of stage 0 come first, then its positives, then stage 1.

**Proof idea (Theorem H).**
* Along an AP with $d=2^ju$, $u$ odd, digit $j$ alternates (Lemma 1). So two consecutive steps of one sign can never both go in the $\prec_2$ direction that the listing prescribes for their sign.
* Separation lemmas between stages, using the base $a=3>1+\sqrt2$, show that every step must go in that direction, except a *seam step*. A seam step is a growing step from stage $s$ to stage $s+1$ inside one residue class mod $m_{s+1}$.
* Hence every monotone 4-term AP has a seam step, so $2^{t_{s+1}}\mid d$, and its terms are bounded in terms of $s$.
* With $t_s\to\infty$, a fixed $\nu_2(d)$ bounds $s$, which leaves finitely many progressions. With $t_s=t$ constant it gives Theorem G.

## What survives, and why

The permutations do contain monotone 4-term APs, and all of them pass through a seam. A seam is a magnitude cut inside a residue class: everything of the class below the cut is listed before everything above it, whichever way $\prec_2$ points. The outer two steps of the AP then come out in the right direction automatically. Every seam carries such progressions (Prop. 2 of `docs/proof.md`): $(0,y,2y,3y)$ for suitable $y<0$ near the cut. The Lean files check two of them:
* $0,-6,-12,-18$ in the Theorem G permutation with $t=1$;
* $0,-44,-88,-132$ in the Theorem H permutation, with $\nu_2(-44)=2$.

So Theorem H bounds the progressions of each depth but does not remove them. A full solution along these lines would need class restrictions that are not monotone in the stage; `docs/proof.md` §5 discusses this, labelled heuristic. The research note behind this repository also stated that progressions exist for *every* depth $j\ge t_1$. That is false for sequences with jumps, and `docs/proof.md` §4 gives the corrected statement.

## Lean formalization

| File | Contents |
| --- | --- |
| [`Challenge.lean`](Challenge.lean) | The two statements to audit (Mathlib-only, proofs `sorry`). |
| [`Solution.lean`](Solution.lean) | The same statements, proved. |
| [`Erdos195Bands/Digits.lean`](Erdos195Bands/Digits.lean) | Binary digits `bit`, bit-reversed residues `rho`, alternation and comparison lemmas. |
| [`Erdos195Bands/Basic.lean`](Erdos195Bands/Basic.lean) | Bands, stages, the permutation `E t`, separation lemmas, the case analysis (`core`), Theorems G and H, the two seam examples. |
| [`checks/fidelity.lean`](checks/fidelity.lean) | Audit file (not part of the formalization), described below. |

The construction and the seam lemma `Erdos195Bands.exists_seam` are proved for an arbitrary sequence `t : ℕ → ℕ` with base $3$. Theorem G uses constant `t`, and Theorem H uses `t s = s + 1`. Not formalized: a general real base $a\ge1+\sqrt2$; the precise seam items (i), (ii), (iv) of Theorem H and the explicit bound $\mathcal H(j)$ (Lean proves cruder bounds, which suffice for finiteness); and Prop. 2 beyond the two instances.

Checks run on this repository:

- Lean `v4.35.0`, Mathlib `v4.35.0` (`56a005855ea1`). `lake build` succeeds; the only warnings are the two `sorry`s in `Challenge.lean`.
- No `sorry`, `admit`, `native_decide`, `decide`, `implemented_by` or `axiom` in the Lean files outside `Challenge.lean` and the audit file `checks/fidelity.lean` (checked with `grep`).
- Both theorems depend only on `propext`, `Classical.choice` and `Quot.sound` (`#print axioms`).
- The statements in `Challenge.lean` and `Solution.lean` elaborate to byte-identical terms under `set_option pp.all true`.
- `scripts/check-lean-sources.py` and `scripts/validate-formalization.rb` from the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate) (commit `2891de4`) pass. The scripts are not vendored here; copy them from the template to rerun them.

The repository follows the Palomar layout, with `comparator.json` and `formalization.yaml`. It has **not** been submitted to the registry.

To build:

```sh
lake exe cache get   # download Mathlib build files
lake build
```

## Reproducing the fidelity audit

After `lake build`, run `lake env lean checks/fidelity.lean` from the repository root. The file:
* copies formal-conjectures' `List.IsAPOfLengthWith`, `List.IsAPOfLength` and `HasMonotoneAP` verbatim from commit [`5d8b04d3`](https://github.com/google-deepmind/formal-conjectures/blob/5d8b04d3d41b745cc3f2f3cdd5ed04b60c500983/FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean);
* defines `HasMonotoneAPNotDvd f k t` (`HasMonotoneAP` restricted to differences not divisible by `2 ^ t`);
* proves `fc_form : ∀ t, 1 ≤ t → ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAPNotDvd f 4 t` from `Erdos195Bands.finite_depth`, in term mode through the equivalence `index_iff`;
* restates `main_result` with the list form (`fc_form_main`);
* proves two non-vacuity facts. Some permutation has a monotone 4-term AP with $2^t\nmid d$ (`nonvacuous`). The two permutations used in the proofs both satisfy formal-conjectures' `HasMonotoneAP · 4` (`seam_ap_depth`, `seam_ap_main`).

Its `#print axioms` lines report only `propext`, `Classical.choice` and `Quot.sound`. Unlike the files covered by the `grep` check above, it uses `decide`, on four-element lists in its non-vacuity example.

## Related repositories

- [Alex-lop/erdos-195-odd-difference](https://github.com/Alex-lop/erdos-195-odd-difference): no monotone 4-term AP with odd difference (a key order).
- [Alex-lop/erdos-195-difference-not-div-4](https://github.com/Alex-lop/erdos-195-difference-not-div-4): no monotone 4-term AP with $4\nmid d$ (a reflection merge).

Both statements are special cases of Theorem G, and so of Geneson's §5 with $c=1$; their constructions are different.

## Use of AI

This work was produced by **Claude Fable 5.1 and Claude Opus 5.5 (Anthropic) in Claude Code, under the direction of Alex Lopez**.

- Theorem G was noticed by a Claude Opus 5.5 critic agent reading Geneson's §5 with its constants traced.
- Theorem H, the stage-dependent modulus, was found by a Claude Fable 5.1 solver agent.
- Each theorem was checked by three adversarial AI referees (proof, computation, scope), with independently written programs. Their fixes are incorporated in `docs/proof.md`.
- Both theorems are verified by the Lean kernel. The Lean proof was written by a Claude Opus 5.5 agent.
- The work has **not** been refereed by a human.

## License

Apache-2.0; see [LICENSE](LICENSE).
