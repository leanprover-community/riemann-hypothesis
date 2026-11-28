module

public import Lib.General.Groups.BesselGroups
public import Lib.General.Measure.IntegralOperators

/-!
# The decay and the head weights of the sieve at the real places

The sieve over all places (`New.Filling.sieve`) uses sieve systems in the sense of
`TauCeti.SieveSystem`: forms `J i p q` on pairs of sequences ("heads"), each but the last the
integral of the next one over a common entry, with bounds `En`, `Λ`, `β`. At the real places the
decay `β` and the weights `Λ` are the following.

* `New.dampedPower`: the decay `r ^ k * min 1 r ^ 6` in the ratio `r`.
* `New.headWeight`: the weight of a head, a product over its partial products.

## Relation to the literature

See `New.Spanning.MainTerm.GlobalSieve` for related work.
-/

@[expose] public section

noncomputable section

open Finset

namespace New

/-- The gain at the ratio `r`: the function `r ^ k * min 1 r ^ 6`. -/
def dampedPower (k : ℕ) (r : ℝ) : ℝ := r ^ k * min 1 r ^ 6

/-- The weight of a head `p` (with entries in `ℂˣ`) of length `i` at a real place. It is zero unless
the partial products `δ = p 0 * ⋯ * p l`, `l < i`, have modulus at most `R`, and then it is the
product of the numbers `max 1 ‖δ‖⁻¹ ^ K`. -/
def headWeight (R : ℝ) (K i : ℕ) (p : ℕ → ℂˣ) : ℝ :=
  ∏ l ∈ range i,
    let δ : ℂ := ∏ a ∈ range (l + 1), (p a : ℂ)
    if ‖δ‖ ≤ R then max 1 ‖δ‖⁻¹ ^ K else 0

lemma headWeight_nonneg (R : ℝ) (K i : ℕ) (p : ℕ → ℂˣ) : 0 ≤ headWeight R K i p :=
  prod_nonneg fun _ _ ↦ ite_nonneg (by positivity) le_rfl

end New

end
