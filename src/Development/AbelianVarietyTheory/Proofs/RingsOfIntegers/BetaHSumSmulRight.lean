import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CoeffSingleLawAdd

set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.FormalCalc

section

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  (k : Type) [CommRing k] [Algebra R k]

theorem dAct_mul (B : FB R d O) (a b : O) : dAct k B (a * b) = dAct k B a * dAct k B b := by
  ext i j
  simp only [dAct, FB.actK, coeff_map, Matrix.mul_apply]
  rw [B.A.mul_act]
  unfold comp1 ev
  rw [coeff_single_subst, Fintype.sum_prod_type, Fin.sum_univ_one, map_sum]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    rfl
  · rintro ⟨s, l⟩
    fin_cases s
    exact B.A.const b l

theorem betaH_eq_dotProduct (ξ η : (Fin d → k) × (Fin d → k)) :
    betaH k ξ η = η.2 ⬝ᵥ ξ.1 - ξ.2 ⬝ᵥ η.1 := by
  simp [betaH, dotProduct, Finset.sum_sub_distrib]




theorem betaH_sum_smul_right {ι : Type} (s : Finset ι) (c : ι → k)
    (ξ : (Fin d → k) × (Fin d → k)) (v : ι → (Fin d → k) × (Fin d → k)) :
    betaH k ξ (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i * betaH k ξ (v i) := by
  simp only [betaH_eq_dotProduct, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
    dotProduct_sum, sum_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib]

theorem betaH_sum_right {ι : Type} (s : Finset ι)
    (ξ : (Fin d → k) × (Fin d → k)) (v : ι → (Fin d → k) × (Fin d → k)) :
    betaH k ξ (∑ i ∈ s, v i) = ∑ i ∈ s, betaH k ξ (v i) := by
  simpa using betaH_sum_smul_right k s (fun _ => 1) ξ v


end


end GlobalTheory.FormalCalc
