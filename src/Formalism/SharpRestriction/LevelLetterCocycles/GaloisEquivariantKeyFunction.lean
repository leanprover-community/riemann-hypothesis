module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Formalism.ConjugateSelfDual.Statement
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsIdealDenominator
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace Formalism.MainNotions.ExistsIdealDenominator

open Formalism.IrreducibleCountingLemmas.TW

section Dense

variable (l : ℕ) [Fact l.Prime]

theorem norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  rw [Padic.norm_p, map_natCast, PadicComplex.coe_natCast] at h
  exact h

theorem exists_norm_btwn (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) : ∃ a : ℂ_[l], x < ‖a‖ ∧ ‖a‖ < y := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := lt_trans one_pos hl1
  have hy : 0 < y := lt_of_le_of_lt hx hxy
  set x' := max x (y / 2) with hx'
  have hx'0 : 0 < x' := lt_of_lt_of_le (half_pos hy) (le_max_right _ _)
  have hx'y : x' < y := max_lt hxy (half_lt_self hy)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ((Real.logb_lt_logb_iff hl1 hx'0 hy).2 hx'y)
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (l : ℂ_[l]) q.den_pos
  have hcn : ‖c‖ ^ q.den = (l : ℝ)⁻¹ := by rw [← norm_pow, hc, norm_l]
  have hc' : ‖c‖ = ((l : ℝ)⁻¹) ^ ((q.den : ℝ)⁻¹) := by
    rw [← hcn, Real.pow_rpow_inv_natCast (norm_nonneg _) q.den_ne_zero]
  have hval : ‖c ^ (-q.num)‖ = (l : ℝ) ^ (q : ℝ) := by
    rw [norm_zpow, ← Real.rpow_intCast, hc', ← Real.rpow_mul (inv_nonneg.2 hl0.le),
      Real.inv_rpow hl0.le, ← Real.rpow_neg hl0.le]
    congr 1
    have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den q).symm
    rw [hq]
    push_cast
    field_simp
  refine ⟨c ^ (-q.num), ?_, ?_⟩
  · rw [hval]
    refine lt_of_le_of_lt (le_max_left x (y / 2)) ?_
    rw [← hx']
    calc x' = (l : ℝ) ^ Real.logb l x' := (Real.rpow_logb hl0 hl1.ne' hx'0).symm
      _ < (l : ℝ) ^ (q : ℝ) := (Real.rpow_lt_rpow_left_iff hl1).2 hq1
  · rw [hval]
    calc (l : ℝ) ^ (q : ℝ) < (l : ℝ) ^ Real.logb l y := (Real.rpow_lt_rpow_left_iff hl1).2 hq2
      _ = y := Real.rpow_logb hl0 hl1.ne' hy

@[reducible] def denseC : DenselyNormedField ℂ_[l] where
  __ := (inferInstance : NormedField ℂ_[l])
  lt_norm_lt := exists_norm_btwn l

attribute [local instance] denseC

variable {l}

end Dense

namespace PtGeo

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [AddCommGroup Λ] {σ : Type} (X : PtGeo l Λ σ)

variable {X} {k : ℕ} {ρ : ℝ}

end PtGeo

variable {D : Formalism.BasicNotions.D7}

section U4

end U4

namespace SplitL

variable {R : Ranks} (H : Host R)

end SplitL

end Formalism.MainNotions.ExistsIdealDenominator

end
