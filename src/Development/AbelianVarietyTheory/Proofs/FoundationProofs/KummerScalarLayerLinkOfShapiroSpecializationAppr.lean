module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KZ

theorem spLink_of_spec_approx (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (e : ℕ)
    (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (y : G ℚ Ω → Fin 2 → Qbar l)
    (h : ∀ r, ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 →
      ‖y s 1 - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s 1‖ ≤
        ‖((l : ℕ) : Qbar l) ^ r‖) :
    SpLink A e χ (fun r s x => Y r s x 1) y := by
  intro n
  refine ⟨n, fun r hr s hs hc => ?_⟩
  have h1 := h r s hs hc
  have heq : spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s 1 =
      sp (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Y r s x 1) s := by
    simp only [spec, sp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq] at h1
  unfold Cg
  refine h1.trans ?_
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _) hr

end GlobalTheory.KZ
