module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section




section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Filter Topology Matrix
namespace UpperTheory.V.Af.GlobalFixedVectors
variable {F : Type} [Field F] [NumberField F] {n M : ℕ}
end UpperTheory.V.Af.GlobalFixedVectors
open UpperTheory.V.Af UpperTheory.V.Af.GlobalFixedVectors in
theorem UpperTheory.V.Af.globFixed_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.GlobFixed := by
  classical
  intro _ F _ _ n M _ V _ _ ρ hρ h
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), HasFixed ρ (KAway n M S) → HasFixed ρ (KAway n M ∅) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      rintro ⟨v, hv0, hv⟩
      obtain ⟨σ, ⟨-, hσ⟩, hfix⟩ := h w
      let W : Submodule ℂ V := ⨅ k : KAway n M (insert w S), LinearMap.ker (ρ k - 1)
      have hWm : ∀ x, x ∈ W ↔ ∀ k ∈ KAway n M (insert w S), ρ k x = x := fun x => by
        simp [W, Submodule.mem_iInf, sub_eq_zero]
      obtain ⟨x, hxW, hx0, hx⟩ := sub_fixed σ.ρ σ.irred (ρ.comp (locGL F n w)) hσ W (fun g x hx => (hWm _).2 fun k hk => by
        have e : k * locGL F n w g = locGL F n w g * k := gl_ext fun u => by
          by_cases hu : u = w
          · subst hu; simp [(mem_KAway.1 hk).2 u (Finset.mem_insert_self _ _)]
          · simp [pLoc_locGL_of_ne hu]
        change ρ k (ρ (locGL F n w g) x) = ρ (locGL F n w g) x
        rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, (hWm x).1 hx k hk])
        (fun e => hv0 (by simpa [e] using (hWm v).2 hv)) _ hfix
      refine ih ⟨x, hx0, fun k hk => ?_⟩
      have h1 := loc_mem w (mem_KAway.1 hk).1
      have h2 : k * (locGL F n w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway n M (insert w S) := by
        refine mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩
        by_cases huw : u = w
        · subst huw; simp [pLoc_locGL]
        · simp [pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]
      have h3 : ρ (locGL F n w (GeneralLinearGroup.map (pLoc F w) k)) x = x := hx _ h1
      have h4 := (hWm x).1 hxW _ h2
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h4
  obtain ⟨w⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩⟩
  obtain ⟨σ, ⟨hV, -⟩, -⟩ := h w
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := M) ((hρ v).mem_nhds (by simp))
  obtain ⟨x, hx0, hx⟩ := key S ⟨v, hv, fun k hk => hS hk⟩
  exact ⟨x, hx0, fun k hk => hx k (mem_KAway.2 ⟨hk, by simp⟩)⟩
end
