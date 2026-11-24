module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne

theorem scalar_action_holds : SPois → SInt → SSmooth → SSmul := by
  intro _ _ _ F _ _ _ ω c k φ a ha
  have e2 : ∀ g, (a • φ).1 g = a * φ.1 g := fun _ => rfl
  refine ⟨fun h => ?_, fun c₀ b h => ?_⟩
  · obtain ⟨⟨hl, hlev, hk, hz, hg⟩, hlevel, hcent, hwt, hlow⟩ := h
    refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, fun w => Submodule.smul_mem _ a (hlevel w),
      fun z g => ?_, fun v => ?_, fun v => ?_⟩
    · rw [e2, e2, hl]
    · have e : {x | UpperTheory.V.TR.finRep F 2 x (a • φ) = a • φ} = {x | UpperTheory.V.TR.finRep F 2 x φ = φ} := by
        ext x
        simp only [Set.mem_ofPred_eq, map_smul]
        exact smul_right_inj ha
      rw [e]
      exact hlev
    · refine Submodule.finiteDimensional_of_le
        (S₂ := Submodule.span ℂ (Set.range fun x => UpperTheory.V.TR.cptRep F 2 x φ)) (Submodule.span_le.2 ?_)
      rintro _ ⟨x, rfl⟩
      show UpperTheory.V.TR.cptRep F 2 x (a • φ) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨x, rfl⟩)
    · refine Submodule.finiteDimensional_of_le
        (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (UpperTheory.V.TR.Sm F 2) => z φ) '' UpperTheory.V.TR.Zalg F 2))
        (Submodule.span_le.2 ?_)
      rintro _ ⟨z, hz', rfl⟩
      show z (a • φ) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨z, hz', rfl⟩)
    · obtain ⟨C, N, hC⟩ := hg g
      refine ⟨‖a‖ * C, N, fun y => ?_⟩
      rw [e2, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg a)
    · rw [e2, e2, hcent]
      ring
    · simp only [map_smul]
      rw [← smul_sub, hwt v]
      exact smul_comm _ _ _
    · simp only [map_smul]
      rw [← smul_sub, hlow v, ← smul_add]
      exact smul_comm _ _ _
  · intro x y hy yf
    have e : ∀ z : Af F, coefAt (fun 𝔪 => a * b 𝔪) z = a * coefAt b z := by
      intro z
      unfold coefAt
      split_ifs <;> simp
    convert (h x y hy yf).mul_left a using 1
    · funext ξ
      rw [e, mul_assoc]
    · rw [e2]
      simp only
      ring

end UpperTheory.HilbertEisensteinWeightOne
