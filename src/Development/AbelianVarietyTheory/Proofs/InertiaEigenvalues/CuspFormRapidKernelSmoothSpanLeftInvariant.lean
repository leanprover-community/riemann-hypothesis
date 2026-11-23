module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.JSW

theorem mspanR_left_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ F ∈ GlobalTheory.JSW.mspanR π,
    ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g := by
  intro E _ _ _ a π
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g}
      add_mem' := by
        intro F G hF hG γ g
        simp only [Pi.add_apply, hF γ g, hG γ g]
      zero_mem' := by intro γ g; rfl
      smul_mem' := by
        intro c F hF γ g
        simp only [Pi.smul_apply, hF γ g] }
  have hS : mspanR π ≤ S := by
    refine sInf_le ⟨?_, ?_, ?_⟩
    · intro φ hφ γ g
      exact (π.cusp φ hφ).1.left γ g
    · intro F hF h γ g
      show F (ratGL E a γ * g * h) = F (g * h)
      rw [mul_assoc]; exact hF γ (g * h)
    · intro F hF X _ ν _ k γ' _ γ g
      show (∫ x, k x * F (ratGL E a γ * g * infGL E a (γ' x)) ∂ν) = ∫ x, k x * F (g * infGL E a (γ' x)) ∂ν
      congr 1
      funext x
      rw [mul_assoc, hF γ (g * infGL E a (γ' x))]
  intro F hF
  exact hS hF

end GlobalTheory.JSW
