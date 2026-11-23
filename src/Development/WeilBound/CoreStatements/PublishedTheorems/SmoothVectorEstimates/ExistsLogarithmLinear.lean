module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace ExistsLogarithmLinear

theorem exists_log_lin {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (χ : AddChar V ℂ) (hχ : Continuous χ)
    (h0 : ∀ z, χ z ≠ 0) : ∃ L : V →L[ℝ] ℂ, ∀ z, χ z = Complex.exp (L z) := by
  let f : C(V, {z : ℂ // z ≠ 0}) := ⟨fun z => ⟨χ z, h0 z⟩, hχ.subtype_mk _⟩
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (Subtype.ext (by simp [f]))
  have hF' : ∀ z, Complex.exp (F z) = χ z := fun z => congrArg Subtype.val (congrFun hF z)
  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    have hc : Continuous fun y => F (x + y) - F y := by fun_prop
    have := Complex.isCoveringMap_exp.const_of_comp hc (fun y y' => Subtype.ext (by
      simp only [Complex.exp_sub, hF', AddChar.map_add_eq_mul]
      rw [mul_div_assoc, mul_div_assoc, div_self (h0 _), div_self (h0 _)])) y 0
    simp only [add_zero, hF0, sub_zero] at this
    rw [← this]; ring
  exact ⟨(AddMonoidHom.mk' F hadd).toRealLinearMap F.continuous, fun z => (hF' z).symm⟩

end ExistsLogarithmLinear

theorem exists_logarithm_linear : S8 := by
  intro ι _ χ hχ h1
  obtain ⟨L, hL⟩ := ExistsLogarithmLinear.exists_log_lin χ hχ (fun z h => by simpa [h] using h1 z)
  refine ⟨Complex.imCLM.comp L, fun z => ?_⟩
  have hre : (L z).re = 0 := by
    have := h1 z
    rw [hL z, Complex.norm_exp] at this
    exact Real.exp_eq_one_iff _ |>.1 this
  rw [hL z]
  congr 1
  apply Complex.ext <;> simp [hre]

end PositivityTheory.jumpWindows

end
