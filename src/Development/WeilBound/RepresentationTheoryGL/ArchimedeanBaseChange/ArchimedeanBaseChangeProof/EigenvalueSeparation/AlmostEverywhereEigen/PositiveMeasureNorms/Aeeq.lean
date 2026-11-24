module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

open MeasureTheory
open scoped Pointwise

theorem aeeq : AeEq := by
  intro X u u' hu hu' hi hi' hae
  have : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  have : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  set A : Set X.G := {x | u x ≠ u' x} with hA
  have hAo : IsOpen A := isOpen_ne_fun hu hu'
  have hAF : X.μ (A ∩ X.F) = 0 := by
    have h1 : X.ν A = 0 := ae_iff.1 hae
    rw [Ctx.ν, Measure.restrict_apply hAo.measurableSet] at h1
    exact h1
  have hinv : ∀ γ : X.Γ, γ • A = A := by
    intro γ
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show u (((γ⁻¹ : X.Γ) : X.G) * x) ≠ u' (((γ⁻¹ : X.Γ) : X.G) * x) ↔ u x ≠ u' x
    rw [hi _ (γ⁻¹).2, hi' _ (γ⁻¹).2]
  have hμA : X.μ A = 0 := X.fd.measure_zero_of_invariant A hinv hAF
  have hAe : A = ∅ := (hAo.measure_eq_zero_iff X.μ).1 hμA
  funext x
  by_contra h
  have hx : x ∈ A := h
  rw [hAe] at hx
  exact hx

end PositivityTheory.Rg.BcB.E2.P
