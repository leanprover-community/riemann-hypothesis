module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump

theorem isCompact_GL_of_invSet : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (T : Set (Lie E n)),
    IsCompact T → T ⊆ invSet E n →
      IsCompact {y : GL (Fin n) (Cinf E) | toL (y : Matrix (Fin n) (Fin n) (Cinf E)) ∈ T} := by
  intro E _ _ n T hT hsub
  haveI : CompactSpace T := isCompact_iff_compactSpace.1 hT
  have hu : Continuous fun p : T =>
      (IsUnit.unit (hsub p.2 : IsUnit (Matrix.of p.1)) : GL (Fin n) (Cinf E)) := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have hinv : ContDiffOn ℝ ∞ (GlobalTheory.ConstTermSmooth.invM (E := E) (a := n)) (invSet E n) := by
      have h1 : ContDiffOn ℝ ∞ (fun y : Lie E n => Ring.inverse (Matrix.of y).det) (invSet E n) := fun y hy => by
        obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hy
        have := contDiffAt_ringInverse ℝ (n := ∞) u
        rw [hu] at this
        exact (this.comp y contDiff_det.contDiffAt).contDiffWithinAt
      refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
      have h2 : ContDiff ℝ ∞ fun y : Lie E n => (Matrix.of y).adjugate i j := by
        simp only [Matrix.adjugate_apply]
        have h3 : ContDiff ℝ ∞ fun y : Lie E n => (Function.update y j (Pi.single i 1) : Lie E n) := by
          refine contDiff_pi.2 fun k => ?_
          by_cases h : k = j
          · subst h; simpa using contDiff_const
          · simpa [Function.update_of_ne h] using contDiff_apply ℝ _ k
        exact contDiff_det.comp h3
      exact h1.mul h2.contDiffOn
    have := hinv.continuousOn.comp_continuous
      (f := fun p : T => (p : Lie E n)) continuous_subtype_val fun p => hsub p.2
    refine Continuous.congr this fun p => ?_
    simp only [Matrix.coe_units_inv]
    rfl
  convert isCompact_range hu using 1
  ext y
  constructor
  · intro hy
    exact ⟨⟨toL (y : Matrix (Fin n) (Fin n) (Cinf E)), hy⟩, Units.ext rfl⟩
  · rintro ⟨p, rfl⟩
    exact p.2

end GlobalTheory.WhitBump
