module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem sec_finite_flat (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W : Z.affineOpens) :
    Module.Finite Γ(Z, W) (GlobalTheory.HilbAff.Sec A B y W) ∧ Module.Flat Γ(Z, W) (GlobalTheory.HilbAff.Sec A B y W) := by
  obtain ⟨h1, h2, -⟩ := y.2.2
  haveI : IsFinite (subStr A B y) := h1
  haveI : Flat (subStr A B y) := h2
  constructor
  · exact IsFinite.finite_app (subStr A B y) W W.2
  · have hV : IsAffineOpen (subStr A B y ⁻¹ᵁ (W : Z.Opens)) := W.2.preimage (subStr A B y)
    have h := Scheme.Hom.flat_appLE (subStr A B y) W.2 hV le_rfl
    rw [← Scheme.Hom.app_eq_appLE] at h
    exact h

end GlobalTheory.HilbAff
