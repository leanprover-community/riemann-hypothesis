module

public import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4

def LeafCoprod : Prop := Hyps → ∀ (q : ℕ) (n i : ℤ) (m : ℕ) (Z : Fin m → Scheme.{0}),
  (∀ j, Finite (Ht q (sch.obj (Z j)) n i)) → Finite (Ht q (sch.obj (∐ Z)) n i)

def LeafCompGeom : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p],
  ∃ (m : ℕ) (Z : Fin m → Scheme.{0}) (ι : ∀ j, Z j ⟶ X), (∀ j, IsClosedImmersion (ι j) ∧ IsIntegral (Z j)) ∧
    IsProper (Sigma.desc ι) ∧ Surjective (Sigma.desc ι)

theorem LeafComp_of (hC : LeafCoprod) (hG : LeafCompGeom) : LeafComp := by
  intro hH q k _ X p _ n i hZ
  obtain ⟨m, Z, ι, hι, hP, hS⟩ := hG k p
  exact ⟨∐ Z, Sigma.desc ι, hP, hS, hC hH q n i m Z (fun j => hZ (Z j) (ι j) (hι j).1 (hι j).2)⟩

end LateralTheory.E.E4
