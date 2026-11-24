module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.TensorSpan
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsHopfOrder
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
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import ReciprocityTheory.DualLattices.CotangentSurjective

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torsion_points_hopf_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → (∃ AA : HopfOrder (C := C) R N, AA.carrier = torsFun C T pt) ∧ (∀ a : T.A, (∀ φ : T.A →ₐ[R] R, φ a = 0) → a = 0) ∧ (∀ x, ∃! φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x) ∧ (∀ φ : T.A →ₐ[R] R, ∃ x, spMap φ ≫ T.y = pt x) ∧ ∀ x : N, p • x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.torsion_points_hopf_order | exact GlobalTheory.CompanionTheory.Relay.torsion_points_hopf_order | (intros; apply GlobalTheory.CompanionTheory.Relay.torsion_points_hopf_order <;> assumption)
