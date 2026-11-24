module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinatesPullIsoNonzeroLocus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.sectionCoordinates_pull_iso_nonzeroLocus : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec), M.IsLB → (∀ (X' : Scheme.{0}) (π : X' ⟶ X), ∃ th' : I → (M.pull π).Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X') (v : I → R), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v) ∧ (∀ M' : LB X, M'.IsLB → LBIso M M' → ∃ th' : I → M'.Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), SecCoord M' th' x v ↔ SecCoord M th x v) ∧ ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R) (i : I) (p : Sp R), SecCoord M th x v → (x p ∈ Out.nonzeroLocus (th i) ↔ v i ∉ p.asIdeal) := by
  first | exact @GlobalTheory.ZM.CoordMove.secCoord_pull_iso_locus | exact GlobalTheory.ZM.CoordMove.secCoord_pull_iso_locus | (intros; apply GlobalTheory.ZM.CoordMove.secCoord_pull_iso_locus <;> assumption)
