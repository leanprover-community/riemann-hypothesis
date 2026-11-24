module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphism
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
open GlobalTheory.ZV
theorem _root_.GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms : ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K) (M : LB X), M.IsLB → (∀ r r', SectionsHaveFiniteDimension p M r → SectionsHaveFiniteDimension p M r' → r = r') ∧ (∀ M' : LB X, M'.IsLB → LBIso M M' → (∀ r, SectionsHaveFiniteDimension p M r → SectionsHaveFiniteDimension p M' r) ∧ ∀ e, LBIso (lbPow M e) (lbPow M' e)) ∧ (∀ a e, LBIso (lbPow (lbPow M a) e) (lbPow M (a * e))) ∧ LBIso (lbPow M 1) M ∧ (∀ (Y : Scheme.{0}) (φ : Y ⟶ X) (e : ℕ), LBIso (lbPow (M.pull φ) e) ((lbPow M e).pull φ)) ∧ ∀ (Y : Scheme.{0}) (φ : Y ≅ X) (r : ℕ), SectionsHaveFiniteDimension p M r ↔ SectionsHaveFiniteDimension (φ.hom ≫ p) (M.pull φ.hom) r := by
  first | exact @GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant | exact GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant | (intros; apply GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant <;> assumption)
