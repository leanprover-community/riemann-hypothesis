module

public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllipticCurveLatticeBaseChangeStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane
theorem _root_.GlobalTheory.T.ellipticCurve_lattice_baseChange_stable : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (Lf : (R →+* ℂ) → PeriodPair) (R₁ : Type) [CommRing R₁] (f : R →+* R₁) (P₁ : Out.PolAV (Sp R₁)) (φ : P₁.A.left ⟶ P.A.left) (v₁ : epsR R₁ ⟶ P₁.A), (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : R →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (Lf s').lattice ↔ z • w' ∈ u'.Λ)) → IsPolFibre f P P₁ φ → IsVecOver f φ v v₁ → (P₁.g = 1 ∧ IsLieBasis ![v₁] ∧ (∀ (R' : Type) [CommRing R'] (f' : R₁ →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P₁.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P₁ P' φ' → IsVecOver f' φ' v₁ v' → IsLieBasis ![v']) ∧ ∀ s' : R₁ →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P₁.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P₁ P' φ' → IsVecOver s' φ' v₁ v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ ((fun s : R₁ →+* ℂ => Lf (s.comp f)) s').lattice ↔ z • w' ∈ u'.Λ)) := by
  first | exact @GlobalTheory.curve_lattice_baseChange | exact GlobalTheory.curve_lattice_baseChange | (intros; apply GlobalTheory.curve_lattice_baseChange <;> assumption)
