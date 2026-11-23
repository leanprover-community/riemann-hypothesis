module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormLineBundleDescent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.norm_line_bundle_descent : ∀ {X Y : Scheme.{0}} (q : X ⟶ Y), IsFinite q → ∀ (N : ∀ V : Y.Opens, Γ(X, q ⁻¹ᵁ V) →* Γ(Y, V)), (∀ (V W : Y.Opens) (h : W ≤ V) (a : Γ(X, q ⁻¹ᵁ V)), (Y.presheaf.map (homOfLE h).op).hom (N V a) = N W ((X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ V from fun _ hx => h hx)).op).hom a)) → (∀ (V : Y.Opens) (a : Γ(X, q ⁻¹ᵁ V)) (y : Y), y ∈ V → (y ∈ Y.basicOpen (N V a) ↔ ∀ x : X, q x = y → x ∈ X.basicOpen a)) → ∀ L : LB X, L.IsLB → (∀ y : Y, ∃ W : X.Opens, (∀ x : X, q x = y → x ∈ W) ∧ ∃ t : (L.pull W.ι).Gen, t.IsGen) → ∃ L' : LB Y, L'.IsLB ∧ ∀ (n : ℕ) (s : (lbPow L n).Sec), ∃ σ : (lbPow L' n).Sec, ∀ y : Y, y ∈ nonzeroLocus σ ↔ ∀ x : X, q x = y → x ∈ nonzeroLocus s := by
  exact @GlobalTheory.CompanionTheory.NormLB.exists_normLB
