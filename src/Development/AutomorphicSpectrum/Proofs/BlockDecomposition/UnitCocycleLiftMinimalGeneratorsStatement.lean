module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitCocycleLiftMinimalGenerators
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

theorem _root_.GlobalTheory.T.unit_cocycle_lift_minimal_generators : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (I : Ideal R) (r : ℕ) (t : Fin r → R),
    Ideal.span (Set.range t) = I → I ≤ IsLocalRing.maximalIdeal R →
    (∀ x : Fin r → R, ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I → ∀ i, x i ∈ IsLocalRing.maximalIdeal R) →
    ∀ (M : LB X) (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (u w : ∀ a, Γ(X, V a))
      (b : Fin r → ∀ a c, Γ(X, V a ⊓ V c)) (e : Fin r → R) (β : ∀ a, Γ(X, V a)) (l : Fin r),
      (∀ a, u a * w a - 1 ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a)) →
      (∀ a c, rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) *
        (1 + ∑ i, GlobalTheory.SmallExtLift.cst s _ (t i) * b i a c) ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a ⊓ V c)) →
      IsUnit (e l) →
      (∀ a c, ∑ i, GlobalTheory.SmallExtLift.cst s _ (e i) * b i a c - (rs X inf_le_left (β a) - rs X inf_le_right (β c)) ∈
        ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c)) →
      ∃ (J : Ideal R) (y z : ∀ a, Γ(X, V a)), ¬ I ≤ J ∧ (∀ a, y a * z a - 1 ∈ ext s J (V a)) ∧
        ∀ a c, rs X inf_le_left (y a) - tr M V j hj a c * rs X inf_le_right (y c) ∈ ext s J (V a ⊓ V c) := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.exists_correction | exact GlobalTheory.CompanionTheory.FewEq.exists_correction | (intros; apply GlobalTheory.CompanionTheory.FewEq.exists_correction <;> assumption)
