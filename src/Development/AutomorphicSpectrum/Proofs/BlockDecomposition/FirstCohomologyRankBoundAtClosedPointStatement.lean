module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyRankBoundAtClosedPoint
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

theorem _root_.GlobalTheory.T.first_cohomology_rank_bound_at_closed_point : DepSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsSeparated s →
    ∀ n r : ℕ, n < r →
    (∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp (IsLocalRing.ResidueField R)) (φ : X' ⟶ X),
      IsPullback φ s' s (spMap (algebraMap R (IsLocalRing.ResidueField R))) →
      Module.Finite (IsLocalRing.ResidueField R) (HO1 s') ∧
        Module.finrank (IsLocalRing.ResidueField R) (HO1 s') ≤ n) →
    ∀ (A : Type) (V : A → X.Opens), ⨆ a, V a = ⊤ → (∀ a, IsAffineOpen (V a)) →
    ∀ b : Fin r → ∀ a c, Γ(X, V a ⊓ V c),
      (∀ i a c d, rs X (le₁₂ V a c d) (b i a c) + rs X (le₂₃ V a c d) (b i c d) -
        rs X (le₁₃ V a c d) (b i a d) ∈ ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c ⊓ V d)) →
      ∃ (e : Fin r → R) (β : ∀ a, Γ(X, V a)), (∃ l, IsUnit (e l)) ∧ ∀ a c,
        ∑ i, GlobalTheory.SmallExtLift.cst s _ (e i) * b i a c - (rs X inf_le_left (β a) - rs X inf_le_right (β c)) ∈
          ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c) := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.FibreRed.dep_fibre | exact GlobalTheory.CompanionTheory.FewEq.FibreRed.dep_fibre | (intros; apply GlobalTheory.CompanionTheory.FewEq.FibreRed.dep_fibre <;> assumption)
