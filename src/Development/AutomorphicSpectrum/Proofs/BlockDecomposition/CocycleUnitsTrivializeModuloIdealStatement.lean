module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleUnitsTrivializeModuloIdeal
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

theorem _root_.GlobalTheory.T.cocycle_units_trivialize_modulo_ideal : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Ideal R) (M : LB X), M.IsLB →
    ∀ (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)), ⨆ a, V a = ⊤ →
    ∀ y z : ∀ a, Γ(X, V a), (∀ a, y a * z a - 1 ∈ ext s J (V a)) →
      (∀ a b, rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b) ∈ ext s J (V a ⊓ V b)) →
      GlobalTheory.AbLaw.Triv (M.pull (pullback.fst s (spMap (Ideal.Quotient.mk J)))) := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.triv_of_compatible_mod | exact GlobalTheory.CompanionTheory.FewEq.triv_of_compatible_mod | (intros; apply GlobalTheory.CompanionTheory.FewEq.triv_of_compatible_mod <;> assumption)
