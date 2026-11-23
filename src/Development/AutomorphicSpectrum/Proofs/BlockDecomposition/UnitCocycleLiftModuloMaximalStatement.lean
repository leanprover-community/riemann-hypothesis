module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitCocycleLiftModuloMaximal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

theorem _root_.GlobalTheory.T.unit_cocycle_lift_modulo_maximal : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (𝔪 I : Ideal R) (r : ℕ) (t : Fin r → R),
    Ideal.span (Set.range t) = I → I ≤ 𝔪 → ∀ (M : LB X), M.IsLB →
    ∀ (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (u w : ∀ a, Γ(X, V a)),
      (∀ a, u a * w a - 1 ∈ ext s (𝔪 * I) (V a)) →
      (∀ a c, rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) ∈ ext s I (V a ⊓ V c)) →
      ∃ b : Fin r → ∀ a c, Γ(X, V a ⊓ V c),
        (∀ a c d, ∑ i, GlobalTheory.SmallExtLift.cst s _ (t i) * (rs X (le₁₂ V a c d) (b i a c) +
            rs X (le₂₃ V a c d) (b i c d) - rs X (le₁₃ V a c d) (b i a d)) ∈ ext s (𝔪 * I) (V a ⊓ V c ⊓ V d)) ∧
        ∀ a c, rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) *
          (1 + ∑ i, GlobalTheory.SmallExtLift.cst s _ (t i) * b i a c) ∈ ext s (𝔪 * I) (V a ⊓ V c) := by
  exact @GlobalTheory.CompanionTheory.FewEq.Cochain.exists_cochain
