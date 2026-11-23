module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearDescentToBaseChangeOfForm
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_semilinear_descent_to_baseChange_of_form : ∀ {LL : Type} [Field LL] [Algebra ℚ LL] (L0 : IntermediateField ℚ LL) {Ks : Type} [Field Ks] [Algebra Ks LL]
    (kKs : Ks →+* L0), (∀ x, ((kKs x : L0) : LL) = algebraMap Ks LL x) →
    ∀ {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    (WK : Submodule Ks WL) {n : ℕ} (bs : Fin n → WL), (∀ i, bs i ∈ WK) →
    Submodule.span Ks (Set.range bs) = WK → LinearIndependent LL bs → Submodule.span LL (Set.range bs) = ⊤ →
    ∀ {KT : Type} [Field KT] [Algebra Ks KT] (rd : L0 →+* KT), (∀ s, algebraMap Ks KT s = rd (kKs s)) →
    ∃ Φ : WL →+ KT ⊗[Ks] WK, (∀ (c : L0) (x : WL), Φ ((c : LL) • x) = rd c • Φ x) ∧
      (∀ (f : WL →ₗ[LL] WL) (fr : WK →ₗ[Ks] WK), (∀ w : WK, (fr w : WL) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange KT fr (Φ x)) ∧
      ∀ w : WK, Φ (w : WL) = (1 : KT) ⊗ₜ[Ks] w := by
  first | exact @GlobalTheory.exists_semilinear_descent_to_baseChange | exact GlobalTheory.exists_semilinear_descent_to_baseChange | (intros; apply GlobalTheory.exists_semilinear_descent_to_baseChange <;> assumption)
