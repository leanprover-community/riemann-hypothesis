module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPSubTwoMulUnit
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.valuation_weierstrassP_sub_two_mul_eq_sq : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ¬ 3 ∣ N → ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → 2 * z ∉ L.lattice ∧ V.valuation (L.weierstrassP z - L.weierstrassP (2 * z)) = V.valuation u ^ 2 := by
  first | exact @GlobalTheory.CMModel.weierstrassP_sub_two_mul_unit | exact GlobalTheory.CMModel.weierstrassP_sub_two_mul_unit | (intros; apply GlobalTheory.CMModel.weierstrassP_sub_two_mul_unit <;> assumption)
