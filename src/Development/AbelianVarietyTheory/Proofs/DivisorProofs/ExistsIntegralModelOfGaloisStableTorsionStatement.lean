module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralModelOfGaloisStableTorsion
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.exists_integralModel_of_galoisStable_torsion : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ∀ (F : IntermediateField ℚ ℂ) (ι : Type) [Fintype ι] (T : ι → ℂ), L.g₂ ∈ F → L.g₃ ∈ F → u ∈ F → Stable L F T → (∀ i, T i ∉ L.lattice ∧ (N : ℂ) * T i ∈ L.lattice) → V.valuation (Fintype.card ι : ℂ) = 1 → ModelAt V F (latticeCurve L) 1 := by
  first | exact @GlobalTheory.CMModel.modelAt_of_stable_torsion | exact GlobalTheory.CMModel.modelAt_of_stable_torsion | (intros; apply GlobalTheory.CMModel.modelAt_of_stable_torsion <;> assumption)
