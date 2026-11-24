module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitRootCyclotomicExpExpansions
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

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

theorem _root_.GlobalTheory.T.exists_unit_root_cyclotomicExpExpansions : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), l ≠ 2 → (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) → ∃ (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : ↥(OL LL)) (jj : ℕ → PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1), (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ maximalIdeal ↥(OL LL) ∧ ∀ b ∈ Finset.Ioo 0 l, IsLocExp l ↥(OL LL) ↥LL.1 (OL LL).val.toRingHom (ζ ^ b - 1) (u : ℤ_[l]) (jj b) ∧ IsExpAt (OL LL).val.toRingHom (ζ ^ b) (jj b) := by
  first | exact @GlobalTheory.WachExp.exists_locExp_expAt | exact GlobalTheory.WachExp.exists_locExp_expAt | (intros; apply GlobalTheory.WachExp.exists_locExp_expAt <;> assumption)
