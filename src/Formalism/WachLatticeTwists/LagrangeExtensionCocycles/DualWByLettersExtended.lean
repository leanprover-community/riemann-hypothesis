module

public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatWPrimeExt
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementTop
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.EtaleClosedPointLiftsSimpleRootsMonic
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.Letters
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.MemSpanOfFrobeniusMemSpan
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.ResidueQuotientHolds
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.ResidueSeriesExpansionHolds
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.SecondDescentFreePartHolds
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.SecondDescentStatementHolds
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.SizeBoundSecondCase
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.SumVal
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.TotallyRealRoots
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.UnitLemmaCaseALevelZero
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.UnitLemmaPrimeExtensionHolds
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

theorem lifting_theorem : StatLIFT := etaleClosed_point_lifts_simple_roots_monic

theorem dual_w_by_letters : StatWPrime := unit_lemma_prime_case_holds

theorem dual_w_by_letters_extended : StatWPrimeExt := unit_lemma_prime_extension_holds

theorem lagrange_and_w_all : StatLagrange ∧ StatLagrangeKill ∧ StatWB ∧ StatWA ∧ StatWA0 :=
  ⟨lagrange_annihilation, lagrange_resolvent_kills_class, unit_lemma_case_b_holds, unit_lemma_case_a_unconditional, unit_lemma_case_a_level_zero⟩

theorem descent_cost_all : StatChiVal ∧ StatDescentStep ∧ StatDescent ∧ StatCostFormula ∧ StatCostBound ∧
    StatCostKills ∧ Stat1 ∧ Stat2Free ∧ Stat2 ∧ StatResFinite ∧ StatResAlways ∧ StatResQ ∧ StatResCut :=
  ⟨character_value_formula_holds, descent_reduces_level, mem_span_of_frobenius_mem_span, cost_formula_holds, cost_bound,
    cost_bound_kills_obstruction, unconditional_first_statement, second_descent_free_part_holds, second_descent_statement_holds, residue_finite_holds, residue_always_holds,
    residue_quotient_holds, residue_at_truncation⟩

theorem superadditivity_frame_all : StatASuper ∧ StatFrameInv ∧ StatSigJNum :=
  ⟨superadditivity_holds, frame_invariance_holds, sigma_j_numerical⟩

theorem lifting_size_bounds_all : StatSumValEnd ∧ StatSumValGen ∧ StatResSeries ∧ StatSigJ ∧ StatSizeB ∧ StatSizeA :=
  ⟨valuation_sum_at_endpoint, valuation_sum_general_index, residue_series_expansion_holds, sign_character_at_j_holds, size_bound_second_case, size_bound_first_case⟩

end Formalism.RepresentationBoundsCohomology.N2
