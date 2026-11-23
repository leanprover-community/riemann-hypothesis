module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionEqSumKFiniteModuleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKFiniteModuleIrreducibleUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteSmoothVecOfIrreducibleUnitaryRepStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteSpanRaisingOperatorWordsLowestKTypeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KTypeWeightMemConeOverLowestKTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypeSpaceHolomorphicKModuleKilledStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaisingSpanEqSpanWordsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP

@[expose] public section

open Matrix GlobalTheory.HolDS

namespace GlobalTheory.HolDS

theorem holomorphicDiscreteSeries_holds : GlobalTheory.Published.HolomorphicDiscreteSeries := by
  intro n ε lam hHC hHol H _ _ σ hDS
  obtain ⟨hc, hnt, hU, hI, -⟩ := id hDS
  haveI := hc
  haveI := hnt
  obtain ⟨D, E, hK⟩ := GlobalTheory.T.exists_kFiniteModule_irreducible_unitary n ε H σ hU hI
  have low := GlobalTheory.T.lowestKTypeSpace_holomorphicKModule_killed n ε H σ D E lam hHC hHol hDS hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun μ S hS => GlobalTheory.T.kType_weight_mem_cone_over_lowest_kType n ε H σ D E lam hHC hHol hDS hK μ S hS
  · exact fun v hv => GlobalTheory.T.kFinite_smoothVec_of_irreducible_unitaryRep n ε H σ hU hI v hv
  · intro Z hZ v hv
    let vD : D := ⟨v, low.1 hv⟩
    have hx : vD ∈ (Formalism.MainNotions.S.lowKSub ε lam σ).comap D.subtype := hv
    have h0 : (∑ a, ∑ b, Z a b • E a b vD : D) = 0 := by
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      by_cases hab : ε a = false ∧ ε b = true
      · rw [low.2.2.2 b a hab.2 hab.1 vD hx, smul_zero]
      · rw [hZ a b hab, zero_smul]
    change GlobalTheory.SmVec.dRepC (Formalism.REAL.Jm ε) σ Z (vD : H) = 0
    rw [GlobalTheory.T.complexifiedDerivedAction_eq_sum_kFiniteModule n ε H σ D E hK Z vD,
      h0, Submodule.coe_zero]
  · intro v
    rw [GlobalTheory.T.raisingSpan_eq_map_span_words_of_isKMod n ε H σ D E hK _ low.1, GlobalTheory.T.kFinite_span_raisingOperator_words_lowestKType n ε H σ D E lam hHC hHol hDS hK,
      Submodule.map_top, Submodule.range_subtype]
    exact (hK.mem v).symm

end GlobalTheory.HolDS
