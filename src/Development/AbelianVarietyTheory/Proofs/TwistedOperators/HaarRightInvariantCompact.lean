module

public import Mathlib.MeasureTheory.Group.Measure
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.RealPlaceAnalysis.StatementA
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible IsIrredSubrep)
open scoped InnerProductSpace
open scoped Pointwise

namespace GlobalTheory.CompactRight

theorem map_mul_right_eq_of_mem_compact {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (k : G) (hk : k ∈ K) : Measure.map (· * k) μ = μ := by
  set c := Measure.haarScalarFactor (Measure.map (· * k) μ) μ with hc
  have hmapEq : Measure.map (· * k) μ = c • μ := Measure.isMulLeftInvariant_eq_smul _ μ
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  set S : Set G := V * (K : Set G) with hS
  have hScpt : IsCompact S := hVc.mul hK
  have hVsubS : V ⊆ S := by
    intro v hv
    exact Set.mem_mul.2 ⟨v, hv, 1, K.one_mem, mul_one v⟩
  have hSpre : (· * k) ⁻¹' S = S := by
    ext x
    simp only [Set.mem_preimage, hS, Set.mem_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨v, hv, a, ha, hva⟩
      refine ⟨v, hv, a * k⁻¹, K.mul_mem ha (K.inv_mem hk), ?_⟩
      rw [← mul_assoc, hva, mul_inv_cancel_right]
    · rintro ⟨v, hv, a, ha, hva⟩
      exact ⟨v, hv, a * k, K.mul_mem ha hk, by rw [← mul_assoc, hva]⟩
  have hSpos : μ S ≠ 0 := (lt_of_lt_of_le (Measure.measure_pos_of_mem_nhds (μ := μ) hV1) (measure_mono hVsubS)).ne'
  have hSfin : μ S ≠ ⊤ := hScpt.measure_lt_top.ne
  have hmapS : Measure.map (· * k) μ S = μ S := by
    rw [show (· * k) = (MeasurableEquiv.mulRight k : G → G) from rfl, MeasurableEquiv.map_apply]
    exact congrArg μ hSpre
  have hcOne : c = 1 := by
    have hcEq : (c : ENNReal) * μ S = 1 * μ S := by
      have hcS := hmapS
      rw [hmapEq, smul_apply, ENNReal.smul_def, smul_eq_mul] at hcS
      rw [one_mul]
      exact hcS
    exact_mod_cast (ENNReal.mul_left_inj hSpos hSfin).1 hcEq
  rw [hmapEq, hcOne, one_smul]

end GlobalTheory.CompactRight
