module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenIsCompactTwoBlockParahoricSubgroupStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasureRealDoubleCosetEqRelIndexConjMulStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairwiseDisjointParahoricTorusDoubleCosetAntitonStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexConjUniformizerPowerDiagonalGLReindex
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexTwoBlockParahoricConjTorusDiagElementStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne

@[expose] public section

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ChainCells

theorem vol_dcell_and_disjoint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) [MeasurableSpace (GL (Fin r ⊕ Blocks l t) k)] [BorelSpace (GL (Fin r ⊕ Blocks l t) k)]
    (m : Measure (GL (Fin r ⊕ Blocks l t) k)) [m.IsHaarMeasure], m (parahoric k (Fin r) (Blocks l t)) = 1 →
  ∀ [MeasurableSpace (GL (Fin (l * t)) k)] [BorelSpace (GL (Fin (l * t)) k)] (μK : Measure (GL (Fin (l * t)) k))
    [μK.IsHaarMeasure], μK (KO k (Fin (l * t))) = 1 →
  (∀ e : Fin (l * t) → ℤ, m.real (dcell ϖ (e ∘ (blkEquiv l t).symm)) =
    (resCard k : ℝ) ^ ((r : ℤ) * sumAbs e) * μK.real (cell k (Fin (l * t)) ϖ e)) ∧
  Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
    (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))) := by
  intro k _ _ _ _ ϖ hϖ r l t _ _ m _ hm _ _ μK _ hμK
  refine ⟨fun e => ?_, GlobalTheory.T.pairwise_disjoint_parahoricTorusDoubleCoset_antitone k ϖ hϖ r l t⟩
  obtain ⟨ho, hc⟩ := GlobalTheory.T.isOpen_isCompact_twoBlockParahoricSubgroup k (Fin r) (Blocks l t)
  have h1 := GlobalTheory.T.measureReal_doubleCoset_eq_relIndex_conj_mul m _ ho hc (mtor (A := Fin r) ϖ (e ∘ (blkEquiv l t).symm))
  have h2 := GlobalTheory.T.measureReal_doubleCoset_eq_relIndex_conj_mul μK (KO k (Fin (l * t))) SplitFlip.isOpen_KO SplitFlip.isCompact_KO (torusElt k _ ϖ e)
  have hs : sumAbs (e ∘ (blkEquiv l t).symm) = sumAbs e := by
    unfold sumAbs; exact Equiv.sum_comp (blkEquiv l t).symm (fun i => |e i|)
  have hm1 : m.real (parahoric k (Fin r) (Blocks l t) : Set _) = 1 := by simp [Measure.real, hm]
  have hK1 : μK.real (KO k (Fin (l * t)) : Set _) = 1 := by simp [Measure.real, hμK]
  rw [dcell, h1, cell, h2, hm1, hK1, GlobalTheory.T.relIndex_twoBlockParahoric_conj_torusDiagElement k ϖ hϖ, GlobalTheory.ReindexTorus.relIndex_conj_torusElt_reindex k ϖ _ _ (blkEquiv l t), hs]
  simp

end GlobalTheory.ChainCells
