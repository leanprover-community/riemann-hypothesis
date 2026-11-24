module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdDecomp
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitP
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitW
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SplitB
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.KSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem gSplit_of (hF : FockMem) (hAw : AwayAct) : GSplit := by
  intro F E _ _ _ _ _ σ d R w L hL Ψ hΨ φ hφ g
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa g
  obtain ⟨y, hk'K, hk'w⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplitW.kSplit d R w k hk
  set k' := (R.ι w y)⁻¹ * k with hk'
  have hcomm := _root_.PositivityTheory.SiegelWeilFormula.KSplitW.commW d R w k' hk'w
  obtain ⟨A, hA⟩ := hAw F E σ d R w k' hk'w
  have hΨi : d.Indep w Ψ := ((hF F E σ d R).2.1 w Ψ hΨ).2
  obtain ⟨C, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplitP.siegel d hp
  refine ⟨p * k', y, C * A Ψ 0, (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ), _root_.PositivityTheory.SiegelWeilFormula.KSplitP.absE_pos _, ?_,
    fun y' => ⟨?_, fun P => ?_⟩⟩
  · rw [mul_assoc, hcomm y, hk', mul_inv_cancel_left]
  · obtain ⟨q, k₀, rfl, hq, hk₀, hloc⟩ := Glob.locIwasawa y'
    obtain ⟨tq, hPq, habs⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplitP.iota_isPar d R w q hq
    have e : p * k' * R.ι w (q * k₀) = (p * R.ι w q) * (R.ι w k₀ * k') := by
      rw [map_mul, mul_assoc p, ← mul_assoc k', hcomm q, mul_assoc (R.ι w q), hcomm k₀]
      simp only [mul_assoc]
    have hval := d.ok.hgt.val _ _ (_root_.PositivityTheory.SiegelWeilFormula.KSplitP.isPar_mul hp hPq) _ ((d.K).mul_mem (_root_.PositivityTheory.SiegelWeilFormula.KSplitW.iota_mem_K d R w k₀ hk₀) hk'K)
    have h0 : 0 ≤ d.a ((p * R.ι w q) * (R.ι w k₀ * k')) := by rw [hval]; exact NNReal.coe_nonneg _
    show ((d.a (p * k' * R.ι w (q * k₀))).toNNReal : ℝ) = _
    rw [e, Real.coe_toNNReal _ h0, hval, map_mul, map_mul, NNReal.coe_mul, habs, hloc]
  · have hsw := _root_.PositivityTheory.SiegelWeilFormula.KSplitP.fP_sw P
    have hΞ := (hL y' (fP P) hsw).2 Ψ hΨi (φ P) (hφ P).1 (hφ P).2
    have hΞs : d.om (R.ι w y') (φ P) ∈ d.sch := d.ok.dbl.weil.2.1.pres _ _ (hφ P).1
    have h2 := (hA Ψ hΨi).2 _ (hL y' (fP P) hsw).1 _ hΞs hΞ
    have hs2 : d.om k' (d.om (R.ι w y') (φ P)) ∈ d.sch := d.ok.dbl.weil.2.1.pres _ _ hΞs
    unfold SD.sec0
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hC _ hs2, ← _root_.PositivityTheory.SiegelWeilFormula.KSplitP.T_zero, h2]
    simp only [RD.tens, _root_.PositivityTheory.SiegelWeilFormula.KSplitP.loc_zero]
    ring

end PositivityTheory.SiegelWeilFormula.KSplit

end
