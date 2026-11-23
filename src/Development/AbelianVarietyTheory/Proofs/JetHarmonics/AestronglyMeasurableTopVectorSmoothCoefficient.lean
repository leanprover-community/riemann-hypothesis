module

public import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellVectorAestronglyMeasurable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiftedWordContinuousOnGPos
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

theorem aesm_pi_of_finite {α ι E : Type} [MeasurableSpace α] {μ : Measure α} [Finite ι] [NormedAddCommGroup E]
    (f : α → ι → E) (hf : ∀ i, AEStronglyMeasurable (fun a => f a i) μ) : AEStronglyMeasurable f μ := by
  classical
  have := Fintype.ofFinite ι
  have e : f = fun a => ∑ i, (Pi.single i (f a i) : ι → E) := by
    funext a; rw [Finset.univ_sum_single]
  rw [e]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (continuous_single (A := fun _ : ι => E) i).comp_aestronglyMeasurable (hf i)

theorem measurable_nPt_bigPt (k r : ℕ) (TT : ℝ) :
    Measurable fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c) := by
  have e : (fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c)) = fun c =>
      ∏ i : Fin (r + 1), (if 1 + (i : ℕ) = r + 1 then (‖c (Fin.last r)‖ ^ 2 - TT) ^ (k - 1)
        else ‖c i‖ ^ (2 * (C.Mlev k r (1 + (i : ℕ)) - 2))) := by
    funext c
    unfold TBB.nPt D.ptGG
    rw [Formalism.FourierDecayAlt.P.CutBP.ptLast_bigPt, Complex.normSq_eq_norm_sq]
    unfold TBB.bigPt
    rw [Formalism.FourierDecayAlt.P.CutBP.level_product_of_constant_weights]
  rw [e]
  refine Finset.measurable_prod _ fun i _ => ?_
  split_ifs
  · fun_prop
  · exact ((measurable_pi_apply i).norm).pow_const _

theorem measurable_wPt_bigPt (r : ℕ) (TT : ℝ) :
    Measurable fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c) := by
  have e : (fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c)) = fun c =>
      ‖∏ i, c i‖ ^ 2 / (‖∏ i, c i‖ ^ 2 - TT * ‖∏ i : Fin r, c i.castSucc‖ ^ 2) := by
    funext c
    show Top.wPt TT r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
    unfold Top.wPt D.ptG
    rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rw [e]
  refine Measurable.div ?_ ?_
  · exact (by fun_prop : Continuous fun c : Fin (r + 1) → ℂ => ‖∏ i, c i‖ ^ 2).measurable
  · exact (by fun_prop : Continuous fun c : Fin (r + 1) → ℂ =>
      ‖∏ i, c i‖ ^ 2 - TT * ‖∏ i : Fin r, c i.castSucc‖ ^ 2).measurable

theorem aestronglyMeasurable_tv : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → B.CkOn ⊤ (B.GV P.k P.r) H →
    AEStronglyMeasurable (tv p H w) volume := by
  intro Wp Wq _ _ _ _ _ _ P p Cb H w hD hw hH
  unfold tv
  refine (PiLp.continuous_toLp 2 _).comp_aestronglyMeasurable (aesm_pi_of_finite _ fun x => ?_)
  have hV := GlobalTheory.bigCell_vector_aestronglyMeasurable Wp Wq P p _ (GlobalTheory.liftedWord_continuousOn_GPos Wp Wq P p Cb w x.1 H hD hw hH)
  have hc : Continuous fun X : Wq →L[ℂ] Wp => B.hsVec ((p.TP.E x.2).comp X) := by
    unfold B.hsVec
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact (p.TP.E x.2).continuous.comp
      (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous
  refine AEStronglyMeasurable.smul (f := fun c : Fin (P.r + 1) → ℂ =>
    ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
        Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) x.1 x.2 : ℝ) : ℂ)) ?_ (hc.comp_aestronglyMeasurable hV)
  refine (Complex.measurable_ofReal.comp ?_).aestronglyMeasurable
  refine (measurable_nPt_bigPt _ _ _).sqrt.mul ?_
  unfold Top.dH
  exact (((measurable_wPt_bigPt _ _).pow_const _).mul_const _).sqrt

end GlobalTheory.TopVec
