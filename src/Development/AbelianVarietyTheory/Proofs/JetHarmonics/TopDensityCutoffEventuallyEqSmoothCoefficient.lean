module

public import Formalism.HermitianCurvature.StatementTBB
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HsInnerSelfEqNormSq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorCutoffEqAndVanishStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

theorem Ew_cutF_eventually_eq : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → KB.CutWord P p.l0 w → ∀ᵐ c : Fin (P.r + 1) → ℂ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c) = TBB.Ew p (fun _ => 1) f (P.r + 1) w (TBB.bigPt P.r c) := by
  intro Wp Wq _ _ _ _ _ _ P p Cb f χ w hΘ hχ hf hw
  obtain ⟨δ, hδ, hδχ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x, x < δ → χ x = 0 := by
    have h := hχ
    unfold C6.IsCut0 at h
    tauto
  refine Filter.Eventually.of_forall fun c => ?_
  simp only [Ew_eq_norm_tv_sq]
  by_cases hG : 0 < TBB.Gp p (TBB.bigPt P.r c)
  · filter_upwards [Ioo_mem_nhdsGT hG] with ε hε
    rw [(GlobalTheory.T.topVector_cutoff_eq_and_vanish Wp Wq P p Cb χ δ ε f w c hΘ hw hχ hδχ hε.1 hf).1 hε.2]
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    have h := GlobalTheory.T.topVector_cutoff_eq_and_vanish Wp Wq P p Cb χ δ ε f w c hΘ hw hχ hδχ hε' hf
    rw [h.2.1 ((not_lt.1 hG).trans_lt (mul_pos hδ hε')), h.2.2 (not_lt.1 hG)]

end GlobalTheory.TopVec
