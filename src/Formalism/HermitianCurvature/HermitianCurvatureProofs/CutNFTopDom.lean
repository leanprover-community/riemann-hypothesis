module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJD
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def NFOpOK (C : ℝ) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (N : ℕ) (Th : B.DiffOp P.k P.r Wp Wq) : Prop :=
  B.SmoothCoef (B.GPos p.T.base) Th ∧ B.Commutes p.T.base (B.GPos p.T.base) Th ∧
    CutMP.GlobCoef Th (C * ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1)) ∧
    (B.opOrder Th : ℝ) ≤ C * CutMP.nDim P.k P.r * ((N : ℝ) + 1)

def NFDomZero : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ),
    ¬ (D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)) → topD p H w c = 0

def NFDomMeas : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ ε : ℝ, 0 < ε →
      AEStronglyMeasurable (topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w)
        volume

theorem domination_at_zero_holds : NFDomZero := by
  intro Wp Wq _ _ _ _ _ _ P p H w c hc
  unfold topD TBB.Ew TBB.NP KB.Pl.RR
  generalize TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) = a
  generalize TBB.normC (fun x => 1) w = b
  generalize TBB.bigPt P.r c = x at hc ⊢
  unfold D.RRplace
  by_cases hl : D.IsLocPt x (P.r + 1)
  · have hG : ¬ 0 < TBB.Gp p x := fun h => hc ⟨hl, h⟩
    rw [dite_eq_left ⟨hl, hl⟩, dite_eq_right (by omega)]
    have hv : ∀ H' : B.Mat P.k P.r → (Wq →L[ℂ] Wp), D.vecV p.T.base p.ν' p.m₀ H' x = 0 := by
      intro H'
      unfold D.vecV
      rw [dite_eq_right]
      rintro ⟨-, h⟩
      apply hG
      unfold TBB.Gp
      exact h
    have h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
      unfold B.hsVec
      ext i
      simp
    have hi0 : B.hsInner (0 : Wq →L[ℂ] Wp) 0 = 0 := by
      simp [B.hsInner, h0]
    simp [hv]
    split_ifs with hw
    · simp [hi0]
    · unfold Top.topOf
      simp [hv, hi0]
  · simp [hl]

end

end Formalism.FourierDecayAlt.P.CutBP
