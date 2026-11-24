module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDom
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def xD (φ : ℝ → ℝ) : ℝ → ℝ := fun x => x * deriv φ x

def IsSCoef {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (Q : ℕ) (L : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq) : Prop :=
  ∀ (s : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV P.k P.r) F → ∀ g ∈ C6.domL p.T.base ∅,
    ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ (-s) : ℝ) : ℂ) •
        p.Θ.Θ w e (fun g' => ((Gf P.k P.r p.T.base.z p.T.base.z' g' ^ s : ℝ) : ℂ) • F g') g =
      ∑ q : Fin (Q + 1), ((s ^ (q : ℕ) : ℝ) : ℂ) • B.opApply (L q) F g

def NFUnfoldTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), w ≠ [] →
    D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
      topD p H w c = (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
          Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c))) *
        ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P, Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) e ρ ^ 2 *
          ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e H) (TBB.bigPt P.r c)))‖ ^ 2

def NFVMul : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (φ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (γ : C.LPt), D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
      p.V (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g) γ = ((φ (TBB.Gp p γ) : ℝ) : ℂ) • p.V F γ

def NFCutSup : Prop :=
  ∀ χ : ℝ → ℝ, C6.IsCut0 χ → ∀ q : ℕ, ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ∀ x : ℝ, 0 < x →
    |(xD^[q] (fun y => χ (y / ε))) x| ≤ K

def NFLeibV : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → ∀ w, KB.CutWord P p.l0 w → ∀ e : Wd.Ix (Fin w.length),
      ∃ (Q : ℕ) (L : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq),
        (∀ q, B.SmoothCoef (C6.domL p.T.base ∅) (L q)) ∧ IsSCoef p w e Q L ∧
        ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ),
          B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
          Cc * ((P.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
          ∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
            p.V (p.Θ.Θ w e (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g)) γ =
              ∑ q : Fin (Q + 1), (((xD^[(q : ℕ)] φ) (TBB.Gp p γ) : ℝ) : ℂ) • p.V (B.opApply (L q) F) γ

def NFEmptyOps : Prop :=
  ∃ C₁ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (N : ℕ), ∃ Th₀ Th₁ : B.DiffOp P.k P.r Wp Wq, NFOpOK C₁ p N Th₀ ∧ NFOpOK C₁ p N Th₁ ∧
      ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r),
        B.opApply Th₀ F g = F g ∧ B.opApply Th₁ F g = ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • F g

theorem unfolding_top_term_holds : NFUnfoldTop := by
  intro Wp Wq _ _ _ _ _ _ P p H w c hw hloc _
  have hn : TBB.normC (fun _ => 1) w = 1 := by
    simp [TBB.normC]
  have hRR : p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c) =
      Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP H w (TBB.bigPt P.r c) (TBB.bigPt P.r c) := by
    rw [KB.Pl.RR, D.RRplace, dite_eq_left ⟨hloc, hloc⟩, dite_eq_right (Nat.not_succ_le_self _), if_pos rfl, if_neg hw]
  show (TBB.NP p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).re = _
  rw [TBB.NP, hn, div_one, hRR, Top.topOf, Complex.re_ofReal_mul]
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hsq : ∀ v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp), (inner ℂ v v : ℂ).re = ‖v‖ ^ 2 :=
    fun v => by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [Complex.re_ofReal_mul, B.hsInner, hsq]
  simp only [TBB.TTp, KB.Pl.V]
  ring

end

end Formalism.FourierDecayAlt.P.CutBP
