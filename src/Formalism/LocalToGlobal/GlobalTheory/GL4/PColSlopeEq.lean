module

public import Formalism.LocalToGlobal.GlobalTheory.GL4.PColInf
public import Formalism.SharpRestriction.GlobalSchurBounds.SlopeMaxOpenOfHookTwoLeV
public import Formalism.LocalToGlobal.GlobalTheory.GL4.PColSlope
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module NumberField

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions.flipTwoThree

def TSpanEqVV : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), TSpan K lam = VV K lam

def ZBasisStd : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), ∃ (Z : ZBasis lam) (μs : ι → ℝ), Nonempty Z.J0 ∧
    (∀ τ, MuStd (lam τ).natW (μs τ)) ∧ -Real.log (gramZ lam Z).det / (Fintype.card Z.J0 : ℝ) = ∑ τ, μs τ

def QSlope (D : D7) : Prop :=
  ∀ u (CV : ColVal D u) c τ, (CV.Q c τ).mu = -Real.log (Tu D u) / D.R.k

theorem wsum_eq_colAbs (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ((wsum ((D.fm u).lam 0 τ) : ℤ) : ℝ) = colAbs D u τ := by
  have hk : D.R.N 0 = D.R.k := by simp only [Ranks.N]; omega
  rw [colAbs, wsum, Int.cast_sum]
  simp_rw [Formalism.MainNotions.flipTwoThree.weight_eq_lamCol]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((lamCol D u τ i : ℚ) : ℝ)) (D.R.N 0), hk]

theorem colSlopeEq_of (h1 : TSpanEqVV) (h2 : ZBasisStd) (D : D7) (h3 : QSlope D) : ColSlopeEq D := by
  intro u CV
  obtain ⟨Z, μs, hne, hμ, hdet⟩ := h2 D.what₂.Tau (D.R.N 0) ((D.fm u).lam 0)
  refine ⟨μs, hμ, ?_⟩
  haveI : Nonempty Z.J0 := hne
  haveI := CV.ne
  have hm := col_mu CV (h1 D.what₂.LL D.what₂.Tau (D.R.N 0) ((D.fm u).lam 0)) Z
  have key : ∑ c, ∑ τ, ((wsum ((D.fm u).lam 0 τ) * (Fintype.card Z.J0 : ℤ) : ℤ) : ℝ) * (CV.Q c τ).mu =
      ∑ _c : (D.mem u).C.cls 0, ∑ τ, colAbs D u τ * (Fintype.card Z.J0 : ℝ) *
        (-Real.log (Tu D u) / D.R.k) := by
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun τ _ => ?_
    rw [h3 u CV c τ, ← wsum_eq_colAbs]
    push_cast
    ring
  have e2 : ∑ τ, colAbs D u τ * (Fintype.card Z.J0 : ℝ) * (-Real.log (Tu D u) / D.R.k) =
      -((Fintype.card Z.J0 : ℝ) * ∑ τ, colAbs D u τ / D.R.k * Real.log (Tu D u)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  rw [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, e2] at hm
  have hN : (0 : ℝ) < Fintype.card Z.J0 := by exact_mod_cast Fintype.card_pos
  have hC : (0 : ℝ) < Fintype.card ((D.mem u).C.cls 0) := by exact_mod_cast Fintype.card_pos
  rw [← hdet]
  apply mul_left_cancel₀ (mul_ne_zero hN.ne' hC.ne')
  have hN' : (Fintype.card Z.J0 : ℝ) ≠ 0 := hN.ne'
  have e3 : (Fintype.card Z.J0 : ℝ) * Fintype.card ((D.mem u).C.cls 0) *
      (-Real.log (gramZ ((D.fm u).lam 0) Z).det / Fintype.card Z.J0) =
      -(Fintype.card ((D.mem u).C.cls 0) * Real.log (gramZ ((D.fm u).lam 0) Z).det) := by
    field_simp
  rw [hm, mul_add, e3]
  ring

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
