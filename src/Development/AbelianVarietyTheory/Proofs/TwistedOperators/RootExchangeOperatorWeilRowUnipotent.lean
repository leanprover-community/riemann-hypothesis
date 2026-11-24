module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousWittExtendByZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.RootEx.RowSign
open GlobalTheory.RootEx.Exchange

theorem mat_add_gRow {k : Type} [Field k] {n n' : Type} [DecidableEq n] {c : ℕ} (q : Fin c) (u : n' → k) (x₀ : Matrix n n' k)
    (y : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k) :
    mat x₀ (y + gRow q u) = mat x₀ y + rowM n c (q.val + 1) u := by
  ext r s
  rcases r with r | l <;> rcases s with s | i <;>
    simp [mat, gRow, rowM, Fin.ext_iff, add_assoc]

private theorem ch_affPt_add_sRow {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] {c : ℕ} (q : Fin c) (u : n' → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    ch (affPt (q.val + 1) x₀ (e + sRow q u e)) = ch (affPt (q.val + 1) x₀ e) := by
  unfold ch
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [affPt, sRow]

theorem opE_om_rowE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (u : n' → k) (x₀ : Matrix n n' k), opE ψ ν p (om μ (rowE (c + 1) p u) 1 Φ.1) x₀ = opE ψ ν p (fun x => Φ.1 (x + rowM n c p u)) x₀ := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ hψ ν _ μ Φ u x₀
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨q, rfl⟩ : ∃ q : Fin c, q.val + 1 = p := ⟨⟨p - 1, by omega⟩, by show p - 1 + 1 = p; omega⟩
  have hΦ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
  have hA : Continuous fun e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k =>
      affPt (q.val + 1) x₀ e :=
    ((continuous_mat x₀).comp (continuous_wittExtendByZero _)).congr fun e => (affPt_eq _ x₀ e).symm
  have hch : Continuous fun x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => ch x :=
    continuous_finsetSum _ fun i _ => continuous_id.matrix_elem _ _
  set f : ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) → ℂ := fun e =>
    Φ.1 (affPt (q.val + 1) x₀ e + rowM n c (q.val + 1) u) * (ψ (-ch (affPt (q.val + 1) x₀ e)) : ℂ) with hf_def
  have hf : Continuous f := by
    refine (hΦ.1.continuous.comp (hA.add continuous_const)).mul ?_
    exact continuous_subtype_val.comp (hψ.comp (hch.comp hA).neg)
  have hS : Continuous (sRow (n := n) (n' := n') q u) := by
    refine continuous_pi fun i => ?_
    rcases i with ⟨⟨r, s | s⟩, hi⟩
    · exact ((continuous_apply _).comp (continuous_wittExtendByZero _)).mul continuous_const
    · exact continuous_const
  have h0 : ∀ e (i : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs}),
      ¬ (∃ s, i.1.2 = Sum.inl s) → sRow q u e i = 0 := by
    rintro e ⟨⟨r, s | s⟩, hi⟩ h
    · exact absurd ⟨s, rfl⟩ h
    · rfl
  have h1 : ∀ e e' : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k,
      (∀ i, ¬ (∃ s, i.1.2 = Sum.inl s) → e i = e' i) → sRow q u e = sRow q u e' := by
    intro e e' he
    funext i
    rcases i with ⟨⟨r, s | s⟩, hi⟩
    · simp only [sRow, Sum.elim_inl]
      congr 1
      simp only [ext0]
      split_ifs with h
      · exact he _ (by simp)
      · rfl
    · rfl
  have hL : ∀ e, om μ (rowE (c + 1) (q.val + 1) u) 1 Φ.1 (affPt (q.val + 1) x₀ e) *
      (ψ (-ch (affPt (q.val + 1) x₀ e)) : ℂ) = f (e + sRow q u e) := by
    intro e
    rw [om_rowE, affPt_mul_rowE, mat_add_gRow, ← affPt_eq]
    simp only [hf_def, ch_affPt_add_sRow]
  unfold opE
  simp_rw [hL]
  exact integral_shear ν (fun i => ∃ s, i.1.2 = Sum.inl s) (sRow q u) hS h0 h1 f hf

end GlobalTheory.RootEx.RowSign
