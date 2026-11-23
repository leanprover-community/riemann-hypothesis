module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAnalyticGermsNoetherian
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def coordGerm {σ : Type} [Fintype σ] (w : σ → ℂ) (i : σ) : holGerms w :=
  ⟨↑(fun z : σ → ℂ => z i), fun z => z i,
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w, rfl⟩

def IsFiniteGermProjection {σ : Type} [Fintype σ] (w : σ → ℂ) (P : Ideal (holGerms w)) {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) : Prop :=
  (∀ φ : holGerms (A w), germPull A (A.analyticAt w) rfl φ ∈ P → φ = 0) ∧
  (∀ ψ : holGerms w, ∃ F : MvPolynomial σ (holGerms (A w)),
      ψ - MvPolynomial.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w) F ∈ P) ∧
  (∀ i : σ, ∃ q : Polynomial (holGerms (A w)), q.Monic ∧
      q.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w i) ∈ P)

theorem isFiniteGermProjection_bot {σ : Type} [Fintype σ] (w : σ → ℂ) :
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w ⊥ A := by
  classical
  let e : (σ → ℂ) ≃L[ℂ] (Fin (Fintype.card σ) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ).symm).toContinuousLinearEquiv
  let A : (σ → ℂ) →L[ℂ] (Fin (Fintype.card σ) → ℂ) := e
  have hA : AnalyticAt ℂ (⇑A) w := A.analyticAt w
  have hB : AnalyticAt ℂ (⇑e.symm) (A w) := e.symm.analyticAt _
  have hBe : e.symm (A w) = w := e.symm_apply_apply w
  have back : ∀ φ : holGerms (A w), germPull e.symm hB hBe (germPull A hA rfl φ) = φ := fun φ =>
    germPull_germPull _ _ hA rfl hB hBe (fun y => e.apply_symm_apply y) φ
  have fwd : ∀ ψ : holGerms w, germPull A hA rfl (germPull e.symm hB hBe ψ) = ψ := fun ψ =>
    germPull_germPull _ _ hB hBe hA rfl (fun z => e.symm_apply_apply z) ψ
  refine ⟨Fintype.card σ, A, ?_, ?_, ?_⟩
  · intro φ hφ
    rw [Ideal.mem_bot] at hφ
    rw [← back φ, hφ, map_zero]
  · intro ψ
    refine ⟨MvPolynomial.C (germPull e.symm hB hBe ψ), ?_⟩
    rw [MvPolynomial.eval₂_C, fwd, sub_self]
    exact Ideal.zero_mem _
  · intro i
    have hc : AnalyticAt ℂ (fun y : Fin (Fintype.card σ) → ℂ => e.symm y i) (A w) :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).comp
        (e.symm : (Fin (Fintype.card σ) → ℂ) →L[ℂ] (σ → ℂ))).analyticAt _
    let c : holGerms (A w) := ⟨↑(fun y : Fin (Fintype.card σ) → ℂ => e.symm y i), _, hc, rfl⟩
    refine ⟨Polynomial.X - Polynomial.C c, Polynomial.monic_X_sub_C c, ?_⟩
    rw [Ideal.mem_bot, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero]
    apply Subtype.ext
    rw [germPull_coe _ hA rfl c _ rfl]
    show (↑(fun z : σ → ℂ => z i) : Germ (𝓝 w) ℂ) = ↑((fun y => e.symm y i) ∘ ⇑A)
    congr 1
    funext z
    simp [A]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
