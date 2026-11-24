module

public import ReciprocityTheory.DualLattices.LenIdBStatement
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.DualLattices.UpSmith

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

lemma hasLen_of_equiv {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) {x : NNReal} (h : HasLen v R N x) : HasLen v R M x := by
  obtain ⟨k, c, ⟨f⟩, hx⟩ := h
  exact ⟨k, c, ⟨e.trans f⟩, hx⟩

theorem hasLen_coker_det' {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R) :
    HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)) := by
  set e := Fintype.equivFin κ
  set X' := X.submatrix e.symm e.symm
  have hdet : X'.det = X.det := Matrix.det_submatrix_equiv_self e.symm X
  let Φ : (κ → R) ≃ₗ[R] (Fin (Fintype.card κ) → R) := LinearEquiv.funCongrLeft R R e.symm
  have hrange : (LinearMap.range X.mulVecLin).map (Φ : (κ → R) →ₗ[R] (Fin (Fintype.card κ) → R)) =
      LinearMap.range X'.mulVecLin := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      refine ⟨y ∘ e.symm, ?_⟩
      funext i
      show (X' *ᵥ (y ∘ e.symm)) i = (X *ᵥ y) (e.symm i)
      simp only [X', Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Function.comp_apply]
      exact Equiv.sum_comp e.symm (fun k => X (e.symm i) k * y k)
    · rintro ⟨y, rfl⟩
      refine ⟨X *ᵥ (y ∘ e), ⟨y ∘ e, rfl⟩, ?_⟩
      funext i
      simp only [Matrix.mulVecLin_apply, X', Matrix.submatrix_mulVec_equiv, Φ,
        Function.comp_apply]
      simp
  have h := Smith.hasLen_coker_det hv X'
  rw [hdet] at h
  exact hasLen_of_equiv (Submodule.Quotient.equiv _ _ Φ hrange) h

theorem lenId_of_B (hB : LenIdBStatement) : LenIdStatement :=
  lenId_of (fun C _ v R _ _ hv => hasLen_coker_det' v R hv) hB

end ReciprocityTheory.PGsh.Up
