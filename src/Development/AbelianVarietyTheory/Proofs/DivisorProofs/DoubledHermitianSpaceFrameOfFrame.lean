module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section

namespace GlobalTheory.RealLift.Dbl

theorem dblM_gram {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (N : Matrix β β ℂ) (C : Matrix β (Ix R S) ℂ)
    (h : Cᵀ * N * C.map star = Jm R S) :
    (dblM C)ᵀ * Matrix.fromBlocks N 0 0 (-N) * (dblM C).map star = Jm (R + S) (S + R) := by
  have hG : ∀ a a', ∑ x, (∑ y, C y a * N y x) * (starRingEnd ℂ) (C x a') = Jm R S a a' := by
    intro a a'
    have := congrFun (congrFun h a) a'
    simpa [Matrix.mul_apply] using this
  ext j k
  rcases j with p | p <;> rcases k with q | q <;>
  · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective p
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective q
    rcases x with r | s <;> rcases y with r' | s' <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, dblM, dblCol, hG, Jm, Formalism.UG.Jpq, Matrix.one_apply,
        Finset.sum_neg_distrib, Matrix.neg_apply, Fin.ext_iff, Function.swap] <;> omega

theorem dblM_rinv {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (C : Matrix β (Ix R S) ℂ)
    (h : ∃ C' : Matrix (Ix R S) β ℂ, C * C' = 1) :
    ∃ D : Matrix (Ix (R + S) (S + R)) (β ⊕ β) ℂ, dblM C * D = 1 := by
  obtain ⟨C', hC'⟩ := h
  refine ⟨(dblM C'ᵀ)ᵀ, ?_⟩
  have hI : ∀ i i', ∑ r, C i (Sum.inl r) * C' (Sum.inl r) i' + ∑ s, C i (Sum.inr s) * C' (Sum.inr s) i' =
      (1 : Matrix β β ℂ) i i' := by
    intro i i'
    rw [← hC', Matrix.mul_apply, Fintype.sum_sum_type]
  ext i i'
  rcases i with i | i <;> rcases i' with i' | i' <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_add, dblM, dblCol, Matrix.one_apply, hI, add_comm, Function.swap]

theorem dblM_isFrame {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (N : Matrix β β ℂ) (C : Matrix β (Ix R S) ℂ)
    (h : IsFrame N C) : IsFrame (Matrix.fromBlocks N 0 0 (-N)) (dblM C) :=
  ⟨dblM_gram N C h.1, dblM_rinv C h.2⟩

theorem framed_dbl (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (α β : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (P Q R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) :
    Framed τ JA JB a b A C → Framed τ JA (dbl JB) a b A (fun w => dblM (C w)) := by
  rintro ⟨hab, hA, hC⟩
  refine ⟨hab, hA, fun w => ?_⟩
  have key : b • (dbl JB).map (piInf (τ w)) =
      Matrix.fromBlocks (b • JB.map (piInf (τ w))) 0 0 (-(b • JB.map (piInf (τ w)))) := by
    simp [dbl, Matrix.fromBlocks_map, Matrix.fromBlocks_smul, Matrix.map_neg]
  rw [key]
  exact dblM_isFrame _ _ (hC w)

end GlobalTheory.RealLift.Dbl

end
