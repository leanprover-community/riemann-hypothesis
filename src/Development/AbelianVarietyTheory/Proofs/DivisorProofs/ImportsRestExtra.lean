module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace GlobalTheory.GramDet

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  subst hn
  set A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm with hA'
  have key : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]
    ext i j
    simp [hA', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
  intro h0
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁] at hd
  simp [Matrix.det_neg] at hd
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) hd.symm

theorem det_ne_zero_of_map {n : ℕ} {K : Type} [Field K] (φ : K →+* ℂ) {J : Matrix (Fin n) (Fin n) K}
    (h : (J.map φ).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem gram_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    G.V'.J.det ≠ 0 ∧ G.W.J.det ≠ 0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine ⟨det_ne_zero_of_map (B.emb w).1 (det_ne_zero_of_hasSig (hT.geo.hV'.sig w)), ?_⟩
  refine det_ne_zero_of_map (B.emb w).1 ?_
  have h := det_ne_zero_of_hasSig (hT.geo.hW.sig w)
  rw [Matrix.det_smul] at h
  intro h0
  exact h (by rw [h0, mul_zero])

end GlobalTheory.GramDet
