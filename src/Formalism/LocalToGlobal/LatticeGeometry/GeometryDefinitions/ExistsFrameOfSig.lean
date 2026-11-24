module

public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.ClsSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

noncomputable section

open Module Matrix NumberField IsDedekindDomain Formalism.UG Formalism.BasicNotions Formalism.HN
open scoped TensorProduct

namespace Formalism.L2.Geo.Def.G1

section Frames

theorem exists_frame_of_sig {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (p : ℕ)
    (h : HasSignature M p 0) : ∃ Y : Matrix ι ι ℂ, IsUnit Y.det ∧ (Y⁻¹).conjTranspose * Y⁻¹ = M := by
  obtain ⟨e, P, hP⟩ := h
  set A : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ := (P : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ) with hA
  have hJ : Jpq p 0 = 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [Jpq, Matrix.one_apply]
    · exact j.elim0
    · exact i.elim0
    · exact i.elim0
  have hcT : cT (starRingEnd ℂ) A = A.conjTranspose := by
    ext i j; simp [cT, Matrix.conjTranspose_apply]
  rw [hJ, hcT] at hP
  have hdetA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
  have hM' : M.reindex e e = (A⁻¹).conjTranspose * A⁻¹ := by
    have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdetA
    calc M.reindex e e = (A * A⁻¹).conjTranspose * M.reindex e e * (A * A⁻¹) := by
          rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      _ = (A⁻¹).conjTranspose * (A.conjTranspose * M.reindex e e * A) * A⁻¹ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (A⁻¹).conjTranspose * A⁻¹ := by rw [hP, Matrix.mul_one]
  refine ⟨A.submatrix e e, ?_, ?_⟩
  · rw [Matrix.det_submatrix_equiv_self]; exact hdetA
  · rw [Matrix.inv_submatrix_equiv, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, ← hM']
    ext i j
    simp

theorem frameOf_spec {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (h : ∃ Y : Matrix ι ι ℂ, IsUnit Y.det ∧ (Y⁻¹).conjTranspose * Y⁻¹ = M) :
    IsUnit (frameOf M).det ∧ ((frameOf M)⁻¹).conjTranspose * (frameOf M)⁻¹ = M := by
  rw [frameOf, dite_eq_left h]
  exact h.choose_spec

end Frames

section Space

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

open Formalism.L2.Herm

theorem crdLat_mem (S : HSpace E) (L : Submodule (𝓞 E) S.V) (x : S.V) : crd S x ∈ crdLat S L ↔ x ∈ L := by
  simp only [crdLat, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [(crd S).injective hyx] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem crdLat_lattice (S : HSpace E) (L : Submodule (𝓞 E) S.V) (hL : Submodule.IsFullLattice E L) :
    Submodule.IsLattice E (crdLat S L) := by
  exact Submodule.IsLattice.of_fg E (hL.fg.map _)

end Space


variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E]


end Formalism.L2.Geo.Def.G1
