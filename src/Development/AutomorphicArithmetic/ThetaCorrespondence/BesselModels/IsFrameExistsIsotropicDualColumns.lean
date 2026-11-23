module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame

@[expose] public section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.DualCols


open scoped ComplexOrder in
theorem exists_right_inv {n r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {e : Matrix (Fin n) (Fin r) ℂ}
    (hJ : IsUnit J) (he : LinearIndependent ℂ eᵀ) : ∃ f : Matrix (Fin n) (Fin r) ℂ, eᴴ * J * f = 1 := by
  have hr : eᵀ.rank = r := by simpa using LinearIndependent.rank_matrix (M := eᵀ) he
  have hr2 : (eᴴ * J).rank = r := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det J).1 hJ),
      Matrix.rank_conjTranspose, ← Matrix.rank_transpose, hr]
  have hs : Function.Surjective (eᴴ * J).mulVec := by
    have h : LinearMap.range (eᴴ * J).mulVecLin = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by
        first
          | rw [Matrix.finrank_range_mulVecLin, hr2, Module.finrank_fin_fun]
          | simpa [Matrix.finrank_range_mulVecLin] using hr2)
    exact LinearMap.range_eq_top.1 h
  exact Matrix.mulVec_surjective_iff_exists_right_inverse.1 hs

theorem adj {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) {α β : Type} [Fintype α] [Fintype β]
    (X : Matrix (Fin n) α ℂ) (Y : Matrix (Fin n) β ℂ) : (Xᴴ * J * Y)ᴴ = Yᴴ * J * X := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]

theorem core {n m r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {J₀ : Matrix (Fin m) (Fin m) ℂ}
    {F : Matrix (Fin n) (Fin m) ℂ} {e f' : Matrix (Fin n) (Fin r) ℂ} {Z : Matrix (Fin n) Unit ℂ} {c : ℂ}
    (hJ : Jᴴ = J) (hd : IsUnit J₀.det) (hc : c ≠ 0) (hFF : Fᴴ * J * F = J₀) (hFe : Fᴴ * J * e = 0)
    (hFZ : Fᴴ * J * Z = 0) (hee : eᴴ * J * e = 0) (heZ : eᴴ * J * Z = 0) (hZZ : Zᴴ * J * Z = c • 1)
    (hf' : eᴴ * J * f' = 1) :
    ∃ f : Matrix (Fin n) (Fin r) ℂ, eᴴ * J * f = 1 ∧ fᴴ * J * f = 0 ∧ Fᴴ * J * f = 0 ∧ Zᴴ * J * f = 0 := by
  have heF : eᴴ * J * F = 0 := by rw [← adj hJ F e, hFe, conjTranspose_zero]
  have hZF : Zᴴ * J * F = 0 := by rw [← adj hJ F Z, hFZ, conjTranspose_zero]
  have hZe : Zᴴ * J * e = 0 := by rw [← adj hJ e Z, heZ, conjTranspose_zero]
  obtain ⟨P, hP⟩ : ∃ P, J₀ * P = Fᴴ * J * f' :=
    ⟨J₀⁻¹ * (Fᴴ * J * f'), by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Zᴴ * J * Z * Q = Zᴴ * J * f' :=
    ⟨c⁻¹ • (Zᴴ * J * f'), by rw [hZZ, Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  obtain ⟨f₂, h₂⟩ : ∃ f₂, f₂ = f' - F * P - Z * Q := ⟨_, rfl⟩
  have hF₂ : Fᴴ * J * f₂ = 0 := by
    rw [h₂, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc _ F, ← Matrix.mul_assoc _ Z, hFF, hFZ, hP,
      Matrix.zero_mul, sub_self, sub_zero]
  have hZ₂ : Zᴴ * J * f₂ = 0 := by
    rw [h₂, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc _ F, ← Matrix.mul_assoc _ Z, hZF, hQ,
      Matrix.zero_mul, sub_zero, sub_self]
  have he₂ : eᴴ * J * f₂ = 1 := by
    rw [h₂, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc _ F, ← Matrix.mul_assoc _ Z, heF, heZ, hf',
      Matrix.zero_mul, Matrix.zero_mul, sub_zero, sub_zero]
  have he₂' : f₂ᴴ * J * e = 1 := by rw [← adj hJ e f₂, he₂, conjTranspose_one]
  obtain ⟨H, hH, hHH⟩ : ∃ H : Matrix (Fin r) (Fin r) ℂ, Hᴴ = H ∧ H + H = f₂ᴴ * J * f₂ := by
    refine ⟨(1 / 2 : ℝ) • (f₂ᴴ * J * f₂), ?_, ?_⟩
    · rw [conjTranspose_smul, adj hJ f₂ f₂]; simp
    · rw [← add_smul]; norm_num
  have hfH : (f₂ - e * H)ᴴ = f₂ᴴ - H * eᴴ := by
    rw [conjTranspose_sub, conjTranspose_mul, hH]
  refine ⟨f₂ - e * H, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_sub, ← Matrix.mul_assoc _ e, hee, he₂, Matrix.zero_mul, sub_zero]
  · have h1 : (f₂ᴴ - H * eᴴ) * J * f₂ = f₂ᴴ * J * f₂ - H := by
      rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc H, Matrix.mul_assoc H, he₂,
        Matrix.mul_one]
    have h2 : (f₂ᴴ - H * eᴴ) * J * e = 1 := by
      rw [Matrix.sub_mul, Matrix.sub_mul, he₂', Matrix.mul_assoc H, Matrix.mul_assoc H, hee,
        Matrix.mul_zero, sub_zero]
    rw [hfH, Matrix.mul_sub, ← Matrix.mul_assoc _ e, h1, h2, Matrix.one_mul, ← hHH]
    abel
  · rw [Matrix.mul_sub, ← Matrix.mul_assoc _ e, hFe, hF₂, Matrix.zero_mul, sub_zero]
  · rw [Matrix.mul_sub, ← Matrix.mul_assoc _ e, hZe, hZ₂, Matrix.zero_mul, sub_zero]

theorem exists_dual_cols {n m r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {J₀ : Matrix (Fin m) (Fin m) ℂ}
    {F : Matrix (Fin n) (Fin m) ℂ} {e : Matrix (Fin n) (Fin r) ℂ} {z : Fin n → ℂ} (hf : IsFrame J J₀ F e z) :
    ∃ f : Matrix (Fin n) (Fin r) ℂ, eᴴ * J * f = 1 ∧ fᴴ * J * f = 0 ∧ Fᴴ * J * f = 0 ∧ (fᴴ * J) *ᵥ z = 0 := by
  obtain ⟨f', hf'⟩ := exists_right_inv hf.unit hf.e_indep
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin n) Unit ℂ, Z = Matrix.of fun i _ => z i := ⟨_, rfl⟩
  have hcol : ∀ {a : Type} (M : Matrix a (Fin n) ℂ) (i : a) (u : Unit), (M * Z) i u = (M *ᵥ z) i := by
    intro a M i u
    subst hZ
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hFZ : Fᴴ * J * Z = 0 := by
    ext i u
    rw [hcol, hf.z_perpF]
    rfl
  have heZ : eᴴ * J * Z = 0 := by
    ext i u
    rw [hcol, hf.z_perpE]
    rfl
  have hZZ : Zᴴ * J * Z = (Formalism.QuantumDeterminants.herm J z z) • (1 : Matrix Unit Unit ℂ) := by
    ext u v
    subst hZ
    simp [Formalism.QuantumDeterminants.herm, Matrix.mul_apply, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  obtain ⟨f, h1, h2, h3, h4⟩ := core hf.herm ((Matrix.isUnit_iff_isUnit_det J₀).1 hf.unit₀) hf.z_ne hf.gram
    hf.e_perp hFZ hf.e_iso heZ hZZ hf'
  refine ⟨f, h1, h2, h3, ?_⟩
  have h5 : fᴴ * J * Z = 0 := by rw [← adj hf.herm Z f, h4, conjTranspose_zero]
  funext i
  rw [← hcol _ i (), h5]
  rfl

end UpperTheory.Lit.Bur.DualCols

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

theorem _root_.UpperTheory.Lit.Bur.isFrame_exists_isotropic_dual_columns : ∀ {n m r : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {J₀ : Matrix (Fin m) (Fin m) ℂ} {F : Matrix (Fin n) (Fin m) ℂ} {e : Matrix (Fin n) (Fin r) ℂ} {z : Fin n → ℂ} (hf : IsFrame J J₀ F e z), ∃ f : Matrix (Fin n) (Fin r) ℂ, eᴴ * J * f = 1 ∧ fᴴ * J * f = 0 ∧ Fᴴ * J * f = 0 ∧ (fᴴ * J) *ᵥ z = 0 := by
  exact @UpperTheory.Lit.Bur.DualCols.exists_dual_cols
