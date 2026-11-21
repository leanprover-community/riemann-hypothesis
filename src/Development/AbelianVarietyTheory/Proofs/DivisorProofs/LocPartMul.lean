import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne

section
noncomputable section

open Matrix
open scoped Classical

namespace GlobalTheory.OrbDesc

section Blocks

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ}

def side (e : ι ≃ Fin a ⊕ Fin b) (i : ι) : Bool := (e i).isRight

def uMat (e : ι ≃ Fin a ⊕ Fin b) (X : Fin a → Fin b → K) : Matrix ι ι K :=
  Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)

theorem uMat_add (e : ι ≃ Fin a ⊕ Fin b) (X Y : Fin a → Fin b → K) :
    uMat e (X + Y) = uMat e X * uMat e Y := by
  simp only [uMat, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  simp [Matrix.of_add_of, add_comm]

theorem uMat_zero (e : ι ≃ Fin a ⊕ Fin b) : uMat e (0 : Fin a → Fin b → K) = 1 := by
  simp [uMat]

def uGL (e : ι ≃ Fin a ⊕ Fin b) (X : Fin a → Fin b → K) : GL ι K :=
  ⟨uMat e X, uMat e (-X), by rw [← uMat_add, add_neg_cancel, uMat_zero],
    by rw [← uMat_add, neg_add_cancel, uMat_zero]⟩

def uHom (e : ι ≃ Fin a ⊕ Fin b) : Multiplicative (Fin a → Fin b → K) →* GL ι K where
  toFun X := uGL e X.toAdd
  map_one' := Units.ext (uMat_zero e)
  map_mul' X Y := Units.ext (uMat_add e X.toAdd Y.toAdd)

def blockPar (e : ι ≃ Fin a ⊕ Fin b) : Subgroup (GL ι K) where
  carrier := {g | (g : Matrix ι ι K).BlockTriangular (side e)}
  one_mem' := by simpa using Matrix.blockTriangular_one
  mul_mem' := by
    intro g h hg hh
    simpa using Matrix.BlockTriangular.mul hg hh
  inv_mem' := by
    intro g hg
    have : Invertible (g : Matrix ι ι K) := Units.invertible g
    simp only [Set.mem_setOf_eq, Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

def blockParOpp (e : ι ≃ Fin a ⊕ Fin b) : Subgroup (GL ι K) where
  carrier := {g | (g : Matrix ι ι K).BlockTriangular (fun i => OrderDual.toDual (side e i))}
  one_mem' := by simpa using Matrix.blockTriangular_one
  mul_mem' := by
    intro g h hg hh
    simpa using Matrix.BlockTriangular.mul hg hh
  inv_mem' := by
    intro g hg
    have : Invertible (g : Matrix ι ι K) := Units.invertible g
    simp only [Set.mem_setOf_eq, Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

def blockLevi (e : ι ≃ Fin a ⊕ Fin b) : Subgroup (GL ι K) := blockPar e ⊓ blockParOpp e

def blockUni (e : ι ≃ Fin a ⊕ Fin b) : Subgroup (GL ι K) := (uHom e).range

end Blocks

section Sums

variable {H : Type} [Group H]

def wt (T L U : Subgroup H) (Ψ : H → ℂ) (x : H) : ℂ :=
  (GlobalTheory.LKLoc.volRat U (GlobalTheory.LKLoc.locPart T L x) : ℂ) * Ψ x

def dsum (T L U : Subgroup H) (Ψ : H → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (T : Set H) (L : Set H), wt T L U Ψ (Quotient.out q)

end Sums

end GlobalTheory.OrbDesc
end
end

section
noncomputable section

namespace GlobalTheory.OrbDesc

variable {H : Type} [Group H]

theorem locPart_mul {T L : Subgroup H} (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) {t x l : H} (ht : t ∈ T)
    (hl : l ∈ L) : GlobalTheory.LKLoc.locPart T L (t * x * l) = GlobalTheory.LKLoc.locPart T L x := by
  unfold GlobalTheory.LKLoc.locPart
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hg, k, hk, rfl⟩
    refine ⟨hg, l * k * l⁻¹, L.mul_mem (L.mul_mem hl hk) (L.inv_mem hl), ?_⟩
    calc x * (l * k * l⁻¹) * x⁻¹ = t⁻¹ * ((t * x * l * k * (t * x * l)⁻¹) * t) := by group
      _ = t⁻¹ * (t * (t * x * l * k * (t * x * l)⁻¹)) := by rw [hT _ hg t ht]
      _ = t * x * l * k * (t * x * l)⁻¹ := by group
  · rintro ⟨hg, k, hk, rfl⟩
    refine ⟨hg, l⁻¹ * k * l, L.mul_mem (L.mul_mem (L.inv_mem hl) hk) hl, ?_⟩
    have := hT _ hg t ht
    calc t * x * l * (l⁻¹ * k * l) * (t * x * l)⁻¹ = t * (x * k * x⁻¹) * t⁻¹ := by group
      _ = (x * k * x⁻¹) * t * t⁻¹ := by rw [← this]
      _ = x * k * x⁻¹ := by group

theorem wt_mul {T L : Subgroup H} (U : Subgroup H) {Ψ : H → ℂ} (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    (hΨl : ∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) (hΨr : ∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) {t x l : H} (ht : t ∈ T)
    (hl : l ∈ L) : wt T L U Ψ (t * x * l) = wt T L U Ψ x := by
  unfold wt
  rw [locPart_mul hT ht hl, hΨr l hl, hΨl t ht]

theorem wt_out {T L : Subgroup H} (U : Subgroup H) {Ψ : H → ℂ} (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    (hΨl : ∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) (hΨr : ∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) (x : H) :
    wt T L U Ψ (Quotient.out (DoubleCoset.mk T L x)) = wt T L U Ψ x := by
  obtain ⟨t, ht, l, hl, h⟩ := (DoubleCoset.eq T L _ _).1 (DoubleCoset.out_eq' T L (DoubleCoset.mk T L x))
  exact (wt_mul U hT hΨl hΨr ht hl).symm.trans (congrArg _ h.symm)

end GlobalTheory.OrbDesc
end
end
