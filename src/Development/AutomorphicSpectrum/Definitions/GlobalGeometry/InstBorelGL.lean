module

public import Mathlib

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL

section Base

variable {F : Type} [Field F]

def IsInt {n : ℕ} (R : Subring F) (Z : Matrix (Fin n) (Fin n) F) : Prop := ∀ a b, Z a b ∈ R

theorem isInt_mul' (O : Subring F) {a : ℕ} {x y : Matrix (Fin a) (Fin a) F} (hx : IsInt O x)
    (hy : IsInt O y) : IsInt O (x * y) := by
  intro a b
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => O.mul_mem (hx a k) (hy k b)

def GLint (O : Subring F) (a : ℕ) : Subgroup (GL (Fin a) F) where
  carrier := {g | IsInt O (g : Matrix (Fin a) (Fin a) F) ∧
    IsInt O ((g⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)}
  one_mem' := by
    constructor <;> intro i j <;> by_cases h : i = j <;> simp [h, O.one_mem, O.zero_mem]
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by simpa using isInt_mul' O hx hy, ?_⟩
    simpa [_root_.mul_inv_rev] using isInt_mul' O hy' hx'
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    exact ⟨by simpa using hx', by simpa using hx⟩

instance instMeasGL {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n : ℕ) :
    MeasurableSpace (GL (Fin n) K) := borel _
instance instBorelGL {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n : ℕ) :
    BorelSpace (GL (Fin n) K) := ⟨rfl⟩

end Base

section Local

variable {F : Type} [Field F]

variable (O : Subring F) (ϖ : F) (nrm : AbsoluteValue F ℝ)

def IsSphFn {c : ℕ} (χ : Fin c → F → ℂ) (φ : GL (Fin c) F → ℂ) : Prop :=
  ∀ b : GL (Fin c) F, (b : Matrix (Fin c) (Fin c) F).BlockTriangular id → ∀ k ∈ GLint O c,
    φ (b * k) = ∏ i : Fin c, χ i ((b : Matrix (Fin c) (Fin c) F) i i) *
      ((nrm ((b : Matrix (Fin c) (Fin c) F) i i) ^ (((c : ℝ) - 1) / 2 - (i : ℕ)) : ℝ) : ℂ)

variable [TopologicalSpace F] [IsTopologicalRing F]

end Local

section More

variable {F : Type} [Field F]

def Mint (O : Subring F) (c : ℕ) : Set (GL (Fin c) F) := {g | IsInt O (g : Matrix (Fin c) (Fin c) F)}

def UnrChar (nrm : AbsoluteValue F ℝ) (q : ℕ) {c : ℕ} (χ : Fin c → F → ℂ) (α : Fin c → ℂ) : Prop :=
  (∀ i, α i ≠ 0) ∧ ∀ i (x : F) (e : ℤ), nrm x = (q : ℝ) ^ (-e) → χ i x = α i ^ e

structure LF [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (O : Subring F) (ϖ : F) (nrm : AbsoluteValue F ℝ) (q : ℕ) : Prop where
  O_eq : O = 𝒪[F]
  ne : ϖ ≠ 0
  lt_one : ∀ x : F, ValuativeRel.valuation F x < 1 ↔ ∃ o ∈ O, x = ϖ * o
  card : q = Nat.card 𝓀[F]
  nrm_unit : ∀ x : F, ValuativeRel.valuation F x = 1 → nrm x = 1
  nrm_pi : nrm ϖ = (q : ℝ)⁻¹

end More

end GlobalTheory.CompanionTheory.QL
