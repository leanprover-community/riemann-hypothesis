import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsLZBasis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IntegerRingSmulMemSubmodule

namespace GlobalTheory.MaxCusp

open NumberField Complex MeasureTheory Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.TorusFourier
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r d : ℕ}

def IsIsotropicSub (G : Matrix (Fin r) (Fin r) E) (V : Submodule E (Fin r → E)) : Prop :=
  ∀ v ∈ V, ∀ w ∈ V, herm G v w = 0

def IsMaximal (X : Data E r) (u : Fin d → Fin r → E) : Prop :=
  IsIsoFam X.Gm u ∧ (∀ i, u i ∈ X.Λ) ∧
    Maximal (IsIsotropicSub X.Gm) (Submodule.span E (Set.range u))

theorem isIsotropicSub_span {G : Matrix (Fin r) (Fin r) E} {s : Set (Fin r → E)}
    (h : ∀ v ∈ s, ∀ w ∈ s, herm G v w = 0) : IsIsotropicSub G (Submodule.span E s) := by
  intro v hv w hw
  induction hv using Submodule.span_induction with
  | mem x hx =>
    induction hw using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp [herm, cc]
    | add y z _ _ hy hz =>
      have : herm G x (y + z) = herm G x y + herm G x z := by
        simp [herm, cc, mul_add, Finset.sum_add_distrib]
      rw [this, hy, hz, add_zero]
    | smul c y _ hy =>
      have : herm G x (c • y) = cc c * herm G x y := by
        simp only [herm, cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      rw [this, hy, mul_zero]
  | zero => simp [herm]
  | add x y _ _ hx hy =>
    have : herm G (x + y) w = herm G x w + herm G y w := by
      simp [herm, add_mul, Finset.sum_add_distrib]
    rw [this, hx, hy, add_zero]
  | smul c x _ hx => rw [herm_smul_left', hx, mul_zero]


theorem exists_smul_mem (X : Data E r) (v : Fin r → E) : ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v ∈ X.Λ := by
  first
  | exact @_root_.GlobalTheory.SubmoduleScalarClosure.main
  | exact _root_.GlobalTheory.SubmoduleScalarClosure.main
  | (apply _root_.GlobalTheory.SubmoduleScalarClosure.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SubmoduleScalarClosure.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SubmoduleScalarClosure.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SubmoduleScalarClosure.main ..)





section Torus

variable (X : Data E r)

def orb (u : Fin d → Fin r → E) (G : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (b : hermSub X.Ψ d) : ℂ :=
  G (Zb X u b.1 x)

def lineMap (a : X.Ψ → Fin d → ℂ) : (X.Ψ → ℝ) →ₗ[ℝ] hermSub X.Ψ d where
  toFun s := ⟨fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k), fun τ i k => by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]; ring⟩
  map_add' s t := by apply Subtype.ext; funext τ i k; simp; ring
  map_smul' c s := by apply Subtype.ext; funext τ i k; simp; ring

def nuForm (ν : X.Ψ → ℝ) : (X.Ψ → ℝ) →ₗ[ℝ] ℝ where
  toFun s := 2 * ∑ τ, ν τ * s τ
  map_add' s t := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c s := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem nuForm_apply (ν s : X.Ψ → ℝ) : nuForm X ν s = 2 * ∑ τ, ν τ * s τ := rfl

theorem nuForm_injective : Function.Injective (nuForm X) := by
  classical
  intro ν ν' h
  funext τ
  simpa [nuForm_apply, Pi.single_apply] using LinearMap.congr_fun h (Pi.single τ 1)

theorem form_comp_lineMap (χ : X.Ψ → Fin d → Fin d → ℂ) (a : X.Ψ → Fin d → ℂ) :
    form X χ ∘ₗ lineMap X a = nuForm X fun τ => (chiAt X χ a τ).re := by
  refine LinearMap.ext fun s => ?_
  rw [LinearMap.comp_apply, form_apply, nuForm_apply, pairR, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Complex.re_mul_ofReal, chiAt]
  congr 1
  simp only [lineMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring


theorem form_comp_eq_iff (χ : X.Ψ → Fin d → Fin d → ℂ) (a : X.Ψ → Fin d → ℂ) (ν : X.Ψ → ℝ) :
    form X χ ∘ₗ lineMap X a = nuForm X ν ↔ ∀ τ, (chiAt X χ a τ).re = ν τ := by
  rw [form_comp_lineMap, (nuForm_injective X).eq_iff, funext_iff]




theorem orb_add {u : Fin d → Fin r → E} (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (G : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (b l : hermSub X.Ψ d) :
    orb X u G x (b + l) = G (Zb X u l.1 (Zb X u b.1 x)) := by
  rw [orb, Zb_Zb X u hu, add_comm]; rfl







end Torus

section Main

variable (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P)
  (hχ : ∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
    Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1)

include hP hχ






end Main

end

end GlobalTheory.MaxCusp
