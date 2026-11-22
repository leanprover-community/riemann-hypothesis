module

public import Mathlib

@[expose] public section

namespace GlobalTheory

open scoped BigOperators

section JetWedge

variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  {D : ℕ}

theorem alternating_map_sum_smul_eq_det_smul {n : ℕ} (ω : M [⋀^Fin n]→ₗ[A] N)
    (a : Matrix (Fin n) (Fin n) A) (w : Fin n → M) :
    ω (fun i => ∑ k, a i k • w k) = a.det • ω w := by
  classical
  let φ : (Fin n → A) →ₗ[A] M := Fintype.linearCombination A w
  have key : ω.compLinearMap φ
      = ((LinearMap.toSpanSingleton A N (ω w)).compAlternatingMap Matrix.detRowAlternating) := by
    refine Module.Basis.ext_alternating (Pi.basisFun A (Fin n)) fun v hv => ?_
    have hb : Function.Bijective v := Finite.injective_iff_bijective.mp hv
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective v hb
    have e1 : (fun i => (Pi.basisFun A (Fin n)) (v i)) = (Pi.basisFun A (Fin n)) ∘ σ := rfl
    rw [e1, AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    have e2 : (Matrix.detRowAlternating : (Fin n → A) [⋀^Fin n]→ₗ[A] A) (Pi.basisFun A (Fin n))
        = 1 := by
      rw [← Matrix.det_one (n := Fin n)]
      change Matrix.det _ = _
      congr 1
      ext i j
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    simp only [LinearMap.compAlternatingMap_apply, e2, LinearMap.toSpanSingleton_apply, one_smul,
      AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    simp [φ]
  have := congrArg (fun F : (Fin n → A) [⋀^Fin n]→ₗ[A] N => F a) key
  have e3 : (fun i => ∑ k, a i k • w k) = fun i => φ (a i) := by
    funext i
    exact (Fintype.linearCombination_apply A w (a i)).symm
  rw [e3]
  exact this

theorem alternating_sub_mem_smul_top (ω : M [⋀^Fin D]→ₗ[A] N) (I : Ideal A) (v w : Fin D → M)
    (hvw : ∀ k, v k - w k ∈ I • (⊤ : Submodule A M)) :
    ω v - ω w ∈ I • (⊤ : Submodule A N) := by
  classical
  have key : ∀ s : Finset (Fin D), ω (s.piecewise v w) - ω w ∈ I • (⊤ : Submodule A N) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      have h1 : s.piecewise v w = Function.update (s.piecewise v w) i (w i) := by
        rw [eq_comm, Function.update_eq_self_iff, Finset.piecewise_eq_of_notMem _ _ _ hi]
      have h2 : ω ((insert i s).piecewise v w) - ω (s.piecewise v w)
          = ω.toMultilinearMap.toLinearMap (s.piecewise v w) i (v i - w i) := by
        rw [map_sub, Finset.piecewise_insert]
        conv_lhs => rw [h1]
        simp
      have h3 : ω ((insert i s).piecewise v w) - ω (s.piecewise v w)
          ∈ I • (⊤ : Submodule A N) := by
        rw [h2]
        have := Submodule.mem_map_of_mem
          (f := ω.toMultilinearMap.toLinearMap (s.piecewise v w) i) (hvw i)
        rw [Submodule.map_smul''] at this
        exact Submodule.smul_mono le_rfl le_top this
      simpa using add_mem h3 ih
  simpa using key Finset.univ

end JetWedge

section JacForm

variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [AddCommGroup N] [Module A N] {D : ℕ}

variable (d : Derivation R A M) (ω : M [⋀^Fin D]→ₗ[A] N)

theorem form_d_mul_sub_mem (I : Ideal A) (h : A) (g : Fin D → A) (hg : ∀ k, g k ∈ I) :
    ω (fun k => d (h * g k)) - h ^ D • ω (fun k => d (g k)) ∈ I • (⊤ : Submodule A N) := by
  have : h ^ D • ω (fun k => d (g k)) = ω (fun k => h • d (g k)) := by
    rw [ω.map_smul_univ (fun _ => h)]
    simp
  rw [this]
  refine alternating_sub_mem_smul_top ω I _ _ fun k => ?_
  rw [Derivation.leibniz, add_sub_cancel_left]
  exact Submodule.smul_mem_smul (hg k) Submodule.mem_top

variable [Module R N] [IsScalarTower R A N] [IsScalarTower R A M]

end JacForm

section RestrictScalars

variable (A : Type*) {B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] {D : ℕ}

def altRestrictScalars (ω : M [⋀^Fin D]→ₗ[B] N) : M [⋀^Fin D]→ₗ[A] N where
  toMultilinearMap := ω.toMultilinearMap.restrictScalars A
  map_eq_zero_of_eq' v _ _ hv hij := ω.map_eq_zero_of_eq v hv hij

variable {A} {L : Type*} [AddCommGroup L] [Module A L]

variable (B D) in
noncomputable def exteriorPowerMapOver (φ : L →ₗ[A] M) : (⋀[A]^D L) →ₗ[A] (⋀[B]^D M) :=
  exteriorPower.alternatingMapLinearEquiv
    ((altRestrictScalars A (exteriorPower.ιMulti B D (M := M))).compLinearMap φ)

@[simp] theorem exteriorPowerMapOver_ιMulti (φ : L →ₗ[A] M) (v : Fin D → L) :
    exteriorPowerMapOver B D φ (exteriorPower.ιMulti A D v)
      = exteriorPower.ιMulti B D (fun k => φ (v k)) := by
  simp only [exteriorPowerMapOver,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  rfl

end RestrictScalars

section Jac

variable (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A] {D : ℕ}

open KaehlerDifferential

noncomputable def dWedge (g : Fin D → A) : ⋀[A]^D Ω[A⁄R] :=
  exteriorPower.ιMulti A D (fun k => KaehlerDifferential.D R A (g k))

theorem dWedge_mul_sub_mem (I : Ideal A) (h : A) (g : Fin D → A) (hg : ∀ k, g k ∈ I) :
    dWedge R (fun k => h * g k) - h ^ D • dWedge R g ∈ I • (⊤ : Submodule A (⋀[A]^D Ω[A⁄R])) :=
  form_d_mul_sub_mem _ _ I h g hg

variable {R}

end Jac

end GlobalTheory
