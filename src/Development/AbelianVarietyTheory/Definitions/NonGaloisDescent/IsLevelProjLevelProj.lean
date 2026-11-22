module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
open scoped Topology

namespace GlobalTheory.LBC

section Groups

variable {k k' : Type} [Field k] [Field k'] [Algebra k k']

def galAct (s : k' ≃ₐ[k] k') (n : ℕ) : GL (Fin n) k' →* GL (Fin n) k' :=
  GeneralLinearGroup.map s.toAlgHom.toRingHom

@[simp] theorem galAct_one (n : ℕ) : galAct (1 : k' ≃ₐ[k] k') n = MonoidHom.id _ := by
  ext g i j; rfl

theorem galAct_mul (s t : k' ≃ₐ[k] k') (n : ℕ) : galAct (s * t) n = (galAct s n).comp (galAct t n) := by
  ext g i j; rfl

def incl (k' : Type) [Field k'] [Algebra k k'] (n : ℕ) : GL (Fin n) k →* GL (Fin n) k' :=
  GeneralLinearGroup.map (algebraMap k k')

@[simp] theorem incl_apply {n : ℕ} (γ : GL (Fin n) k) (i j : Fin n) :
    (incl k' n γ : Matrix (Fin n) (Fin n) k') i j = algebraMap k k' ((γ : Matrix (Fin n) (Fin n) k) i j) := rfl

@[simp] theorem galAct_incl (s : k' ≃ₐ[k] k') {n : ℕ} (γ : GL (Fin n) k) : galAct s n (incl k' n γ) = incl k' n γ := by
  ext i j
  change s (algebraMap k k' ((γ : Matrix (Fin n) (Fin n) k) i j)) = _
  exact s.commutes _

variable (k) in
def norm (s : k' ≃ₐ[k] k') {n : ℕ} (g : GL (Fin n) k') : GL (Fin n) k' :=
  (List.ofFn fun j : Fin (Module.finrank k k') => galAct (s ^ (j : ℕ)) n g).prod

def IsStable (s : k' ≃ₐ[k] k') {n : ℕ} (K : Subgroup (GL (Fin n) k')) : Prop := K.map (galAct s n) = K

end Groups

section Traces

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

end Traces

section Unique

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V} {K : Subgroup G}
  {A : V →ₗ[ℂ] V}

end Unique

section Lift

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [Algebra k k']
  {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

variable (k) in
def IsTwInt (s : k' ≃ₐ[k] k') (P : Representation ℂ (GL (Fin n) k') W) (I : W →ₗ[ℂ] W) : Prop :=
  (∀ g, P (galAct s n g) ∘ₗ I = I ∘ₗ P g) ∧ 0 < Module.finrank k k' ∧ I ^ Module.finrank k k' = 1

theorem IsTwInt.mem_fixed {s : k' ≃ₐ[k] k'} {P : Representation ℂ (GL (Fin n) k') W} {I : W →ₗ[ℂ] W}
    (hI : IsTwInt k s P I) {K : Subgroup (GL (Fin n) k')} (hK : IsStable s K) {v : W} (hv : v ∈ fixed P K) :
    I v ∈ fixed P K := by
  intro x
  have hx : (x : GL (Fin n) k') ∈ K.map (galAct s n) := by rw [hK]; exact x.2
  obtain ⟨y, hy, e⟩ := Subgroup.mem_map.1 hx
  have h1 := LinearMap.congr_fun (hI.1 y) v
  simp only [LinearMap.comp_apply] at h1
  have h2 : P y v = v := by simpa using hv ⟨y, hy⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  rw [← e, h1, h2]

end Lift

end GlobalTheory.LBC
