import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormsBaseChange

section
open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mapDR_span_and_linearIndependent_baseChange : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L], (∀ y : DR k L, ∃ (m : ℕ) (b : Fin m → L) (ω : Fin m → DR k K), y = ∑ j, b j • mapDR k K L (ω j)) ∧ ∀ (m : ℕ) (b : Fin m → L) (ω : Fin m → DR k K), LinearIndependent K b → ∑ j, b j • mapDR k K L (ω j) = 0 → ∀ j, ω j = 0 := by
  first | (exact @GlobalTheory.W1.Base.forms_baseChange) | (exact GlobalTheory.W1.Base.forms_baseChange) | (intros; apply GlobalTheory.W1.Base.forms_baseChange  <;> assumption)
end

section
open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

theorem smul_smul_mapDR (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] (c : K) (x : L) (ω : DR k K) :
    (c • x) • mapDR k K L ω = x • mapDR k K L (c • ω) := by
  rw [map_smul, smul_assoc, smul_comm]

theorem trDR_isTrDR_unique : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L],
    IsTrDR k K L (trDR k K L) ∧ ∀ T, IsTrDR k K L T → T = trDR k K L := by
  intro k K L _ _ _ _ _ _ _ _ _
  obtain ⟨hspan, hind⟩ := GlobalTheory.T.mapDR_span_and_linearIndependent_baseChange k K L
  have uniq : ∀ T T' : DR k L →ₗ[k] DR k K, IsTrDR k K L T → IsTrDR k K L T' → T = T' := by
    intro T T' hT hT'
    refine LinearMap.ext fun y => ?_
    obtain ⟨m, b, ω, rfl⟩ := hspan y
    simp only [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hT, hT']
  let e := Module.finBasis K L
  let n := Module.finrank K L
  let φ : (Fin n → DR k K) →ₗ[k] DR k L :=
    { toFun := fun ω => ∑ j, e j • mapDR k K L (ω j)
      map_add' := fun a b => by simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← algebraMap_smul K c (a j), map_smul, algebraMap_smul, smul_comm] }
  have hφ : Function.Bijective φ := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro ω hω
      funext j
      exact hind n e ω e.linearIndependent hω j
    · intro y
      obtain ⟨m, b, ω, rfl⟩ := hspan y
      refine ⟨fun j => ∑ i, e.repr (b i) j • ω i, ?_⟩
      change ∑ j, e j • mapDR k K L (∑ i, e.repr (b i) j • ω i) = _
      simp only [map_sum, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [← smul_smul_mapDR]
      rw [← Finset.sum_smul, e.sum_repr]
  let ψ := (LinearEquiv.ofBijective φ hφ).symm
  let g : (Fin n → DR k K) →ₗ[k] DR k K :=
    { toFun := fun ω => ∑ j, Algebra.trace K L (e j) • ω j
      map_add' := fun a b => by simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_comm] }
  have ex : IsTrDR k K L (g ∘ₗ ψ.toLinearMap) := by
    intro b ω
    have hb : b • mapDR k K L ω = φ (fun j => e.repr b j • ω) := by
      change _ = ∑ j, e j • mapDR k K L (e.repr b j • ω)
      simp only [← smul_smul_mapDR]
      rw [← Finset.sum_smul, e.sum_repr]
    rw [LinearMap.comp_apply, hb]
    have : ψ (φ (fun j => e.repr b j • ω)) = fun j => e.repr b j • ω :=
      (LinearEquiv.ofBijective φ hφ).symm_apply_apply _
    rw [LinearEquiv.coe_coe, this]
    change ∑ j, Algebra.trace K L (e j) • e.repr b j • ω = _
    simp only [smul_smul, ← Finset.sum_smul]
    congr 1
    conv_rhs => rw [← e.sum_repr b]
    simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  have htr : IsTrDR k K L (trDR k K L) := by
    have h : ∃ T, IsTrDR k K L T := ⟨_, ex⟩
    unfold trDR
    rw [dif_pos h]
    exact h.choose_spec
  exact ⟨htr, fun T hT => uniq T _ hT htr⟩

end GlobalTheory.W1
end

section
open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamFormTrace_exists_unique : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L], IsTrDR k K L (trDR k K L) ∧ ∀ T, IsTrDR k K L T → T = trDR k K L := by
  first | (exact @GlobalTheory.W1.trDR_isTrDR_unique) | (exact GlobalTheory.W1.trDR_isTrDR_unique) | (intros; apply GlobalTheory.W1.trDR_isTrDR_unique <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

theorem trDR_projection : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L], ∀ (α : DR k K) (β : DR k L),
    trDR k K L (mapDR k K L α * β) = α * trDR k K L β ∧ trDR k K L (β * mapDR k K L α) = trDR k K L β * α := by
  intro k K L _ _ _ _ _ _ _ _ _ α β
  obtain ⟨m, b, ω, rfl⟩ := (GlobalTheory.T.mapDR_span_and_linearIndependent_baseChange k K L).1 β
  have hT := (GlobalTheory.T.deRhamFormTrace_exists_unique k K L).1
  constructor
  · rw [Finset.mul_sum, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, ← map_mul, hT, hT, mul_smul_comm]
  · rw [Finset.sum_mul, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, ← map_mul, hT, hT, smul_mul_assoc]

end GlobalTheory.W1
end
end

section
open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamFormTrace_projection_formula : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L], ∀ (α : DR k K) (β : DR k L), trDR k K L (mapDR k K L α * β) = α * trDR k K L β ∧ trDR k K L (β * mapDR k K L α) = trDR k K L β * α := by
  first | (exact @GlobalTheory.W1.trDR_projection) | (exact GlobalTheory.W1.trDR_projection) | (intros; apply GlobalTheory.W1.trDR_projection <;> assumption)
end
