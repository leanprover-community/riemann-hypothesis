import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataForm
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems

noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

section CC

variable (R K : Type) [CommRing R] [Field K] [Algebra R K]

def ccL (σ : Type) : MvPolynomial σ K →ₗ[K] K := lcoeff K 0


def ccInt (σ : Type) : Submodule R (MvPolynomial σ K) :=
  (LinearMap.range (Algebra.linearMap R K)).comap ((ccL K σ).restrictScalars R)

theorem mem_ccInt {σ : Type} (F : MvPolynomial σ K) : F ∈ ccInt R K σ ↔ ∃ a : R, algebraMap R K a = constantCoeff F :=
  Iff.rfl

theorem cc_rowAct {r n : ℕ} (g : Matrix (Fin r) (Fin r) K) (F : MvPolynomial (Fin r × Fin n) K) :
    constantCoeff (rowAct K g F) = constantCoeff F := by
  have : (constantCoeff.comp (rowAct K (n := n) g).toRingHom : MvPolynomial (Fin r × Fin n) K →+* K) = constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [rowAct]
    · intro v; simp [rowAct]
  exact congrArg (fun f : MvPolynomial (Fin r × Fin n) K →+* K => f F) this

theorem nablaLTw_le_ccInt (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    nablaLTw R K m 0 g ≤ ccInt R K _ := by
  rintro F ⟨F', hF', rfl⟩
  obtain ⟨P, -, hP⟩ := hF'
  rw [mem_ccInt]
  refine ⟨constantCoeff P, ?_⟩
  have h1 : constantCoeff (rowAct K g F') = algebraMap R K (constantCoeff P) := by
    have hP' : mapAlgHom (Algebra.ofId R K) P = rowAct K g F' := hP
    rw [← hP', mapAlgHom_apply, constantCoeff_map]
    rfl
  rw [cc_rowAct] at h1
  simp [h1]




theorem const_of_dualWeyl (r n : ℕ) (F : MvPolynomial (Fin r × Fin n) K) (hF : F ∈ dualWeyl K r n 0) :
    F = C (constantCoeff F) := by
  have hw : IsWeightedHomogeneous (colW r n) F 0 := (mem_weightedHomogeneousSubmodule K (colW r n) 0 F).1 hF.1
  have : Finsupp.NonTorsionWeight ℕ (colW r n) :=
    ⟨fun {c v} h0 => by
      have := congrFun h0 v.2
      simpa [colW] using this⟩
  ext d
  by_cases hd : d = 0
  · subst hd; simp [constantCoeff_eq]
  · rw [coeff_C, if_neg (Ne.symm hd)]
    by_contra hc
    exact hd ((Finsupp.weight_eq_zero_iff_eq_zero (colW r n)).1 (hw hc))

theorem Vsp_le {n' m : ℕ} : Vsp K (fun _ _ => 0 : Fin n' → Fin (m + 1) → ℤ) ≤ Submodule.span K {1} := by
  unfold Vsp tensorLat
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  have h1 : ∀ s, F s = C (constantCoeff (F s)) := fun s => by
    have h2 := hF s
    simp only [lamAt_zero] at h2
    rw [if_pos (show Antitone (0 : Fin (m + 1) → ℤ) from fun _ _ _ => le_rfl)] at h2
    have h0 : nuOf (0 : Fin (m + 1) → ℤ) = 0 := by funext t; simp [nuOf]
    rw [h0] at h2
    exact const_of_dualWeyl K _ _ _ h2
  refine Submodule.mem_span_singleton.2 ⟨∏ s, constantCoeff (F s), ?_⟩
  have : ∀ s, blockEmb K s (F s) = C (constantCoeff (F s)) := fun s => by
    conv_lhs => rw [h1 s]
    simp [blockEmb]
  simp only [this]
  rw [smul_eq_C_mul, mul_one, map_prod]


theorem one_mem_Vsp {n' m : ℕ} : (1 : MvPolynomial _ K) ∈ Vsp K (fun _ _ => 0 : Fin n' → Fin (m + 1) → ℤ) := by
  unfold Vsp
  refine one_mem_tensorLat K K _ fun s => ?_
  rw [lamAt_zero, if_pos (show Antitone (0 : Fin (m + 1) → ℤ) from fun _ _ _ => le_rfl)]
  have h0 : nuOf (0 : Fin (m + 1) → ℤ) = 0 := by funext t; simp [nuOf]
  rw [h0]
  exact one_mem_dualWeyl K _ _


end CC

end Formalism.MainNotions.G.Inhab

end
