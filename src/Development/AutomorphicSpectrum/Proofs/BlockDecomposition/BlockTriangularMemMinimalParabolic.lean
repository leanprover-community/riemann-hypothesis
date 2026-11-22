module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.LeviPt

section Abstract

variable {K : Type} [CommRing K] (c : K →+* K)

end Abstract

section Place

theorem exists_levi : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (A : Type) [CommRing A] [Algebra F A] [TopologicalSpace A] (p : HA A σ J) (B : Matrix (Fin r) (Fin r) (A ⊗[F] E)), B.BlockTriangular id → (matHom A σ J p).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B → ∃ m : HA A σ J, (matHom A σ J m).1 = leviMat σ J A X Y (matHom A σ J p).1 ∧ (∃ d : Fin r → A ⊗[F] E, (matHom A σ J m).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * diagonal d) ∧ (∃ d' : Fin r → A ⊗[F] E, (matHom A σ J m).1 * Y.map (inclR (F := F) A) = Y.map (inclR (F := F) A) * diagonal d') ∧ (∃ B' : Matrix (Fin r) (Fin r) (A ⊗[F] E), B'.BlockTriangular id ∧ (∀ i, B' i i = 1) ∧ (matHom A σ J (m⁻¹ * p)).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B') ∧ ∀ z : Fin n → A ⊗[F] E, ((cT (σ : E →+* E) X * J).map (inclR (F := F) A)) *ᵥ z = 0 → ∃ a : Fin r → A ⊗[F] E, ((matHom A σ J (m⁻¹ * p)).1 - 1) *ᵥ z = X.map (inclR (F := F) A) *ᵥ a := by
  intro F E _ _ _ _ _ σ n J r X Y hCM hJ hW A _ _ _ p B hBt hB
  have hc := sigR_invol A (sigma_invol hCM)
  have hJh : cT (sigR A σ) (J.map (inclR (F := F) A)) = J.map (inclR (F := F) A) := by
    rw [cT_map_inclR]; congr 1; ext i j; exact hJ.1 i j
  have hmap0 : ((0 : Matrix (Fin r) (Fin r) E)).map (inclR (F := F) A) = 0 := by simp
  have hmap1 : ((1 : Matrix (Fin r) (Fin r) E)).map (inclR (F := F) A) = 1 := by simp
  have hg : cT (sigR A σ) ((matHom A σ J p : GL (Fin n) (A ⊗[F] E)) : Matrix (Fin n) (Fin n) (A ⊗[F] E)) *
      J.map (inclR (F := F) A) * ((matHom A σ J p : GL (Fin n) (A ⊗[F] E)) : Matrix (Fin n) (Fin n) (A ⊗[F] E)) =
      J.map (inclR (F := F) A) := by
    have h : matHom A σ J p ∈ HR A σ J := (show ↥(HR A σ J) from p).2
    exact h
  have hXd : (cT (σ : E →+* E) X * J).map (inclR (F := F) A) =
      cT (sigR A σ) (X.map (inclR (F := F) A)) * J.map (inclR (F := F) A) := by
    rw [Matrix.map_mul, cT_map_inclR]
  have hYd : (cT (σ : E →+* E) Y * J).map (inclR (F := F) A) =
      cT (sigR A σ) (Y.map (inclR (F := F) A)) * J.map (inclR (F := F) A) := by
    rw [Matrix.map_mul, cT_map_inclR]
  have hxx : (cT (σ : E →+* E) X * J).map (inclR (F := F) A) * X.map (inclR (F := F) A) = 0 := by
    rw [← Matrix.map_mul, hW.xx, hmap0]
  have hyy : (cT (σ : E →+* E) Y * J).map (inclR (F := F) A) * Y.map (inclR (F := F) A) = 0 := by
    rw [← Matrix.map_mul, hW.yy, hmap0]
  have hxy : (cT (σ : E →+* E) X * J).map (inclR (F := F) A) * Y.map (inclR (F := F) A) = 1 := by
    rw [← Matrix.map_mul, hW.xy, hmap1]
  obtain ⟨u, hu, hunit, hXa, hYa, hB', hz⟩ := levi_core (sigR A σ) hc hJh hXd hYd hxx hyy hxy
    (matHom A σ J p) hg B hBt hB (leviMat σ J A X Y (matHom A σ J p).1) rfl
  have hmem : u ∈ HR A σ J := by
    show cT (sigR A σ) (u : Matrix (Fin n) (Fin n) (A ⊗[F] E)) * J.map (inclR (F := F) A) *
      (u : Matrix (Fin n) (Fin n) (A ⊗[F] E)) = J.map (inclR (F := F) A)
    rw [hu]; exact hunit
  let m : HA A σ J := (⟨u, hmem⟩ : ↥(HR A σ J))
  have hmu : matHom A σ J m = u := rfl
  have e : ((matHom A σ J (m⁻¹ * p) : GL (Fin n) (A ⊗[F] E)) : Matrix (Fin n) (Fin n) (A ⊗[F] E)) =
      ((u⁻¹ : GL (Fin n) (A ⊗[F] E)) : Matrix (Fin n) (Fin n) (A ⊗[F] E)) *
        ((matHom A σ J p : GL (Fin n) (A ⊗[F] E)) : Matrix (Fin n) (Fin n) (A ⊗[F] E)) := by
    rw [map_mul, map_inv, Units.val_mul, hmu]
  refine ⟨m, by rw [hmu]; exact hu, by rw [hmu, hu]; exact hXa, by rw [hmu, hu]; exact hYa, ?_, ?_⟩
  · obtain ⟨B', h1, h2, h3⟩ := hB'
    exact ⟨B', h1, h2, by rw [e]; exact h3⟩
  · intro z hz0
    obtain ⟨a, ha⟩ := hz z hz0
    exact ⟨a, by rw [e]; exact ha⟩

end Place

end GlobalTheory.CompanionTheory.KFin.LeviPt
