import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveEigenvectorOfSimilitudeUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHaarMeasureScaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacter
import GroundTheory.Brauer.TensorSimple
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip Polynomial
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem charpoly_psi_eq_map_minpoly {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (γ : G.C)
    (hdeg : (minpoly G.F γ).natDegree = G.n) :
    (G.psi v γ).charpoly = (minpoly G.F γ).map v.embedding := by
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hg : ∀ a, G.psi v (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) ℂ) a :=
    fun a => by rw [G.psi_F, Matrix.algebraMap_eq_diagonal]; rfl
  let g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ := { G.psi v with commutes' := hg }
  let L : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) g (fun r _ => Algebra.commute_algebraMap_left r _)
  haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right (not_subsingleton _)
  have hL : ∀ x : G.C, L ((1 : ℂ) ⊗ₜ x) = G.psi v x := fun x => by
    show (Algebra.TensorProduct.lift _ g _) ((1 : ℂ) ⊗ₜ x) = _
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  have hli : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hdeg] at this
    exact this
  have hT : LinearIndependent ℂ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) :=
    Module.Flat.linearIndependent_one_tmul hli
  have hM : LinearIndependent ℂ (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) := by
    have := hT.map' L.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
    have e : (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) =
        L.toLinearMap ∘ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) := by
      funext i
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply]
      rw [hL, map_pow]
    rw [e]
    exact this
  have hint : IsIntegral ℂ (G.psi v γ) := Algebra.IsIntegral.isIntegral _
  set q := minpoly ℂ (G.psi v γ) with hq
  have hqm : q.Monic := minpoly.monic hint
  have hqdeg : G.n ≤ q.natDegree := by
    by_contra hlt
    push_neg at hlt
    have h0 : aeval (G.psi v γ) q = 0 := minpoly.aeval _ _
    rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at h0
    have h1 := Fintype.linearIndependent_iff.1 hM (fun i => q.coeff i) h0 ⟨q.natDegree, hlt⟩
    have h2 : q.coeff q.natDegree = 1 := hqm.coeff_natDegree
    rw [h2] at h1
    exact one_ne_zero h1
  have hpol : aeval (G.psi v γ) ((minpoly G.F γ).map v.embedding) = 0 := by
    have h : aeval (g γ) (minpoly G.F γ) = 0 := by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    change aeval (G.psi v γ) ((minpoly G.F γ).map (algebraMap G.F ℂ)) = 0
    rw [Polynomial.aeval_map_algebraMap]
    exact h
  have hFint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hm1 : ((minpoly G.F γ).map v.embedding).Monic := (minpoly.monic hFint).map _
  have hn1 : ((minpoly G.F γ).map v.embedding).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact hdeg
  have e1 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm hm1 (minpoly.dvd _ _ hpol)
    (by rw [hn1]; exact hqdeg)
  have e2 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm (Matrix.charpoly_monic _)
    (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hqdeg)
  rw [e2, e1]

theorem charpoly_psi_separable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (g : G.C),
    (minpoly G.F g).natDegree = G.n → (minpoly G.F g).Separable → (G.psi v g).charpoly.Separable := by
  intro p _ G v g hdeg hsep
  rw [charpoly_psi_eq_map_minpoly G v g hdeg]
  exact hsep.map

end GlobalTheory.LKMid
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem fixL_pos_unique_of_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 →
    ∀ (β : G.Cˣ), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ y₀ : grp G β,
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n →
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable →
    ∀ z z' : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re →
    FixL G v β y₀ z → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z := by
  intro p _ G v hsig β hsh hR y₀ hdeg hsep z z' hz hz' hf hf'
  obtain ⟨_, _, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G v β hsh hR
  set g0 : Matrix (Fin G.n) (Fin G.n) ℂ := (toV G v β y₀ : Matrix (Fin G.n) (Fin G.n) ℂ) with hg0
  set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := (Z : Matrix (Fin G.n) (Fin G.n) ℂ) with hZm
  set Zi : Matrix (Fin G.n) (Fin G.n) ℂ := ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) with hZi
  have hZiZ : Zi * Zm = 1 := by rw [hZi, hZm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hZZi : Zm * Zi = 1 := by rw [hZi, hZm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  set s : ℝ := ((((y₀ : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) with hs
  have hspos : 0 < s := by rw [hs]; exact_mod_cast y₀.2.2
  have hsim0 := GlobalTheory.LKCx.grp_similitude_herm p G v β y₀
  set g : Matrix (Fin G.n) (Fin G.n) ℂ := Zm * g0 * Zi with hg
  have hsim : gᴴ * G.gram v * g = (s : ℂ) • G.gram v := by
    have e1 : gᴴ * G.gram v * g = Ziᴴ * (g0ᴴ * (Zmᴴ * G.gram v * Zm) * g0) * Zi := by
      rw [hg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e1, ← hZ, hsim0]
    have e2 : Ziᴴ * ((((((y₀ : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) • herm G v β) * Zi =
        (s : ℂ) • ((Zm * Zi)ᴴ * G.gram v * (Zm * Zi)) := by
      rw [hZ, Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_mul]
      congr 1
      simp only [Matrix.mul_assoc]
    rw [e2, hZZi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hcp : g.charpoly.Separable := by
    have e : g = (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * g0 * ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) := rfl
    rw [e, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact GlobalTheory.LKMid.charpoly_psi_separable p G v _ hdeg hsep
  have hpos : ∀ w : Fin G.n → ℂ, star (Zm *ᵥ w) ⬝ᵥ G.gram v *ᵥ (Zm *ᵥ w) = star w ⬝ᵥ (herm G v β *ᵥ w) := by
    intro w; rw [hZ, GlobalTheory.form_conjTranspose_mul_mul]
  have heig : ∀ w : Fin G.n → ℂ, FixL G v β y₀ w → ∃ μ : ℂ, g *ᵥ (Zm *ᵥ w) = μ • (Zm *ᵥ w) := by
    rintro w ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    rw [hg, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hZiZ, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, hμ, Matrix.mulVec_smul]
  obtain ⟨c, hc⟩ := GlobalTheory.eigvec_pos_unique_of_similitude (G.gram v) (G.gram_herm v) (G.gram_det v) hsig g s hspos
    hsim hcp (Zm *ᵥ z) (Zm *ᵥ z') (by rw [hpos]; exact hz) (by rw [hpos]; exact hz') (heig z hf) (heig z' hf')
  refine ⟨c, ?_⟩
  have := congrArg (Zi *ᵥ ·) hc
  simp only [Matrix.mulVec_mulVec, hZiZ, Matrix.one_mulVec, Matrix.mulVec_smul] at this
  exact this

end GlobalTheory.LKCx
end
