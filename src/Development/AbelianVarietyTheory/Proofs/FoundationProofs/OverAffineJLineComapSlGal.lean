import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoInvariantHolomorphicMemAdjoinJInvariant

section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.JInt

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

lemma det_pos (g : GQ) : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
  have h := g.2
  rw [Matrix.mem_glpos] at h
  simpa [ent, Matrix.det_fin_two] using h

lemma den_ne (g : GQ) {z : ℂ} (hz : z ∈ Hs) : (ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  have hz' : 0 < z.im := hz
  simp at him hre
  have hc : ent g 1 0 = 0 := by
    rcases him with h1 | h1
    · exact h1
    · exact absurd h1 hz'.ne'
  rw [hc] at hre
  simp at hre
  have := det_pos g
  rw [hc, hre] at this
  simp at this

lemma mob_im (g : GQ) {z : ℂ} (hz : z ∈ Hs) : mob g z ∈ Hs := by
  have hd := den_ne g hz
  have hz' : 0 < z.im := hz
  have hn : 0 < Complex.normSq ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ)) := Complex.normSq_pos.2 hd
  have key : (mob g z).im = ((ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) : ℝ) * z.im /
      Complex.normSq ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ)) := by
    simp only [mob]
    rw [Complex.div_im]
    simp
    field_simp
    ring
  show 0 < (mob g z).im
  rw [key]
  have := det_pos g
  have : (0 : ℝ) < ((ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) : ℝ) := by exact_mod_cast this
  positivity

lemma mob_diff (g : GQ) : DifferentiableOn ℂ (mob g) Hs := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  show DifferentiableAt ℂ (fun z => ((ent g 0 0 : ℂ) * z + (ent g 0 1 : ℂ)) / ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ))) z
  exact ((differentiableAt_id.const_mul _).add_const _).div
    ((differentiableAt_id.const_mul _).add_const _) (den_ne g hz)

def holR (X : Tower Ω ε) : Subring X.K where
  carrier := {h | ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)}
  mul_mem' := by
    rintro a b ⟨φ, hφ, ha⟩ ⟨ψ, hψ, hb⟩
    exact ⟨φ * ψ, hφ.mul hψ, by rw [map_mul, ha, hb]; rfl⟩
  one_mem' := ⟨fun _ => 1, differentiableOn_const 1, by rw [map_one]; rfl⟩
  add_mem' := by
    rintro a b ⟨φ, hφ, ha⟩ ⟨ψ, hψ, hb⟩
    exact ⟨φ + ψ, hφ.add hψ, by rw [map_add, ha, hb]; rfl⟩
  zero_mem' := ⟨fun _ => 0, differentiableOn_const 0, by rw [map_zero]; rfl⟩
  neg_mem' := by
    rintro a ⟨φ, hφ, ha⟩
    exact ⟨-φ, hφ.neg, by rw [map_neg, ha]; rfl⟩

end GlobalTheory.KZ.JInt

namespace GlobalTheory.KZ.JInt

open Polynomial in

theorem jK_sl_isIntegral : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ g : GQ, IsIntegral (Algebra.adjoin Ω {X.jK}) (X.sl g X.jK) := by
  intro Ω _ _ _ ε Tw hε hj g
  set f := Tw.sl g Tw.jK with hf
  obtain ⟨M, hM, hlev⟩ := Tw.level f
  haveI : NeZero M := ⟨hM.ne'⟩
  let red : SL(2, ℤ) →* SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))

  have hred : ∀ γ γ' : SL(2, ℤ), red γ = red γ' → Tw.sl (ofSL γ) f = Tw.sl (ofSL γ') f := by
    intro γ γ' h
    have hmem : γ' * γ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
      rw [CongruenceSubgroup.Gamma_mem']
      show red (γ' * γ⁻¹) = 1
      rw [map_mul, map_inv, h, mul_inv_cancel]
    have e : γ' = (γ' * γ⁻¹) * γ := by group
    rw [e, map_mul, Tw.sl_mul, hlev _ hmem]
  let S : Set Tw.K := Set.range fun γ : SL(2, ℤ) => Tw.sl (ofSL γ) f
  have hSfin : S.Finite := by
    classical
    let F : SL(2, ZMod M) → Tw.K := fun γb => if h : ∃ γ, red γ = γb then Tw.sl (ofSL h.choose) f else 0
    apply (Set.finite_range F).subset
    rintro _ ⟨γ, rfl⟩
    refine ⟨red γ, ?_⟩
    have h : ∃ γ', red γ' = red γ := ⟨γ, rfl⟩
    simp only [F, dif_pos h]
    exact hred _ _ h.choose_spec
  let T := hSfin.toFinset
  have hT : ∀ y, y ∈ T ↔ y ∈ S := fun y => Set.Finite.mem_toFinset hSfin
  let P : Tw.K[X] := ∏ y ∈ T, (X - C y)
  have hPmon : P.Monic := monic_prod_of_monic _ _ fun y _ => monic_X_sub_C y
  have hfT : f ∈ T := by
    rw [hT]; exact ⟨1, by simp [Tw.sl_one]⟩
  have hPf : P.eval f = 0 := by
    rw [eval_prod]
    exact Finset.prod_eq_zero hfT (by simp)

  have hinv : ∀ (δ : SL(2, ℤ)) (n : ℕ), Tw.sl (ofSL δ) (P.coeff n) = P.coeff n := by
    intro δ n
    have hmap : P.map ((Tw.sl (ofSL δ) : Tw.K ≃ₐ[Ω] Tw.K) : Tw.K →+* Tw.K) = P := by
      simp only [P, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C]
      refine Finset.prod_nbij' (fun y => Tw.sl (ofSL δ) y) (fun y => Tw.sl (ofSL δ⁻¹) y) ?_ ?_ ?_ ?_ ?_
      · intro y hy
        rw [hT] at hy ⊢
        obtain ⟨γ, rfl⟩ := hy
        exact ⟨γ * δ, by simp only [map_mul, Tw.sl_mul]⟩
      · intro y hy
        rw [hT] at hy ⊢
        obtain ⟨γ, rfl⟩ := hy
        exact ⟨γ * δ⁻¹, by simp only [map_mul, Tw.sl_mul]⟩
      · intro y _
        rw [← Tw.sl_mul, ← map_mul, mul_inv_cancel, map_one, Tw.sl_one]
      · intro y _
        rw [← Tw.sl_mul, ← map_mul, inv_mul_cancel, map_one, Tw.sl_one]
      · intro y _
        rfl
    have := congrArg (fun p => p.coeff n) hmap
    simpa [coeff_map] using this

  obtain ⟨φ, hφ, hjφ⟩ := hj
  have hmemS : ∀ y ∈ T, y ∈ holR Tw := by
    intro y hy
    rw [hT] at hy
    obtain ⟨γ, rfl⟩ := hy
    have e : Tw.sl (ofSL γ) f = Tw.sl (g * ofSL γ) Tw.jK := by rw [Tw.sl_mul]
    show Tw.sl (ofSL γ) f ∈ holR Tw
    rw [e]
    exact ⟨fun z => φ (mob (g * ofSL γ) z),
      hφ.comp (mob_diff _) (fun z hz => mob_im _ hz), Tw.an_sl _ _ _ hjφ⟩
  let Q : (holR Tw)[X] := ∏ y ∈ T.attach, (X - C ⟨y.1, hmemS y.1 y.2⟩)
  have hQ : Q.map (holR Tw).subtype = P := by
    simp only [Q, P, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C, Subring.subtype_apply]
    exact Finset.prod_attach T (fun y => X - C y)
  have hhol : ∀ n, P.coeff n ∈ holR Tw := by
    intro n
    rw [← hQ, coeff_map]
    exact (Q.coeff n).2

  have hA : ∀ n, P.coeff n ∈ Algebra.adjoin Ω {Tw.jK} := fun n =>
    GlobalTheory.T.slTwo_invariant_holomorphic_mem_adjoin_jInvariant ε Tw hε ⟨φ, hφ, hjφ⟩ (P.coeff n) (fun δ => hinv δ n) (hhol n)
  have hlift : P ∈ lifts (algebraMap (Algebra.adjoin Ω {Tw.jK}) Tw.K) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hA n⟩, rfl⟩
  obtain ⟨q, hqmap, -, hqmon⟩ := lifts_and_natDegree_eq_and_monic hlift hPmon
  exact ⟨q, hqmon, by rw [eval₂_eq_eval_map, hqmap, hPf]⟩

end GlobalTheory.KZ.JInt
end
end

section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_modularTower_j_comp_glTwoPosRat : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ g : GQ, IsIntegral (Algebra.adjoin Ω {X.jK}) (X.sl g X.jK) := by
  first | exact @GlobalTheory.KZ.JInt.jK_sl_isIntegral | exact GlobalTheory.KZ.JInt.jK_sl_isIntegral | (intros; apply GlobalTheory.KZ.JInt.jK_sl_isIntegral <;> assumption)
end

section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ

theorem vs_mem_of_isIntegral {K : Type} [Field K] (W : ValuationSubring K) {x : K} (h : IsIntegral W x) : x ∈ W := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  rw [← hy]; exact y.2

theorem hs_coeff_algebraMap {Ω : Type} [Field Ω] (c : Ω) (r : ℚ) :
    (algebraMap Ω (HahnSeries ℚ Ω) c).coeff r = if r = 0 then c else 0 := by
  rw [HahnSeries.algebraMap_apply']
  have : algebraMap Ω (PowerSeries Ω) c = PowerSeries.C c := rfl
  rw [this, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single]
  simp

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.gal_algebraMap (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  change (X.exp (X.gal s (algebraMap Ω X.K c))).coeff r = (X.exp (algebraMap Ω X.K (s c))).coeff r
  rw [X.gal_exp, AlgHom.commutes, AlgHom.commutes, hs_coeff_algebraMap, hs_coeff_algebraMap]
  split_ifs <;> simp

theorem Tower.gal_jK (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) : X.gal s X.jK = X.jK := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  change (X.exp (X.gal s X.jK)).coeff r = (X.exp X.jK).coeff r
  rw [X.gal_exp]
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [hn, map_intCast]

theorem Tower.adjoin_le_of_overY (X : Tower Ω ε) (W : ValuationSubring X.K) (hW : X.OverY W) :
    ∀ x ∈ Algebra.adjoin Ω {X.jK}, x ∈ W := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff.mp hy]; exact hW.2
  | algebraMap c => exact hW.1 c
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem Tower.overY_comap_sl_gal : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ W : ValuationSubring X.K, X.OverY W →
      (∀ g : GQ, X.OverY (W.comap (X.sl g).toRingEquiv.toRingHom)) ∧
        ∀ s : Ω ≃ₐ[ℚ] Ω, X.OverY (W.comap (X.gal s).toRingHom) := by
  intro Ω _ _ _ ε X hε hj W hW
  refine ⟨fun g => ⟨fun c => ?_, ?_⟩, fun s => ⟨fun c => ?_, ?_⟩⟩
  · rw [ValuationSubring.mem_comap]
    change X.sl g (algebraMap Ω X.K c) ∈ W
    rw [AlgEquiv.commutes]; exact hW.1 c
  · rw [ValuationSubring.mem_comap]
    change X.sl g X.jK ∈ W
    have hint := GlobalTheory.T.isIntegral_modularTower_j_comp_glTwoPosRat ε X hε hj g
    let A := Algebra.adjoin Ω {X.jK}
    have hle : A.toSubring ≤ W.toSubring := fun x hx => X.adjoin_le_of_overY W hW x hx
    let ι : A →+* W := Subring.inclusion hle
    let _ : Algebra A W := ι.toAlgebra
    have : IsScalarTower A W X.K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    exact vs_mem_of_isIntegral W (hint.tower_top)
  · rw [ValuationSubring.mem_comap]
    change X.gal s (algebraMap Ω X.K c) ∈ W
    rw [X.gal_algebraMap]; exact hW.1 (s c)
  · rw [ValuationSubring.mem_comap]
    change X.gal s X.jK ∈ W
    rw [X.gal_jK]; exact hW.2

end GlobalTheory.KZ
end
end
