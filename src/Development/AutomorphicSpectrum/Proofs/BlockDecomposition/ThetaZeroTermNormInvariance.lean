import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceEmbeddingProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComponentRationalIdele
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionDiagonal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldWeilActionDiagonal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormAtInertPlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilActionDiagonal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductFormulaGlobalCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductFormulaModulusRational
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormEqualsComplexAbsSq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicRealPartProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedStandardValuesAtIntegral

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta

variable {K : Type} [Field K] [NumberField K]

theorem degreeOneEmbedding_zero (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] : dg1 v w (0 : K) = 0 := by
  have hinj : Function.Injective (algebraMap (Qv v) (Kv K w)) := (algebraMap (Qv v) (Kv K w)).injective
  have h := Function.leftInverse_invFun hinj (0 : Qv v)
  simpa [dg1] using h

theorem value_zero_diagonal_norm : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
    L.ok → L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ),
      L.val (dg2 (nv v κ) 1 * g) 0 = c0 L κ * mp (nv v κ) (1 / 2) * L.val g 0 := by
  intro K _ _ _ c v L hok hsp g κ
  cases L with
  | ns w σ η Φ => exact hsp.elim
  | sp w₁ w₂ Φ =>
    obtain ⟨-, hlc, hcs⟩ := hok
    have hc : Continuous ((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) := by
      have h := (continuous_localAdelicChar (K := ℚ) v).comp continuous_neg
      have e : (⇑((GP.psiF v)⁻¹ : AddChar (Qv v) Circle)) = (⇑(localAdelicChar ℚ v)) ∘ Neg.neg := by
        funext x
        simp [AddChar.inv_apply]
      rw [e]
      exact h
    have hn : ((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) ≠ 1 := inv_ne_one.2 (localAdelicChar_ne_one v)
    have key := GlobalTheory.T.split_weil_action_diagonal (Qv v) ((GP.psiF v)⁻¹) hc hn (cAt c v w₁) Φ hlc hcs (nv v κ) g (0, 0)
    simp only [LM.val, c0, degreeOneEmbedding_zero]
    simpa using key

end GlobalTheory.CompanionTheory.FexTheta
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_value_zero_diagonal_norm : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ),
    L.val (dg2 (nv v κ) 1 * g) 0 = c0 L κ * mp (nv v κ) (1 / 2) * L.val g 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FexTheta.value_zero_diagonal_norm
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.ValZeroNs

theorem val_zero_dg : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
    L.ok → ¬ L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ),
      L.val (dg2 (nv v κ) 1 * g) 0 = c0 L κ * mp (nv v κ) (1 / 2) * L.val g 0 := by
  intro K _ _ h2 c v L hok hsp g κ
  have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  have hχc : Continuous ((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) := by
    have : (((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) : Qv v → Circle) = fun x => (GP.psiF v x)⁻¹ := by
      funext x; exact AddChar.inv_apply' _ _
    rw [this]
    exact hstd.1.inv
  have hχ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.mpr hstd.2.1
  cases L with
  | @sp w₁ w₂ i₁ i₂ Φ => exact absurd trivial hsp
  | @ns w i σ η Φ =>
    haveI := i
    obtain ⟨hU, hσ, hη, hΦ⟩ := hok
    have hN : ((nv v κ : (Qv v)ˣ) : Qv v) = Algebra.norm (Qv v) ((atW w κ : (Kv K w)ˣ) : Kv K w) := by
      have e1 : ((nv v κ : (Qv v)ˣ) : Qv v) =
          (((Units.map (Algebra.norm ℚ : K →* ℚ) κ : ℚˣ) : ℚ) : Qv v) := GlobalTheory.T.local_component_rational_idele v _
      have e2 := GlobalTheory.T.local_norm_at_inert_place K h2 v w hU (κ : K)
      rw [e1]
      exact e2.symm
    have h := GlobalTheory.T.field_weil_action_diagonal (Qv v) _ hχc hχ1 (Kv K w)
      (GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl K h2 v w i σ hσ)
      (continuous_adicCompletionMap v w) σ hσ η hη _ Φ hΦ (atW w κ) (nv v κ) hN g
      (algebraMap K (Kv K w) 0)
    have e0 : algebraMap K (Kv K w) 0 * ((atW w κ : (Kv K w)ˣ) : Kv K w) = algebraMap K (Kv K w) 0 := by
      rw [map_zero, zero_mul]
    rw [e0] at h
    exact h

end GlobalTheory.CompanionTheory.ValZeroNs
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_value_zero_diagonal_norm : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ¬ L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ),
    L.val (dg2 (nv v κ) 1 * g) 0 = c0 L κ * mp (nv v κ) (1 / 2) * L.val g 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ValZeroNs.val_zero_dg
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta

theorem zeroScalar_eq_whittakerScalar {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2)
    {c : HeckeCharacter K} {v : Pl} (L : LM c v) (hok : L.ok) (hct : ∀ x : (Qv v)ˣ, L.ct x = 1) (κ : Kˣ) :
    c0 L κ = cW L κ := by
  cases L with
  | ns w σ η Φ => rfl
  | sp w₁ w₂ Φ =>
    have hne : w₁ ≠ w₂ := hok.1
    obtain ⟨d1, d2, d3⟩ := GlobalTheory.T.split_place_embedding_properties K h2 v w₁ w₂ hne
    have heq : ∀ x, cAt c v w₁ x = cAt c v w₂ x := by
      intro x
      have h := hct x
      simp only [LM.ct] at h
      have h' : cAt c v w₁ x * (cAt c v w₂ x)⁻¹ = 1 := Units.ext (by simpa using h)
      exact mul_inv_eq_one.mp h'
    have n1 : dg1 v w₁ (κ : K) ≠ 0 := by
      intro h
      have h' := d1 κ
      rw [h, map_zero] at h'
      exact (map_ne_zero (algebraMap K (Kv K w₁))).mpr κ.ne_zero h'.symm
    have n2 : dg1 v w₂ (κ : K) ≠ 0 := by
      intro h
      have h' := d2 κ
      rw [h, map_zero] at h'
      exact (map_ne_zero (algebraMap K (Kv K w₂))).mpr κ.ne_zero h'.symm
    have hnv : nv v κ = Units.mk0 _ n1 * Units.mk0 _ n2 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mk0, Units.val_mk0, d3 κ]
      exact GlobalTheory.T.local_component_rational_idele v (Units.map (Algebra.norm ℚ : K →* ℚ) κ)
    have hc1 : cK c w₁ κ = ((cAt c v w₁ (Units.mk0 _ n1) : ℂˣ) : ℂ) := by
      have : atW w₁ κ = Units.map (algebraMap (Qv v) (Kv K w₁)).toMonoidHom (Units.mk0 _ n1) :=
        Units.ext (d1 κ).symm
      simp only [cK, cAt, MonoidHom.comp_apply, this]
    have hc2 : cK c w₂ κ = ((cAt c v w₂ (Units.mk0 _ n2) : ℂˣ) : ℂ) := by
      have : atW w₂ κ = Units.map (algebraMap (Qv v) (Kv K w₂)).toMonoidHom (Units.mk0 _ n2) :=
        Units.ext (d2 κ).symm
      simp only [cK, cAt, MonoidHom.comp_apply, this]
    simp only [c0, cW]
    rw [hc1, hc2, hnv, map_mul, Units.val_mul, heq (Units.mk0 _ n2)]

theorem theta_zero_term_norm_diagonal_invariant : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (DK : DatK K) (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (S : Finset (PlK K)), AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M → (∀ (v : Pl) (x : (Qv v)ˣ), (M v).ct x = 1) → ∀ (κ : Kˣ) (g : G2),
    thT n t M (dg2 (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) 1 * g) 0 = thT n t M g 0 := by
  intro K _ _ h2 hC DK c n t S hS M hM hct κ g
  obtain ⟨hok, S0, hS0⟩ := hM
  obtain ⟨hfin, hreal, hrealdg, -⟩ := GlobalTheory.T.adelic_realPart_properties
  obtain ⟨S1, hS1⟩ := GlobalTheory.CompanionTheory.AdelicIntegral.exists_finset_finAt_mem_integralGL g
  classical
  have hloc : ∀ v : Pl, (M v).val (finAt v (dg2 (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) 1 * g)) 0 =
      (cW (M v) κ * mp (Ad3.R.lc v (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ))) (1 / 2)) *
        (M v).val (finAt v g) 0 := by
    intro v
    have hmul : finAt v (dg2 (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) 1 * g) =
        dg2 (nv v κ) 1 * finAt v g := by
      have hl : Ad3.R.lc v 1 = 1 := by simp [Ad3.R.lc]
      rw [GroundTheory.Automorphic.Reduction.finAt_mul, hfin, hl]
      rfl
    rw [hmul, ← zeroScalar_eq_whittakerScalar h2 (M v) (hok v) (hct v) κ]
    by_cases hs : (M v).IsSp
    · exact GlobalTheory.T.split_value_zero_diagonal_norm K h2 c v (M v) (hok v) hs _ κ
    · exact GlobalTheory.T.field_value_zero_diagonal_norm K h2 c v (M v) (hok v) hs _ κ
  obtain ⟨hA, e1⟩ := GlobalTheory.T.product_formula_global_character K h2 hC DK c n t S hS M hok κ
  obtain ⟨hB, e2⟩ := GlobalTheory.T.product_formula_modulus_rational (Units.map (Algebra.norm ℚ : K →* ℚ) κ)
  have hV : (Function.mulSupport fun v => (M v).val (finAt v g) 0).Finite :=
    (S0 ∪ S1).finite_toSet.subset fun v hv => by
      by_contra hn
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hn
      obtain ⟨hU, hs⟩ := hS0 v hn.1
      exact hv (GlobalTheory.T.unramified_standard_values_at_integral K h2 c v (M v) hU (hok v) hs _ (hS1 v hn.2)).2
  obtain ⟨hz1, hz2⟩ := GlobalTheory.T.norm_equals_complex_abs_sq K h2 hC κ
  have hreal0 : piRc (chC n (Complex.I * t))
      (GL2Classical.realPart (dg2 (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) 1 * g)) (PhiInf n) (embC K 0) =
      chC n (Complex.I * t) (embU κ) * ((‖((embU κ : ℂˣ) : ℂ)‖ : ℝ) : ℂ) *
        piRc (chC n (Complex.I * t)) (GL2Classical.realPart g) (PhiInf n) (embC K 0) := by
    have h0 : embC K (0 : K) = 0 := by simp [embC]
    rw [hreal, hrealdg, map_one, h0]
    have h := GlobalTheory.T.real_weil_action_diagonal n t (embU κ) _ hz2 (GL2Classical.realPart g) 0
    rwa [zero_mul] at h
  have hz : (((|(((Units.map (Algebra.norm ℚ : K →* ℚ) κ : ℚˣ) : ℚ) : ℝ)| : ℝ)) : ℂ) ^ (1 / 2 : ℂ) =
      ((‖((embU κ : ℂˣ) : ℂ)‖ : ℝ) : ℂ) := by
    have hh : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [hz1, abs_of_nonneg (by positivity), hh, ← Complex.ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  rw [hz] at e2
  simp only [thT]
  rw [hreal0, finprod_congr hloc,
    finprod_mul_distrib ((hA.union hB).subset (Function.mulSupport_mul _ _)) hV,
    finprod_mul_distrib hA hB]
  linear_combination
    (piRc (chC n (Complex.I * t)) (GL2Classical.realPart g) (PhiInf n) (embC K 0) *
      (∏ᶠ v, (M v).val (finAt v g) 0) *
      (∏ᶠ v : Pl, mp (Ad3.R.lc v (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ))) (1 / 2)) *
      ((‖((embU κ : ℂˣ) : ℂ)‖ : ℝ) : ℂ)) * e1 +
    (piRc (chC n (Complex.I * t)) (GL2Classical.realPart g) (PhiInf n) (embC K 0) *
      (∏ᶠ v, (M v).val (finAt v g) 0)) * e2

end GlobalTheory.CompanionTheory.FexTheta
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_zero_term_norm_invariance : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (DK : DatK K) (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (S : Finset (PlK K)), AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M → (∀ (v : Pl) (x : (Qv v)ˣ), (M v).ct x = 1) → ∀ (κ : Kˣ) (g : G2),
    thT n t M (dg2 (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) 1 * g) 0 = thT n t M g 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FexTheta.theta_zero_term_norm_diagonal_invariant
end
