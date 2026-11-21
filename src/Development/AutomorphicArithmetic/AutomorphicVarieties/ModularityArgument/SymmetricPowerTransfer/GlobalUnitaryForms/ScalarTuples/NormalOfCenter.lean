import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibCon
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricFiberMasterFormula
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricFiberTraceKernel
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberRepresentatives
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberLevelFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberFixedSetConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberFixedSetSupport
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberHasTraceLaw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.IotaEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ChiVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.HsCast
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableLipschitzLatticeNormPowSummand
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSClsD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSTest
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.CommOfConj
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtensionStatement
import GroundTheory.GlobalFields.Adele.WeakApprox
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NormEx
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.EmbAlg

section
namespace UpperTheory.V.Z.Sym.Glob

open Matrix Loc

private theorem base_bot {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (ι : Γ →* G) (U : Subgroup G)
    (W : Representation ℂ Γ V) : ∃ B : Base Γ G V, B.ι = ι ∧ B.U = U ∧ B.ω = 1 ∧ B.Γ₀ = ⊥ ∧ B.W = W := by
  refine ⟨⟨ι, U, 1, W, ⊥, bot_le, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl⟩
  · intro z hz
    rw [Subgroup.mem_bot.1 hz, map_one]
    exact one_mem _
  · intro z hz
    rw [Subgroup.mem_bot.1 hz, map_one]
    exact one_mem _
  · intro z hz v
    obtain rfl := Subgroup.mem_bot.1 hz
    simp

private theorem base_sub {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (ι : Γ →* G) (S : Subgroup Γ)
    (T U : Subgroup G) (h : ∀ γ ∈ S, ι γ ∈ T) (x : G) (W : Representation ℂ S V) :
    ∃ B : Base S T V, (∀ γ : S, (B.ι γ : G) = ι γ) ∧ (∀ g : T, g ∈ B.U ↔ x⁻¹ * g * x ∈ U) ∧ B.ω = 1 ∧ B.Γ₀ = ⊥ ∧ B.W = W := by
  obtain ⟨B, h1, h2, h3⟩ := base_bot ((ι.comp S.subtype).codRestrict T fun γ => h γ γ.2)
    ((U.comap (MulAut.conj x⁻¹).toMonoidHom).subgroupOf T) W
  refine ⟨B, fun γ => by rw [h1]; rfl, fun g => ?_, h3⟩
  rw [h2, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  simp

private theorem mem_SU {K : Type} [Field K] {Δ : K} (g : DX Δ) : g ∈ SU Δ ↔ (mt g).det = 1 := by
  rw [SU, MonoidHom.mem_ker, ← Units.val_eq_one]
  rfl

end UpperTheory.V.Z.Sym.Glob

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob in
theorem UpperTheory.V.Z.Sym.Glob.baseS :
    UpperTheory.V.Z.Sym.Glob.BaseS := by
  intro F _ _ Δ D _ V _ _ W ch htr x
  obtain ⟨-, ⟨ι, hι⟩, -⟩ := iotaEx F Δ
  have hmem : ∀ γ ∈ SU Δ, ι γ ∈ SA Δ := by
    intro γ hγ
    refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_comap.2 ((mem_SU _).2 ?_)
    have h1 : (mt ((ι γ).1 v)).det = 1 := by
      rw [hι γ v, ← RingHom.mapMatrix_apply, ← RingHom.map_det, (mem_SU γ).1 hγ, map_one]
    exact h1
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := base_sub ι (SU Δ) (SA Δ) D.U2 hmem x W
  refine ⟨B, ⟨fun γ v => ?_, h2, h3, h4, fun γ τ h => ?_⟩, h5⟩
  · rw [h1]
    exact hι _ v
  · rw [h5]
    exact htr γ τ h
end

section
open NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob

private theorem hs_real {d x : ℝ} (hd : d < 0) : Loc.hs d x * ((|x| : ℝ) : ℂ) = (x : ℂ) := by
  unfold Loc.hs
  rcases le_or_gt 0 x with h | h
  · rw [if_pos ⟨√x, 0, by rw [Real.sq_sqrt h]; ring⟩, abs_of_nonneg h, one_mul]
  · rw [if_neg (by rintro ⟨a, b, e⟩; nlinarith [sq_nonneg a, sq_nonneg b]), abs_of_neg h]
    push_cast
    ring

private theorem real_prod {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {Δ : F} (hΔ : ∀ σ : F →+* ℝ, σ Δ < 0) (x : F) :
    (∏ σ : F →+* ℝ, Loc.hs (σ Δ) (σ x)) * ((|Algebra.norm ℚ x| : ℚ) : ℂ) = ((Algebra.norm ℚ x : ℚ) : ℂ) := by
  have hN := GlobalTheory.LipschitzTR.LhsSum.prod_realEmb_eq_norm x
  have h1 : ((|Algebra.norm ℚ x| : ℚ) : ℂ) = ∏ σ : F →+* ℝ, ((|σ x| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_ratCast, Rat.cast_abs, ← hN, Finset.abs_prod]
    push_cast
    rfl
  have h2 : ((Algebra.norm ℚ x : ℚ) : ℂ) = ∏ σ : F →+* ℝ, ((σ x : ℝ) : ℂ) := by
    rw [← Complex.ofReal_ratCast, ← hN]
    push_cast
    rfl
  rw [h1, h2, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun σ _ => hs_real (hΔ σ)

private theorem delta_ne {F : Type} [Field F] [NumberField F] {Δ : F} {D : Dat Δ} (h : D.Ok) : Δ ≠ 0 := by
  intro hΔ
  haveI := h.real
  have h0 : ∏ τ : F →+* ℝ, τ 0 = 0 := by
    rw [GlobalTheory.LipschitzTR.LhsSum.prod_realEmb_eq_norm]
    simp
  obtain ⟨σ, -, -⟩ := Finset.prod_eq_zero_iff.mp h0
  have hσ := h.neg σ
  rw [hΔ, map_zero] at hσ
  exact lt_irrefl _ hσ

private theorem int_case {F : Type} [Field F] [NumberField F] {Δ : F} {D : Dat Δ} (h : D.Ok) (z : Fˣ) (a : 𝓞 F)
    (ha : (a : F) = z) :
    (Function.mulSupport fun v : Pl F => (D.χ v (Units.map (cv v : F →* Kv v) z) : ℂ)).Finite ∧
    (∏ᶠ v, (D.χ v (Units.map (cv v : F →* Kv v) z) : ℂ)) = ((Algebra.norm ℚ (z : F) : ℚ) : ℂ)⁻¹ := by
  haveI := h.real
  have hz : (z : F) ≠ 0 := z.ne_zero
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hz
    rw [← ha]
    rfl
  obtain ⟨hfin, hrec⟩ := recip F Δ (z : F) (delta_ne h) hz
  have hval : ∀ v : Pl F, (D.χ v (Units.map (cv v : F →* Kv v) z) : ℂ) =
      Loc.hs (cv v Δ) (cv v (z : F)) / (Nat.card (Ov v ⧸ Ideal.span {algebraMap (𝓞 F) (Ov v) a}) : ℂ) := by
    intro v
    rw [chiVal F Δ D h v _ (algebraMap (𝓞 F) (Ov v) a) (by rw [Units.coe_map, ← ha]; rfl)]
    rfl
  obtain ⟨cfin, cprod⟩ := GlobalTheory.LocalDifferentProduct.finprod_card_quot_map (K := F) (I := Ideal.span {a})
    (by simpa using ha0)
  simp only [Ideal.map_span, Set.image_singleton] at cfin cprod
  have cfinC : (Function.mulSupport fun v : Pl F =>
      (Nat.card (Ov v ⧸ Ideal.span {algebraMap (𝓞 F) (Ov v) a}) : ℂ)).Finite := by
    have e := Function.mulSupport_comp_eq (Nat.cast : ℕ → ℂ) (fun {n} => Nat.cast_eq_one)
      (fun v : Pl F => Nat.card (Ov v ⧸ Ideal.span {algebraMap (𝓞 F) (Ov v) a}))
    rw [Function.comp_def] at e
    rw [e]
    exact cfin
  rw [funext hval]
  refine ⟨(hfin.union cfinC).subset (Function.mulSupport_div _ _), ?_⟩
  rw [finprod_div_distrib hfin cfinC, hrec]
  have hcard : (∏ᶠ v : Pl F, (Nat.card (Ov v ⧸ Ideal.span {algebraMap (𝓞 F) (Ov v) a}) : ℂ)) =
      ((|Algebra.norm ℚ (z : F)| : ℚ) : ℂ) := by
    have e := (Nat.castRingHom ℂ : ℕ →* ℂ).map_finprod cfin
    simp only [MonoidHom.coe_coe, Nat.coe_castRingHom] at e
    rw [← e, cprod, Ideal.absNorm_span_singleton, ← ha, ← Algebra.coe_norm_int]
    rw [Nat.cast_natAbs, ← Int.cast_abs, Rat.cast_intCast]
  rw [hcard]
  have hp := real_prod h.neg (z : F)
  have hn : ((Algebra.norm ℚ (z : F) : ℚ) : ℂ) ≠ 0 := by
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hz)
  have hA : ((|Algebra.norm ℚ (z : F)| : ℚ) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hz)
  have hAA : ((|Algebra.norm ℚ (z : F)| : ℚ) : ℂ) * ((|Algebra.norm ℚ (z : F)| : ℚ) : ℂ) =
      ((Algebra.norm ℚ (z : F) : ℚ) : ℂ) * ((Algebra.norm ℚ (z : F) : ℚ) : ℂ) := by
    exact_mod_cast abs_mul_abs_self (Algebra.norm ℚ (z : F))
  calc (∏ σ : F →+* ℝ, Loc.hs (σ Δ) (σ (z : F))) / ((|Algebra.norm ℚ (z : F)| : ℚ) : ℂ)
      = (∏ σ : F →+* ℝ, Loc.hs (σ Δ) (σ (z : F))) * ((|Algebra.norm ℚ (z : F)| : ℚ) : ℂ) /
          (((|Algebra.norm ℚ (z : F)| : ℚ) : ℂ) * ((|Algebra.norm ℚ (z : F)| : ℚ) : ℂ)) := by
        rw [mul_div_mul_right _ _ hA]
    _ = ((Algebra.norm ℚ (z : F) : ℚ) : ℂ) /
          (((Algebra.norm ℚ (z : F) : ℚ) : ℂ) * ((Algebra.norm ℚ (z : F) : ℚ) : ℂ)) := by
        rw [hp, hAA]
    _ = ((Algebra.norm ℚ (z : F) : ℚ) : ℂ)⁻¹ := by
        rw [div_mul_cancel_left₀ hn]

theorem UpperTheory.V.Z.Sym.Glob.chiProd :
    UpperTheory.V.Z.Sym.Glob.ChiProd := by
  intro F _ _ Δ D h z
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 F) (z : F)
  have hb0 : algebraMap (𝓞 F) F b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have ha0 : algebraMap (𝓞 F) F a ≠ 0 := by
    intro h0
    apply z.ne_zero
    rw [← hab, h0, zero_div]
  have hz : z = Units.mk0 _ ha0 * (Units.mk0 _ hb0)⁻¹ := by
    ext
    simp [← hab, div_eq_mul_inv]
  obtain ⟨fa, pa⟩ := int_case h (Units.mk0 _ ha0) a rfl
  obtain ⟨fb, pb⟩ := int_case h (Units.mk0 _ hb0) b rfl
  have hf : ∀ v : Pl F, (D.χ v (Units.map (cv v : F →* Kv v) z) : ℂ) =
      (D.χ v (Units.map (cv v : F →* Kv v) (Units.mk0 _ ha0)) : ℂ) /
        (D.χ v (Units.map (cv v : F →* Kv v) (Units.mk0 _ hb0)) : ℂ) := by
    intro v
    rw [hz, map_mul, map_inv, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]
  have hinv : Algebra.norm ℚ ((algebraMap (𝓞 F) F b)⁻¹) = (Algebra.norm ℚ (algebraMap (𝓞 F) F b))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, inv_mul_cancel₀ hb0, map_one]
  rw [finprod_congr hf, finprod_div_distrib fa fb, pa, pb, hz]
  simp [map_mul, hinv, div_eq_mul_inv, mul_comm]
end

section
namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

private theorem ext_char {A G C : Type} [Group A] [Group G] [CommGroup C] (σ : A →* G)
    (hσ : ∀ z, σ z ∈ Subgroup.center G) (χ : A →* C) (J Kg : Subgroup G) (hJ : J ≤ Kg)
    (hχ : ∀ z, σ z ∈ Kg → χ z = 1) :
    ∃ ω : ↥(σ.range ⊔ J) →* C, (∀ u z, (σ z)⁻¹ * u.1 ∈ J → ω u = χ z) ∧ ∀ u, u.1 ∈ Kg → ω u = 1 := by
  classical
  have hc : ∀ z x, σ z * x = x * σ z := fun z x => (Subgroup.mem_center_iff.mp (hσ z) x).symm
  have hmul : ∀ z z' a b, (σ z)⁻¹ * a ∈ J → (σ z')⁻¹ * b ∈ J → (σ (z * z'))⁻¹ * (a * b) ∈ J := by
    intro z z' a b h h'
    have hc' : (σ z')⁻¹ * ((σ z)⁻¹ * a) = ((σ z)⁻¹ * a) * (σ z')⁻¹ := by
      rw [← map_inv]; exact hc _ _
    have e : (σ (z * z'))⁻¹ * (a * b) = ((σ z)⁻¹ * a) * ((σ z')⁻¹ * b) := by
      calc (σ (z * z'))⁻¹ * (a * b) = (σ z')⁻¹ * ((σ z)⁻¹ * a) * b := by
            rw [map_mul, _root_.mul_inv_rev]; group
        _ = ((σ z)⁻¹ * a) * (σ z')⁻¹ * b := by rw [hc']
        _ = ((σ z)⁻¹ * a) * ((σ z')⁻¹ * b) := by group
    rw [e]; exact J.mul_mem h h'
  let S : Subgroup G :=
    { carrier := {u | ∃ z, (σ z)⁻¹ * u ∈ J}
      one_mem' := ⟨1, by simp⟩
      mul_mem' := by
        rintro a b ⟨z, hz⟩ ⟨z', hz'⟩
        exact ⟨z * z', hmul _ _ _ _ hz hz'⟩
      inv_mem' := by
        rintro a ⟨z, hz⟩
        refine ⟨z⁻¹, ?_⟩
        have h := J.inv_mem hz
        rw [_root_.mul_inv_rev, inv_inv, ← hc] at h
        simpa [map_inv] using h }
  have hsup : σ.range ⊔ J ≤ S := by
    refine sup_le ?_ ?_
    · rintro _ ⟨z, rfl⟩
      exact ⟨z, by simp⟩
    · intro j hj
      exact ⟨1, by simpa using hj⟩
  have hS : ∀ u ∈ σ.range ⊔ J, ∃ z, (σ z)⁻¹ * u ∈ J := fun u hu => hsup hu
  have hwd : ∀ z z' x, (σ z)⁻¹ * x ∈ J → (σ z')⁻¹ * x ∈ J → χ z = χ z' := by
    intro z z' x h h'
    have hm := J.mul_mem h (J.inv_mem h')
    have e : (σ z)⁻¹ * x * ((σ z')⁻¹ * x)⁻¹ = σ (z⁻¹ * z') := by
      rw [map_mul, map_inv]; group
    rw [e] at hm
    have h2 := hχ _ (hJ hm)
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  let f : ↥(σ.range ⊔ J) → C := fun u => χ (Classical.choose (hS u.1 u.2))
  have hf : ∀ (u : ↥(σ.range ⊔ J)) z, (σ z)⁻¹ * u.1 ∈ J → f u = χ z :=
    fun u z h => hwd _ _ _ (Classical.choose_spec (hS u.1 u.2)) h
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, hf, ?_⟩
  · exact (hf 1 1 (by simp)).trans (map_one χ)
  · intro u v
    obtain ⟨z, hz⟩ := hS u.1 u.2
    obtain ⟨z', hz'⟩ := hS v.1 v.2
    show f (u * v) = f u * f v
    rw [hf u z hz, hf v z' hz', hf (u * v) (z * z') (hmul _ _ _ _ hz hz'), map_mul]
  · intro u hu
    obtain ⟨z, hz⟩ := hS u.1 u.2
    show f u = 1
    rw [hf u z hz]
    apply hχ
    have e : u.1 * ((σ z)⁻¹ * u.1)⁻¹ = σ z := by group
    rw [← e]
    exact Kg.mul_mem hu (Kg.inv_mem (hJ hz))

private theorem prod_char {I : Type} (Gv : I → Type) [∀ v, Group (Gv v)] (K U : ∀ v, Subgroup (Gv v))
    (w : ∀ v, U v →* ℂˣ) (hw : ∀ v u, u.1 ∈ K v → w v u = 1) :
    ∃ ω : (rpg Gv K).box U →* ℂˣ, ∀ (u : (rpg Gv K).box U) (c : I → ℂˣ),
      (∀ v (h : u.1.1 v ∈ U v), w v ⟨u.1.1 v, h⟩ = c v) → (ω u : ℂ) = ∏ᶠ v, (c v : ℂ) := by
  classical
  have hmem : ∀ (u : (rpg Gv K).box U) v, u.1.1 v ∈ U v := fun u v => Subgroup.mem_iInf.mp u.2 v
  let g : (rpg Gv K).box U → I → ℂˣ := fun u v => w v ⟨u.1.1 v, hmem u v⟩
  have hfin : ∀ u, (Function.mulSupport (g u)).Finite := by
    intro u
    have h := Filter.eventually_cofinite.mp ((rpg Gv K).ae u.1)
    refine h.subset ?_
    intro v hv
    by_contra hK
    exact hv (hw v ⟨u.1.1 v, hmem u v⟩ (not_not.mp hK))
  refine ⟨{ toFun := fun u => ∏ᶠ v, g u v, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · show ∏ᶠ v, g 1 v = 1
    rw [show g 1 = fun _ => 1 from funext fun v => map_one (w v)]
    exact finprod_one
  · intro a b
    show ∏ᶠ v, g (a * b) v = (∏ᶠ v, g a v) * ∏ᶠ v, g b v
    have e : g (a * b) = fun v => g a v * g b v := by
      funext v
      exact map_mul (w v) ⟨a.1.1 v, hmem a v⟩ ⟨b.1.1 v, hmem b v⟩
    rw [e]
    exact finprod_mul_distrib (hfin a) (hfin b)
  · intro u c hc
    show ((∏ᶠ v, g u v : ℂˣ) : ℂ) = ∏ᶠ v, (c v : ℂ)
    have e : g u = c := funext fun v => hc v (hmem u v)
    rw [← e]
    exact MonoidHom.map_finprod (Units.coeHom ℂ) (hfin u)

section Local

variable {K : Type} [Field K] (Δ : K)

private theorem scal_ex : ∃ σ : Kˣ →* DX Δ, (∀ z s, IsScal z s ↔ s = σ z) ∧ ZD Δ = σ.range ∧
    ∀ z, σ z ∈ Subgroup.center (DX Δ) := by
  classical
  let f : Kˣ →* GL (Fin 2) (Lsq K Δ) :=
    (GeneralLinearGroup.scalar (Fin 2)).comp (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ))
  have hfm : ∀ z, ((f z : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) =
      Matrix.scalar (Fin 2) (algebraMap K (Lsq K Δ) z) := fun z => by simp [f]
  have hcomm : ∀ z (g : GL (Fin 2) (Lsq K Δ)), f z * g = g * f z := by
    intro z g
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hfm]
    exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq
  have hmem : ∀ z, f z ∈ DX Δ := by
    intro z
    show GeneralLinearGroup.map (starRingEnd _) (f z) = MulAut.conj (wJ Δ)⁻¹ (f z)
    rw [MulAut.conj_apply, ← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    apply Units.ext
    show ((f z : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd _) = _
    rw [hfm]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · ext <;> simp [starRingEnd_apply]
    · simp
  refine ⟨f.codRestrict (DX Δ) hmem, ?_, ?_, ?_⟩
  · intro z s
    have e : (((f.codRestrict (DX Δ) hmem z : DX Δ) : GL (Fin 2) (Lsq K Δ)) :
        Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = Matrix.scalar (Fin 2) (algebraMap K (Lsq K Δ) z) := hfm z
    constructor
    · intro h
      apply Subtype.ext
      apply Units.ext
      exact (show mt s = _ from h).trans e.symm
    · rintro rfl
      exact e
  · ext s
    rw [ZD, Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.mem_range]
    refine exists_congr fun z => ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · intro z
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : GL (Fin 2) (Lsq K Δ)) * f z = f z * g
    exact (hcomm z g).symm

variable {Δ} {O : Type} [CommRing O] [Algebra O K]

private theorem scal_int {z : Kˣ} {s : DX Δ} (h : IsScal z s) (hs : s ∈ KD Δ O) : IsIntegral O (z : K) := by
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hs)
  have h1 : ((s : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0 =
      algebraMap K (Lsq K Δ) z := by
    rw [show ((s : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = _ from h]
    simp
  have h2 : ((s : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0 =
      ((g : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ))) 0 0 : Lsq K Δ) := by
    rw [← hg]
    rfl
  have h3 : IsIntegral O (algebraMap K (Lsq K Δ) z) := by
    rw [← h1, h2]
    exact ((g : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ))) 0 0).2
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom O K (Lsq K Δ))
    (algebraMap K (Lsq K Δ)).injective).mp h3

private theorem loc_char [IsDomain O] [IsIntegrallyClosed O] [IsFractionRing O K] (χ : Kˣ →* ℂˣ) (hχ : Unr O χ)
    (J : Subgroup (DX Δ)) (hJ : J ≤ KD Δ O) :
    ∃ ω : ↥(ZD Δ ⊔ J) →* ℂˣ, (∀ u z s, IsScal z s → s⁻¹ * u.1 ∈ J → ω u = χ z) ∧ ∀ u, u.1 ∈ KD Δ O → ω u = 1 := by
  obtain ⟨σ, hs, hZ, hc⟩ := scal_ex (K := K) Δ
  have hχ' : ∀ z, σ z ∈ KD Δ O → χ z = 1 := by
    intro z hz
    have hi : IsIntegral O (z : K) := scal_int ((hs z (σ z)).mpr rfl) hz
    have hz' : σ z⁻¹ ∈ KD Δ O := by rw [map_inv]; exact (KD Δ O).inv_mem hz
    have hi' : IsIntegral O ((z⁻¹ : Kˣ) : K) := scal_int ((hs z⁻¹ (σ z⁻¹)).mpr rfl) hz'
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi'
    have hab : a * b = 1 := by
      apply IsFractionRing.injective O K
      rw [map_mul, ha, hb, map_one, Units.mul_inv]
    let u : Oˣ := ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
    have hu : Units.map (algebraMap O K : O →* K) u = z := Units.ext ha
    rw [← hu]
    exact hχ u
  rw [hZ]
  obtain ⟨ω, h1, h2⟩ := ext_char σ hc χ J (KD Δ O) hJ hχ'
  refine ⟨ω, ?_, h2⟩
  intro u z s hzs hu
  rw [(hs z s).mp hzs] at hu
  exact h1 u z hu

end Local

theorem baseK : BaseK := by
  intro F _ _ Δ D hD V _ _ W ch hW htr
  classical
  obtain ⟨ιD, hιD⟩ := (iotaEx F Δ).2.1
  have hloc : ∀ v : Pl F, ∃ ω : ↥(ZD (cv v Δ) ⊔ D.J2v v) →* ℂˣ,
      (∀ u z s, IsScal z s → s⁻¹ * u.1 ∈ D.J2v v → ω u = D.χ v z) ∧
      ∀ u, u.1 ∈ KD (cv v Δ) (Ov v) → ω u = 1 := by
    intro v
    have hJ : D.J2v v ≤ KD (cv v Δ) (Ov v) := by
      unfold Dat.J2v
      split_ifs with hv
      · exact (hD.sig v hv).levelTwoLeIntegral
      · exact le_rfl
    exact loc_char (D.χ v) (hD.chi v).1 (D.J2v v) hJ
  choose w hw1 hw2 using hloc
  obtain ⟨ω, hω⟩ := prod_char (fun v => ↥(DX (cv v Δ))) (fun v => KD (cv v Δ) (Ov v))
    (fun v => ZD (cv v Δ) ⊔ D.J2v v) w hw2
  have hsc : ∀ (z0 : Fˣ) (s : DX Δ), IsScal z0 s →
      ∀ v, IsScal (Units.map (cv v : F →* Kv v) z0) ((ιD s : DA Δ).1 v) := by
    intro z0 s hs v
    show mt _ = _
    rw [hιD s v, show mt s = _ from hs]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · ext <;> simp [lmap]
    · simp
  have hlocZ : ∀ v (z : (Kv v)ˣ) (s : DX (cv v Δ)), IsScal z s →
      s ∈ ZD (cv v Δ) ∧ s ∈ Subgroup.center (DX (cv v Δ)) := by
    intro v z s h
    obtain ⟨σ, hs, hZ, hc⟩ := scal_ex (K := Kv v) (cv v Δ)
    rw [(hs z s).mp h, hZ]
    exact ⟨⟨z, rfl⟩, hc z⟩
  obtain ⟨σ, hsF, hZ, hcF⟩ := scal_ex (K := F) Δ
  have hZs : ∀ z ∈ ZD Δ, ∃ z0 : Fˣ, IsScal z0 z := by
    intro z hz
    rw [hZ] at hz
    obtain ⟨z0, rfl⟩ := hz
    exact ⟨z0, (hsF z0 _).mpr rfl⟩
  have hmemU : ∀ z ∈ ZD Δ, ιD z ∈ D.UZ := by
    intro z hz
    obtain ⟨z0, h0⟩ := hZs z hz
    refine Subgroup.mem_iInf.mpr fun v => ?_
    show (ιD z : DA Δ).1 v ∈ ZD (cv v Δ) ⊔ D.J2v v
    exact Subgroup.mem_sup_left (hlocZ v _ _ (hsc z0 z h0 v)).1
  have hωs : ∀ (z0 : Fˣ) (s : DX Δ) (h : IsScal z0 s) (hm : ιD s ∈ D.UZ),
      ((ω ⟨ιD s, hm⟩ : ℂˣ) : ℂ) = ((Algebra.norm ℚ (z0 : F) : ℚ) : ℂ)⁻¹ := by
    intro z0 s h hm
    rw [← chiProd F Δ D hD z0]
    refine hω ⟨ιD s, hm⟩ (fun v => D.χ v (Units.map (cv v : F →* Kv v) z0)) ?_
    intro v hv
    refine hw1 v _ _ _ (hsc z0 s h v) ?_
    rw [inv_mul_cancel]
    exact (D.J2v v).one_mem
  let B : Base (DX Δ) (DA Δ) V :=
    { ι := ιD
      U := D.UZ
      ω := ω
      W := W
      Γ₀ := ZD Δ
      cenΓ := by
        rw [hZ]
        rintro _ ⟨z, rfl⟩
        exact hcF z
      cenG := by
        intro z hz
        obtain ⟨z0, h0⟩ := hZs z hz
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        funext v
        exact Subgroup.mem_center_iff.mp (hlocZ v _ _ (hsc z0 z h0 v)).2 (g.1 v)
      memU := hmemU
      scal := by
        intro z hz x
        obtain ⟨z0, h0⟩ := hZs z hz
        rw [hW z0 z h0 x]
        congr 1
        exact (hωs z0 z h0 _).symm }
  refine ⟨B, ⟨hιD, rfl, ?_, rfl, htr⟩, rfl⟩
  intro u z s hzs
  exact hω u (fun v => D.χ v (z v)) fun v hv => hw1 v _ (z v) (s v) (hzs v).1 (hzs v).2

end UpperTheory.V.Z.Sym.Glob
end

section
open NumberField IsDedekindDomain Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob

private theorem eventually_isIntegral_cv {F : Type} [Field F] [NumberField F] (t : F) :
    ∀ᶠ v : Pl F in Filter.cofinite, IsIntegral (Ov v) (cv v t) := by
  have h := (FiniteAdeleRing.algebraMap (𝓞 F) F t).2
  filter_upwards [h] with v hv
  exact isIntegral_Ov.2 hv

private theorem ae_int {F : Type} [Field F] [NumberField F] {Δ : F} (a : Lsq F Δ) :
    ∀ᶠ v : Pl F in Filter.cofinite, IsIntegral (Ov v) (lmap (cv v) Δ a) := by
  filter_upwards [eventually_isIntegral_cv Δ, eventually_isIntegral_cv a.re, eventually_isIntegral_cv a.im] with v h1 h2 h3
  have key := isIntegral_of_coords (O := Ov v) (a := lmap (cv v) Δ a) (m := 1) isIntegral_one
    (by simpa using h1) h2 h3
  simpa using key

private def dmap {K K' : Type} [Field K] [Field K'] (f : K →+* K') (Δ : K) : DX Δ →* DX (f Δ) :=
  ((GeneralLinearGroup.map (lmap f Δ)).comp (DX Δ).subtype).codRestrict _ fun γ => mem_DX.2 (by
    have e : ∀ y : Lsq K Δ, lmap f Δ (star y) = star (lmap f Δ y) := fun y => by ext <;> simp [lmap]
    refine ⟨?_, ?_⟩
    · change lmap f Δ (mt γ 1 1) = star (lmap f Δ (mt γ 0 0))
      rw [(mt_mem γ).1, e]
    · change lmap f Δ (mt γ 1 0) = -star (lmap f Δ (mt γ 0 1))
      rw [(mt_mem γ).2, map_neg, e])

private theorem ex_iota {F : Type} [Field F] [NumberField F] (Δ : F) : ∃ ι : DX Δ →* DA Δ, IsIotaD ι := by
  have hall : ∀ g : DX Δ, ∀ᶠ v : Pl F in Filter.cofinite,
      ∀ i j : Fin 2, IsIntegral (Ov v) (Glob.mt (dmap (cv v) Δ g) i j) := by
    intro g
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact ae_int (Glob.mt g i j)
  refine ⟨{ toFun := fun γ => ⟨fun v => dmap (cv v) Δ γ, ?_⟩,
            map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · show ∀ᶠ v in Filter.cofinite, dmap (cv v) Δ γ ∈ KD (cv v Δ) (Ov v)
    filter_upwards [hall γ, hall γ⁻¹] with v h1 h2
    rw [mem_KD]
    refine ⟨h1, fun i j => ?_⟩
    have h := h2 i j
    rwa [map_inv] at h
  · exact Subtype.ext (funext fun v => map_one _)
  · exact fun a b => Subtype.ext (funext fun v => map_mul _ a b)
  · intro γ v
    rfl

theorem UpperTheory.V.Z.Sym.Glob.finS :
    UpperTheory.V.Z.Sym.Glob.FinS := by
  intro F _ _ Δ D h V _ _ ch x B hB
  have := h.real
  obtain ⟨ι, hι⟩ := ex_iota Δ
  exact ⟨⟨finS_cls_of D ι hι (clsD h.neg ι hι) (relIndex_normOneLevel_maximalCompact_ne_zero D h) hB, finS_stab D h (normOneLevel_le_maximalCompact D h) hB⟩,
    finS_test F Δ D h V ch x B hB⟩
end

section
open NumberField Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob

private theorem four_values (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Δ x : F)
    (hΔ : ∀ σ : F →+* ℝ, σ Δ < 0) (hx : ∀ σ : F →+* ℝ, 0 < σ x) :
    x ≠ 0 ∧ ∃ a b c d : F, x = a ^ 2 - Δ * b ^ 2 + (c ^ 2 - Δ * d ^ 2) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  let σ : F →+* ℝ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)
  have hx0 : x ≠ 0 := fun h => by simpa [h] using hx σ
  have hΔ0 : Δ ≠ 0 := fun h => by simpa [h] using hΔ σ
  refine ⟨hx0, ?_⟩
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.LocalQuad.isotropic_of_indefinite GlobalTheory.T.hasse_norm_theorem_quadratic_extension F (ι := Fin 5) ![1, -Δ, 1, -Δ, -x]
    (by simp) (fun i => by fin_cases i <;> simp [hx0, hΔ0])
    (fun s => ⟨4, 0, by simpa using hx s, by simp⟩)
  simp [Fin.sum_univ_succ] at hy
  have hy' : y 0 ^ 2 - Δ * y 1 ^ 2 + (y 2 ^ 2 - Δ * y 3 ^ 2) = x * y 4 ^ 2 := by
    linear_combination hy
  have he : y 4 ≠ 0 := by
    intro h
    apply hy0
    have h1 := congrArg σ hy'
    simp only [h, map_add, map_sub, map_mul, map_pow, map_zero] at h1
    have hn := hΔ σ
    have p1 : 0 ≤ -σ Δ * σ (y 1) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have p3 : 0 ≤ -σ Δ * σ (y 3) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have p0 := sq_nonneg (σ (y 0))
    have p2 := sq_nonneg (σ (y 2))
    have e0 : σ (y 0) ^ 2 = 0 := by nlinarith
    have e2 : σ (y 2) ^ 2 = 0 := by nlinarith
    have e1 : -σ Δ * σ (y 1) ^ 2 = 0 := by nlinarith
    have e3 : -σ Δ * σ (y 3) ^ 2 = 0 := by nlinarith
    have z0 : y 0 = 0 := by simpa using e0
    have z2 : y 2 = 0 := by simpa using e2
    have z1 : y 1 = 0 := by simpa [hΔ0] using e1
    have z3 : y 3 = 0 := by simpa [hΔ0] using e3
    funext i
    fin_cases i
    exacts [z0, z1, z2, z3, h]
  refine ⟨y 0 / y 4, y 1 / y 4, y 2 / y 4, y 3 / y 4, ?_⟩
  field_simp
  linear_combination -hy'

private theorem ex_DX {K : Type} [Field K] (Δ x : K) (hx : x ≠ 0) (a b : Lsq K Δ)
    (h : a * star a + b * star b = algebraMap K _ x) : ∃ g : DX Δ, (mt g).det = algebraMap K _ x := by
  have hd : (!![a, b; -star b, star a] : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).det = algebraMap K _ x := by
    rw [det_fin_two_of, ← h]; ring
  have hu : IsUnit (!![a, b; -star b, star a] : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, hd]
    exact (IsUnit.mk0 x hx).map _
  refine ⟨⟨hu.unit, ?_⟩, hd⟩
  show GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) hu.unit = (wJ Δ)⁻¹ * hu.unit * (wJ Δ)⁻¹⁻¹
  rw [inv_inv]
  apply Units.ext
  show (!![a, b; -star b, star a] : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd (Lsq K Δ)) =
    !![0, -1; 1, 0] * !![a, b; -star b, star a] * !![0, 1; -1, 0]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [starRingEnd_apply]

theorem UpperTheory.V.Z.Sym.Glob.normD :
    UpperTheory.V.Z.Sym.Glob.NormD := by
  intro F _ _ Δ D hD x hx
  haveI := hD.real
  obtain ⟨hx0, a, b, c, d, h⟩ := four_values F Δ x hD.neg hx
  refine ex_DX Δ x hx0 ⟨a, b⟩ ⟨c, d⟩ ?_
  ext
  · simp; linear_combination -h
  · simp; ring
end

section
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc Filter Topology

private theorem pow_nhds {K : Type} [NontriviallyNormedField K] [CompleteSpace K] {R : Type} [Ring R] [Algebra K R]
    {ι : Type} [Fintype ι] (p : (ι → K) →ₗ[K] R) (q : R →ₗ[K] (ι → K)) (hqp : ∀ x, q (p x) = x)
    (hmul : ∀ x y, p (q (p x * p y)) = p x * p y) (o : ι → K) (ho : p o = 1) (n : ℕ) (hn : (n : K) ≠ 0)
    (P : (ι → K) → Prop) (hP : ∀ᶠ y in 𝓝 o, P y) : ∀ᶠ x in 𝓝 o, ∃ y, P y ∧ p x = p y ^ n := by
  have hpow : ∀ k x, p (q (p x ^ k)) = p x ^ k := by
    intro k x
    induction k with
    | zero => rw [pow_zero, ← ho, hqp]
    | succ k ih =>
      rw [pow_succ]
      have := hmul (q (p x ^ k)) x
      rwa [ih] at this
  let Bl : (ι → K) →ₗ[K] (ι → K) →ₗ[K] (ι → K) := LinearMap.mk₂ K (fun a b => q (p a * p b))
    (fun a a' b => by simp [add_mul]) (fun c a b => by simp [smul_mul_assoc])
    (fun a b b' => by simp [mul_add]) (fun c a b => by simp [mul_smul_comm])
  let B : (ι → K) →L[K] (ι → K) →L[K] (ι → K) :=
    LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ Bl)
  have hB : ∀ a b, B a b = q (p a * p b) := fun a b => rfl
  let f : ℕ → (ι → K) → (ι → K) := fun k x => q (p x ^ k)
  have hfs : ∀ k, f (k + 1) = fun x => B (f k x) x := by
    intro k
    funext x
    simp only [f, hB, hpow, pow_succ]
  have hfo : ∀ k, f k o = o := by
    intro k
    simp only [f, ho, one_pow]
    rw [← ho, hqp]
  have hder : ∀ k : ℕ, HasStrictFDerivAt (f k) ((k : K) • ContinuousLinearMap.id K (ι → K)) o := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.cast_zero, zero_smul]
      have : f 0 = fun _ => o := by
        funext x
        simp only [f, pow_zero]
        rw [← ho, hqp]
      rw [this]
      exact hasStrictFDerivAt_const _ _
    | succ k ih =>
      rw [hfs k]
      refine (B.hasStrictFDerivAt_of_bilinear ih (hasStrictFDerivAt_id o)).congr_fderiv ?_
      ext h i
      simp [hB, hfo, ho, hqp, add_smul, add_comm]
  have hn' := hder n
  let e : (ι → K) ≃L[K] (ι → K) := (LinearEquiv.smulOfNeZero K (ι → K) (n : K) hn).toContinuousLinearEquiv
  have he : (e : (ι → K) →L[K] (ι → K)) = (n : K) • ContinuousLinearMap.id K _ :=
    ContinuousLinearMap.ext fun x => rfl
  rw [← he] at hn'
  have hmap := hn'.map_nhds_eq_of_equiv
  rw [hfo] at hmap
  rw [← hmap, Filter.eventually_map]
  filter_upwards [hP] with y hy
  exact ⟨y, hy, hpow n y⟩

private theorem int_nhds {K : Type} [NontriviallyNormedField K] [CompleteSpace K] (O : Type) [CommRing O] [IsDomain O] [Algebra O K] [IsFractionRing O K]
    (hO : ∀ᶠ s in 𝓝 (0 : K), s ∈ (algebraMap O K).range) {L : Type} [CommRing L] [Algebra K L] [Algebra O L] [IsScalarTower O K L]
    [Module.Finite K L] {ι : Type} [Fintype ι] (l : (ι → K) →ₗ[K] L) (o : ι → K) (ho : IsIntegral O (l o)) :
    ∀ᶠ x in 𝓝 o, IsIntegral O (l x) := by
  classical
  let e : ι → (ι → K) := fun i j => if i = j then 1 else 0
  have hint : ∀ i, ∃ m : nonZeroDivisors O, IsIntegral O (m • l (e i)) := fun i =>
    IsIntegral.exists_multiple_integral_of_isLocalization (Rₘ := K) (nonZeroDivisors O) (l (e i)) (Algebra.IsIntegral.isIntegral (R := K) _)
  choose m hm using hint
  have hc : ∀ i, algebraMap O K (m i) ≠ 0 := fun i =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (m i).2
  have hev : ∀ i, ∀ᶠ x in 𝓝 o, (x i - o i) / algebraMap O K (m i) ∈ (algebraMap O K).range := by
    intro i
    have hcont : Continuous (fun x : ι → K => (x i - o i) / algebraMap O K (m i)) := by fun_prop
    have ht := hcont.tendsto o
    rw [sub_self, zero_div] at ht
    exact ht.eventually hO
  filter_upwards [Filter.eventually_all.mpr hev] with x hx
  have hsplit : l x = l o + ∑ i, (x i - o i) • l (e i) := by
    have h1 : x - o = ∑ i, (x - o) i • e i := pi_eq_sum_univ (x - o)
    have h2 : l (x - o) = ∑ i, (x i - o i) • l (e i) := by
      rw [h1, map_sum]
      simp [map_smul]
    rw [← h2, ← map_add, add_sub_cancel]
  rw [hsplit]
  refine IsIntegral.add ho (IsIntegral.sum _ fun i _ => ?_)
  obtain ⟨s, hs⟩ := hx i
  have hxi : x i - o i = algebraMap O K s * algebraMap O K (m i) := by
    rw [hs, div_mul_cancel₀ _ (hc i)]
  have e2 : (x i - o i) • l (e i) = s • ((m i : O) • l (e i)) := by
    rw [hxi, mul_smul, algebraMap_smul, algebraMap_smul]
  rw [e2]
  exact (hm i).smul s

section Coord

variable {K : Type} [Field K] (Δ : K)

private def pD : (Fin 4 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) (Lsq K Δ) where
  toFun x := !![⟨x 0, x 1⟩, ⟨x 2, x 3⟩; ⟨-x 2, x 3⟩, ⟨x 0, -x 1⟩]
  map_add' x y := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' c x := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp

private def qD : Matrix (Fin 2) (Fin 2) (Lsq K Δ) →ₗ[K] (Fin 4 → K) where
  toFun M := ![(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im]
  map_add' x y := by
    ext i; fin_cases i <;> simp
  map_smul' c x := by
    ext i; fin_cases i <;> simp

private theorem pD_apply (x : Fin 4 → K) : pD Δ x = !![⟨x 0, x 1⟩, ⟨x 2, x 3⟩; ⟨-x 2, x 3⟩, ⟨x 0, -x 1⟩] := rfl

private theorem qD_apply (M : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) :
    qD Δ M = ![(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im] := rfl

private def nD (x : Fin 4 → K) : K := x 0 ^ 2 - Δ * x 1 ^ 2 + x 2 ^ 2 - Δ * x 3 ^ 2

private theorem qp (x : Fin 4 → K) : qD Δ (pD Δ x) = x := by
  ext i; fin_cases i <;> simp [pD_apply, qD_apply]

private theorem pq_mul (x y : Fin 4 → K) : pD Δ (qD Δ (pD Δ x * pD Δ y)) = pD Δ x * pD Δ y := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [pD_apply, qD_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem p_one : pD Δ ![1, 0, 0, 0] = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [pD_apply, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem det_p (x : Fin 4 → K) : (pD Δ x).det = algebraMap K _ (nD Δ x) := by
  change _ = (⟨nD Δ x, 0⟩ : Lsq K Δ)
  ext <;> simp [pD_apply, nD, Matrix.det_fin_two] <;> ring

private theorem mem_iff_lemma (g : GL (Fin 2) (Lsq K Δ)) : g ∈ DX Δ ↔ (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map star = !![0, -1; 1, 0] * (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * !![0, 1; -1, 0] := by
  change GeneralLinearGroup.map (starRingEnd _) g = MulAut.conj (wJ Δ)⁻¹ g ↔ _
  rw [Units.ext_iff]
  simp [wJ, MulAut.conj_apply]
  rfl

private theorem map_star_eq_conj_iff_pD_qD_eq (M : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) : M.map star = !![0, -1; 1, 0] * M * !![0, 1; -1, 0] ↔ pD Δ (qD Δ M) = M := by
  constructor
  · intro h
    have e00 := congrFun (congrFun h 0) 0
    have e01 := congrFun (congrFun h 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, QuadraticAlgebra.ext_iff, Matrix.vecMul, dotProduct] at e00 e01
    obtain ⟨a1, a2⟩ := e00
    obtain ⟨b1, b2⟩ := e01
    ext i j : 2 <;> fin_cases i <;> fin_cases j <;> simp [pD_apply, qD_apply, a1, a2, b1, b2]
  · intro h
    rw [← h]
    ext i j : 2 <;> fin_cases i <;> fin_cases j <;> simp [pD_apply, qD_apply, Matrix.mul_apply, Fin.sum_univ_two]

private theorem mem_iff (g : GL (Fin 2) (Lsq K Δ)) : g ∈ DX Δ ↔ pD Δ (qD Δ g) = g := by
  rw [mem_iff_lemma, map_star_eq_conj_iff_pD_qD_eq]

private theorem pq_mt (g : DX Δ) : pD Δ (qD Δ (mt g)) = mt g := (mem_iff Δ g).1 g.2

private theorem isUnit_p (x : Fin 4 → K) : IsUnit (pD Δ x) ↔ nD Δ x ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, det_p]
  constructor
  · intro h h0
    rw [h0, map_zero] at h
    exact not_isUnit_zero h
  · intro h
    exact (IsUnit.mk0 _ h).map _

private theorem ex_mt (x : Fin 4 → K) (h : IsUnit (pD Δ x)) : ∃ g : DX Δ, mt g = pD Δ x := by
  refine ⟨⟨h.unit, (mem_iff Δ _).mpr ?_⟩, ?_⟩
  · rw [IsUnit.unit_spec, qp]
  · simp [mt]

private theorem p_map {K' : Type} [Field K'] (f : K →+* K') (x : Fin 4 → K) :
    (pD Δ x).map (lmap f Δ) = pD (f Δ) (fun i => f (x i)) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [pD_apply, lmap]

private theorem n_map {K' : Type} [Field K'] (f : K →+* K') (x : Fin 4 → K) :
    nD (f Δ) (fun i => f (x i)) = f (nD Δ x) := by
  simp [nD]

private theorem mem_KD (O : Type) [CommRing O] [Algebra O K] (g : DX Δ) (h : ∀ i j, IsIntegral O (mt g i j)) (a : O)
    (ha : (mt g).det * algebraMap O _ a = 1) : g ∈ KD Δ O := by
  rw [KD, Subgroup.mem_subgroupOf]
  let N : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) := fun i j => ⟨mt g i j, h i j⟩
  have hdet : IsUnit N.det := by
    refine IsUnit.of_mul_eq_one (algebraMap O _ a) ?_
    apply Subtype.ext
    have e := RingHom.map_det ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ) N
    simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_one]
    rw [← ha]
    congr 1
  refine ⟨((Matrix.isUnit_iff_isUnit_det N).mpr hdet).unit, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

end Coord

private theorem loc_open {K : Type} [NontriviallyNormedField K] [CompleteSpace K] [CharZero K] (O : Type) [CommRing O] [IsDomain O] [Algebra O K]
    [IsFractionRing O K] (hO : ∀ᶠ s in 𝓝 (0 : K), s ∈ (algebraMap O K).range) (Δ : K) (J : Subgroup (DX Δ))
    (hJ : J.relIndex (KD Δ O) ≠ 0) (g : DX Δ) :
    ∀ᶠ x in 𝓝 (qD Δ (mt g⁻¹)), ∃ j ∈ J, mt j = pD Δ x * mt g := by
  classical
  let J' := J.subgroupOf (KD Δ O)
  haveI : J'.FiniteIndex := ⟨hJ⟩
  have hm0 : J'.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpowJ : ∀ k ∈ KD Δ O, k ^ J'.normalCore.index ∈ J := by
    intro k hk
    have h1 := J'.normalCore.pow_index_mem ⟨k, hk⟩
    have h2 := J'.normalCore_le h1
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  let P : (Fin 4 → K) → Prop := fun y => ∃ k : DX Δ, k ∈ KD Δ O ∧ mt k = pD Δ y
  have hcont : Continuous (nD Δ) := by
    show Continuous (fun x : Fin 4 → K => x 0 ^ 2 - Δ * x 1 ^ 2 + x 2 ^ 2 - Δ * x 3 ^ 2)
    fun_prop
  have h1 : nD Δ ![1, 0, 0, 0] = 1 := by simp [nD]
  have hP : ∀ᶠ y in 𝓝 (![1, 0, 0, 0] : Fin 4 → K), P y := by
    have hent : ∀ i j, ∀ᶠ y in 𝓝 (![1, 0, 0, 0] : Fin 4 → K), IsIntegral O (pD Δ y i j) := by
      intro i j
      let l : (Fin 4 → K) →ₗ[K] Lsq K Δ :=
        { toFun := fun y => pD Δ y i j
          map_add' := by
            intro a b
            simp
          map_smul' := by
            intro c a
            simp }
      refine int_nhds O hO l _ ?_
      show IsIntegral O (pD Δ ![1, 0, 0, 0] i j)
      rw [p_one]
      by_cases hij : i = j
      · rw [hij, Matrix.one_apply_eq]
        exact isIntegral_one
      · simp [Matrix.one_apply, hij, isIntegral_zero]
    have ht : Tendsto (fun y => (nD Δ y)⁻¹ - 1) (𝓝 ![1, 0, 0, 0]) (𝓝 0) := by
      have h3 := ((hcont.tendsto ![1, 0, 0, 0]).inv₀ (by rw [h1]; exact one_ne_zero)).sub_const 1
      rwa [h1, inv_one, sub_self] at h3
    have hne : ∀ᶠ y in 𝓝 (![1, 0, 0, 0] : Fin 4 → K), nD Δ y ≠ 0 :=
      hcont.continuousAt.eventually_ne (by rw [h1]; exact one_ne_zero)
    filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hent i)), ht.eventually hO, hne] with y hy hy2 hy3
    obtain ⟨a0, ha0⟩ := hy2
    obtain ⟨g', hg'⟩ := ex_mt Δ y ((isUnit_p Δ y).mpr hy3)
    refine ⟨g', mem_KD Δ O g' (by rw [hg']; exact hy) (a0 + 1) ?_, hg'⟩
    rw [hg', det_p, IsScalarTower.algebraMap_apply O K (Lsq K Δ), map_add, map_one, ha0, sub_add_cancel, ← map_mul, mul_inv_cancel₀ hy3, map_one]
  have hpow := pow_nhds (pD Δ) (qD Δ) (qp Δ) (pq_mul Δ) ![1, 0, 0, 0] (p_one Δ) J'.normalCore.index (Nat.cast_ne_zero.mpr hm0) P hP
  have hT : Tendsto (fun x => qD Δ (pD Δ x * mt g)) (𝓝 (qD Δ (mt g⁻¹))) (𝓝 ![1, 0, 0, 0]) := by
    let T : (Fin 4 → K) →ₗ[K] (Fin 4 → K) := qD Δ ∘ₗ (LinearMap.mulRight K (mt g)) ∘ₗ pD Δ
    have hc : Continuous T := LinearMap.continuous_of_finiteDimensional T
    have h4 := hc.tendsto (qD Δ (mt g⁻¹))
    have e : T (qD Δ (mt g⁻¹)) = ![1, 0, 0, 0] := by
      simp only [T, LinearMap.comp_apply, LinearMap.mulRight_apply]
      rw [pq_mt]
      rw [show mt g⁻¹ * mt g = 1 by simp [mt], ← p_one Δ, qp]
    rw [e] at h4
    exact h4
  filter_upwards [hT.eventually hpow] with x hx
  obtain ⟨y, ⟨k, hk, hky⟩, hxy⟩ := hx
  refine ⟨k ^ J'.normalCore.index, hpowJ k hk, ?_⟩
  have e : pD Δ (qD Δ (pD Δ x * mt g)) = pD Δ x * mt g := by
    rw [← pq_mt Δ g]
    exact pq_mul Δ x _
  rw [← e, hxy, ← hky]
  simp [mt]

private theorem approx {F : Type} [Field F] [NumberField F] (S : Finset (Pl F)) (a : ∀ v : Pl F, Fin 4 → Kv v)
    (P : ∀ v : Pl F, (Fin 4 → Kv v) → Prop) (hP : ∀ v ∈ S, ∀ᶠ x in 𝓝 (a v), P v x) :
    ∃ x : Fin 4 → F, ∀ v ∈ S, P v fun i => cv v (x i) := by
  have h1 : DenseRange fun (x : F) (v : S) => cv v.1 x :=
    (Prod.fst_surjective.denseRange).comp (GroundTheory.Global.denseRange_algebraMap_prod_pi S ∅) continuous_fst
  have h2 := DenseRange.piMap (fun _ : Fin 4 => h1)
  have h3 : ∀ᶠ y : Fin 4 → ∀ v : S, Kv v.1 in 𝓝 fun i v => a v.1 i, ∀ v : S, P v.1 fun i => y i v := by
    refine eventually_all.2 fun v => ?_
    have hc : Continuous fun (y : Fin 4 → ∀ v : S, Kv v.1) i => y i v := by fun_prop
    exact (hc.tendsto _).eventually (hP v.1 v.2)
  obtain ⟨x, hx⟩ := h2.mem_nhds h3
  exact ⟨x, fun v hv => hx ⟨v, hv⟩⟩

private theorem loc_v {F : Type} [Field F] [NumberField F] (v : Pl F) (Δ : Kv v) (J : Subgroup (DX Δ))
    (hJ : J.relIndex (KD Δ (Ov v)) ≠ 0) (g : DX Δ) :
    ∀ᶠ x in 𝓝 (qD Δ (mt g⁻¹)), ∃ j ∈ J, mt j = pD Δ x * mt g := by
  letI : NontriviallyNormedField (Kv v) := Valued.toNontriviallyNormedField (Kv v) (WithZero (Multiplicative ℤ))
  haveI : CharZero (Kv v) := charZero_of_injective_algebraMap (algebraMap F (Kv v)).injective
  have hO : ∀ᶠ s in 𝓝 (0 : Kv v), s ∈ (algebraMap (Ov v) (Kv v)).range := by
    have ho : IsOpen ((HeightOneSpectrum.adicCompletionIntegers F v : Set (Kv v))) := Valued.isOpen_valuationSubring _
    filter_upwards [ho.mem_nhds (HeightOneSpectrum.adicCompletionIntegers F v).zero_mem] with s hs
    exact ⟨⟨s, hs⟩, rfl⟩
  exact loc_open (Ov v) hO Δ J hJ g

end UpperTheory.V.Z.Sym.Glob

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob in
theorem UpperTheory.V.Z.Sym.Glob.weakD :
    UpperTheory.V.Z.Sym.Glob.WeakD := by
  intro F _ _ Δ D hD ι hι g
  classical
  let gv : ∀ v : Pl F, DX (cv v Δ) := fun v => (g : ∀ v : Pl F, DX (cv v Δ)) v
  have hJ : ∀ v ∈ D.Sg, (D.J2v v).relIndex (KD (cv v Δ) (Ov v)) ≠ 0 := by
    intro v hv
    rw [Dat.J2v, if_pos hv]
    exact (hD.sig v hv).levelTwoFiniteIndex
  obtain ⟨x, hx⟩ := approx D.Sg (fun v => qD (cv v Δ) (mt (gv v)⁻¹))
    (fun v y => ∃ j ∈ D.J2v v, mt j = pD (cv v Δ) y * mt (gv v))
    (fun v hv => loc_v v (cv v Δ) (D.J2v v) (hJ v hv) (gv v))
  obtain ⟨v0, hv0⟩ := hD.ne
  have hn : nD Δ x ≠ 0 := by
    obtain ⟨j, -, hj⟩ := hx v0 hv0
    have hu : IsUnit (pD (cv v0 Δ) fun i => cv v0 (x i)) := by
      have h1 : IsUnit (mt j) := (j : GL (Fin 2) (Lsq (Kv v0) (cv v0 Δ))).isUnit
      rw [hj] at h1
      exact isUnit_of_mul_isUnit_left h1
    rw [isUnit_p, n_map] at hu
    intro h0
    exact hu (by rw [h0, map_zero])
  obtain ⟨γ, hγ⟩ := ex_mt Δ x ((isUnit_p Δ x).mpr hn)
  have hmt : ∀ v, mt ((ι γ : ∀ v : Pl F, DX (cv v Δ)) v) = pD (cv v Δ) (fun i => cv v (x i)) := by
    intro v
    rw [hι, hγ, p_map]
  have hmem : ∀ v ∈ D.Sg, (ι γ : ∀ v : Pl F, DX (cv v Δ)) v * gv v ∈ D.J2v v := by
    intro v hv
    obtain ⟨j, hj, hj'⟩ := hx v hv
    have e : (ι γ : ∀ v : Pl F, DX (cv v Δ)) v * gv v = j := by
      apply Subtype.ext
      apply Units.ext
      change mt _ * mt _ = mt j
      rw [hmt, hj']
    rw [e]
    exact hj
  let uf : ∀ v : Pl F, DX (cv v Δ) := fun v => if v ∈ D.Sg then ((ι γ : ∀ v : Pl F, DX (cv v Δ)) v * gv v)⁻¹ else 1
  have huf : uf ∈ RP (fun v : Pl F => DX (cv v Δ)) (fun v => KD (cv v Δ) (Ov v)) := by
    change ∀ᶠ v in Filter.cofinite, uf v ∈ KD (cv v Δ) (Ov v)
    rw [Filter.eventually_cofinite]
    refine D.Sg.finite_toSet.subset ?_
    intro v hv
    have hv2 : ¬ uf v ∈ KD (cv v Δ) (Ov v) := hv
    by_contra hv'
    apply hv2
    have e : uf v = 1 := if_neg hv'
    rw [e]
    exact (KD (cv v Δ) (Ov v)).one_mem
  refine ⟨γ, ⟨uf, huf⟩, ?_, ?_⟩
  · rw [Dat.U2, RPG.box, Subgroup.mem_iInf]
    intro v
    rw [Subgroup.mem_comap]
    change uf v ∈ D.J2v v
    by_cases hv : v ∈ D.Sg
    · have e : uf v = ((ι γ : ∀ v : Pl F, DX (cv v Δ)) v * gv v)⁻¹ := if_pos hv
      rw [e]
      exact inv_mem (hmem v hv)
    · have e : uf v = 1 := if_neg hv
      rw [e]
      exact (D.J2v v).one_mem
  · intro v hv
    change (ι γ : ∀ v : Pl F, DX (cv v Δ)) v * gv v * uf v = 1
    have e : uf v = ((ι γ : ∀ v : Pl F, DX (cv v Δ)) v * gv v)⁻¹ := if_pos hv
    rw [e]
    exact mul_inv_cancel _
end
end

section
open NumberField IsDedekindDomain Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open scoped nonZeroDivisors

private theorem reps {G Γ A C : Type} [Group G] [Group Γ] [CommGroup A] [Finite C] (ι : Γ →* G) (N : G →* A)
    (U K : Subgroup G) (Off : G → Prop) (hUK : U.relIndex K ≠ 0) (c : G → C)
    (hc : ∀ g g', c g = c g' → ∃ γ, ∃ k ∈ K, N g = N g' * N (ι γ) * N k)
    (hw : ∀ g, ∃ γ, ∃ u ∈ U, Off (ι γ * g * u)) :
    ∃ Y : Finset G, (∀ y ∈ Y, Off y) ∧ ∀ g, ∃ γ, ∃ s, N s = 1 ∧ ∃ y ∈ Y, ∃ u ∈ U, g = ι γ * s * y * u := by
  classical
  let H : Subgroup G := ((N.comp ι).range ⊔ U.map N).comap N
  haveI : H.Normal := Subgroup.Normal.comap inferInstance N
  have hUH : U ≤ H := fun u hu => Subgroup.mem_sup_right ⟨u, hu, rfl⟩
  have h1 : H.relIndex (H ⊔ K) ≠ 0 := by
    rw [Subgroup.relIndex_sup_left]
    exact fun h => hUK (Subgroup.relIndex_eq_zero_of_le_left hUH h)
  have h2 : Finite (G ⧸ (H ⊔ K)) := by
    refine Finite.of_injective (fun q : G ⧸ (H ⊔ K) => c q.out) fun p q h => ?_
    obtain ⟨γ, k, hk, e⟩ := hc _ _ h
    rw [← p.out_eq', ← q.out_eq', eq_comm, QuotientGroup.eq]
    have : q.out⁻¹ * p.out * k⁻¹ ∈ H := by
      refine Subgroup.mem_sup_left ⟨γ, ?_⟩
      simp only [MonoidHom.comp_apply, map_mul, map_inv, e]
      simp [mul_assoc]
    simpa using mul_mem (Subgroup.mem_sup_left this : _ ∈ H ⊔ K) (Subgroup.mem_sup_right hk)
  have h3 : H.index ≠ 0 := by
    rw [← Subgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ K)]
    exact mul_ne_zero h1 Subgroup.index_ne_zero_of_finite
  haveI := Subgroup.fintypeOfIndexNeZero h3
  choose γ u hu ho using hw
  refine ⟨Finset.univ.image fun q : G ⧸ H => ι (γ q.out) * q.out * u q.out, ?_, fun g => ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact ho _
  · set g' := (g : G ⧸ H).out with hg'
    have : g'⁻¹ * g ∈ H := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    obtain ⟨_, ⟨γ₁, rfl⟩, _, ⟨u₁, hu₁, rfl⟩, e⟩ := Subgroup.mem_sup.1 (Subgroup.mem_comap.1 this)
    have e' : N g = N g' * (N (ι γ₁) * N u₁) := by
      rw [MonoidHom.comp_apply] at e
      rw [e, map_mul, map_inv, mul_inv_cancel_left]
    refine ⟨γ₁ * (γ g')⁻¹, (ι (γ₁ * (γ g')⁻¹))⁻¹ * g * ((u g')⁻¹ * u₁)⁻¹ * (ι (γ g') * g' * u g')⁻¹, ?_,
      ι (γ g') * g' * u g', Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (u g')⁻¹ * u₁, mul_mem (inv_mem (hu _)) hu₁, by group⟩
    simp only [map_mul, map_inv, e']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel

private theorem box_idx {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)} (P : RPG G Gv K)
    (J : ∀ v, Subgroup (Gv v)) (S : Finset I) (h1 : ∀ v ∈ S, (J v).relIndex (K v) ≠ 0) (h2 : ∀ v ∉ S, K v ≤ J v) :
    (P.box J).relIndex (P.box K) ≠ 0 := by
  have h : (⨅ v : S, (J v).comap (P.p v)).relIndex (P.box K) ≠ 0 := by
    refine Subgroup.relIndex_iInf_ne_zero fun v h => h1 v v.2 ?_
    rw [Subgroup.relIndex_comap] at h
    exact Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_le_iff_le_comap.2 (iInf_le (fun w => (K w).comap (P.p w)) v.1)) h
  rw [← Subgroup.inf_relIndex_right] at h
  refine fun h' => h (Subgroup.relIndex_eq_zero_of_le_left (fun g hg => Subgroup.mem_iInf.2 fun v => ?_) h')
  by_cases hv : v ∈ S
  · exact Subgroup.mem_iInf.1 hg.1 ⟨v, hv⟩
  · exact h2 v hv (Subgroup.mem_iInf.1 hg.2 v)

private theorem narrow (F : Type) [Field F] [NumberField F] : ∃ (C : Type) (_ : Finite C) (c : (Pl F → ℤ) → C), ∀ n m,
    (∀ᶠ v in Filter.cofinite, n v = 0) → (∀ᶠ v in Filter.cofinite, m v = 0) → c n = c m →
    ∃ z : F, z ≠ 0 ∧ TPos z ∧ ∀ v : Pl F, n v = m v + WithZero.log (v.valuation F z) := by
  have h : ∀ I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ, ClassGroup.mk F I = ClassGroup.mk F J → ∃ z : F, z ≠ 0 ∧ ∀ v : Pl F,
      FractionalIdeal.count F v (I : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F) - WithZero.log (v.valuation F z) := by
    intro I J e
    have h1 : ClassGroup.mk F (I * J⁻¹) = 1 := by rw [map_mul, map_inv, e, mul_inv_cancel]
    obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h1)
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact Units.ne_zero _ (hx.trans FractionalIdeal.spanSingleton_zero)
    refine ⟨x, hx0, fun v => ?_⟩
    have := FractionalIdeal.count_mul F v (I * J⁻¹).ne_zero J.ne_zero
    rw [← Units.val_mul, inv_mul_cancel_right, hx, GroundTheory.Global.count_spanSingleton v hx0] at this
    omega
  let ρ : ClassGroup (𝓞 F) → (FractionalIdeal (𝓞 F)⁰ F)ˣ := Function.invFun (ClassGroup.mk F)
  have hρ : ∀ I, ClassGroup.mk F I = ClassGroup.mk F (ρ (ClassGroup.mk F I)) := fun I => (Function.invFun_eq ⟨I, rfl⟩).symm
  choose z hz hv using fun I => h I _ (hρ I)
  let J : (Pl F → ℤ) → (FractionalIdeal (𝓞 F)⁰ F)ˣ := fun n => ∏ᶠ w, GroundTheory.Global.primeIdealUnit w ^ n w
  refine ⟨ClassGroup (𝓞 F) × ((F →+* ℝ) → Prop), inferInstance, fun n => (ClassGroup.mk F (J n), fun σ => 0 < σ (z (J n))), ?_⟩
  intro n m hn hm e
  obtain ⟨e1, e2⟩ := Prod.ext_iff.1 e
  refine ⟨z (J m) / z (J n), div_ne_zero (hz _) (hz _), fun σ => ?_, fun v => ?_⟩
  · have e3 : 0 < σ (z (J n)) ↔ 0 < σ (z (J m)) := iff_of_eq (congrFun e2 σ)
    have a := (map_ne_zero σ).2 (hz (J n))
    have b := (map_ne_zero σ).2 (hz (J m))
    rw [map_div₀]
    rcases a.lt_or_gt with a | a
    · exact div_pos_of_neg_of_neg (b.lt_or_gt.resolve_right fun b => a.not_gt (e3.2 b)) a
    · exact div_pos (e3.1 a) a
  · have a := hv (J n) v
    have b := hv (J m) v
    rw [GroundTheory.Global.count_finprod_primeIdealUnit_zpow _ hn] at a
    rw [GroundTheory.Global.count_finprod_primeIdealUnit_zpow _ hm] at b
    dsimp only at e1
    rw [e1] at a
    rw [map_div₀, WithZero.log_div ((map_ne_zero _).2 (hz _)) ((map_ne_zero _).2 (hz _))]
    omega

section Loc

variable {K : Type} [Field K] {Δ : K}

private theorem det_eq [CharZero K] (g : DX Δ) : (mt g).det = algebraMap K _ (mt g).det.re := by
  have h : GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g.1 = (wJ Δ)⁻¹ * g.1 * (wJ Δ)⁻¹⁻¹ := g.2
  have h1 := congrArg (fun x => (GeneralLinearGroup.det x : Lsq K Δ)) h
  simp only [map_mul, map_inv, mul_right_comm _ (GeneralLinearGroup.det g.1), mul_inv_cancel, one_mul] at h1
  have h2 : star (mt g).det = (mt g).det := by
    rw [← starRingEnd_apply, RingHom.map_det]
    exact h1
  have h3 := congrArg QuadraticAlgebra.im h2
  rw [QuadraticAlgebra.im_star] at h3
  ext
  · simp
  · simpa using (self_eq_neg.1 h3.symm)

private theorem nrd_ex [CharZero K] (Δ : K) : ∃ N : DX Δ →* Kˣ, ∀ g : DX Δ, (Glob.mt g).det = algebraMap K _ (N g : K) := by
  let f : DX Δ →* K :=
    { toFun := fun g => (Glob.mt g).det.re
      map_one' := (congrArg QuadraticAlgebra.re (det_one (n := Fin 2) (R := Lsq K Δ))).trans QuadraticAlgebra.re_one
      map_mul' := fun a b => by
        have : (mt (a * b)).det = (mt a).det * (mt b).det := by rw [← det_mul]; rfl
        rw [this, det_eq a, det_eq b, ← map_mul]
        simp }
  exact ⟨f.toHomUnits, det_eq⟩

variable (O : Type) [CommRing O] [Algebra O K]

private theorem det_int {g : DX Δ} (h : g ∈ KD Δ O) : IsIntegral O (mt g).det := by
  obtain ⟨k, hk⟩ := h
  have : mt g = ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ).mapMatrix k.1 :=
    (congrArg Units.val hk).symm
  rw [this, ← RingHom.map_det]
  exact (k.1.det).2

private theorem star_int {x : Lsq K Δ} (h : IsIntegral O x) : IsIntegral O (star x) := by
  let f : Lsq K Δ →ₐ[O] Lsq K Δ := { starRingEnd (Lsq K Δ) with
    commutes' := fun r => by
      rw [Algebra.algebraMap_eq_smul_one]
      ext <;> simp [starRingEnd_apply, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] }
  exact h.map f

private theorem unit_ex (u : Oˣ) (ν : Lsq K Δ) (h : IsIntegral O ν) (e : QuadraticAlgebra.norm ν = algebraMap O K u) :
    ∃ k ∈ KD Δ O, (mt k).det = algebraMap K _ (algebraMap O K u) := by
  let R := integralClosure O (Lsq K Δ)
  let a : R := ⟨ν, h⟩
  let b : R := ⟨star ν, star_int O h⟩
  have e1 : ν * star ν = algebraMap K _ (algebraMap O K u) := by rw [← e, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  have e2 : a * b = algebraMap O R u := Subtype.ext (e1.trans (IsScalarTower.algebraMap_apply O K (Lsq K Δ) u).symm)
  have hu : IsUnit (!![a, 0; 0, b]).det := by
    rw [det_fin_two_of, mul_zero, sub_zero, e2]
    exact u.isUnit.map _
  let k : GL (Fin 2) R := GeneralLinearGroup.mk'' _ hu
  let g := GeneralLinearGroup.map (R.val : R →+* Lsq K Δ) k
  have hg : (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = !![ν, 0; 0, star ν] := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> rfl
  have hD : g ∈ DX Δ := by
    change GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g = (wJ Δ)⁻¹ * g * (wJ Δ)⁻¹⁻¹
    apply Units.ext
    change (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd _) = !![0, -1; 1, 0] * (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * !![0, 1; -1, 0]
    rw [hg]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [starRingEnd_apply]
  refine ⟨⟨g, hD⟩, ⟨k, rfl⟩, ?_⟩
  change (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).det = _
  rw [hg, det_fin_two_of, mul_zero, sub_zero, e1]

private theorem split_ex [CharZero K] (h0 : Δ ≠ 0) (h : IsSquare Δ) (u : Oˣ) :
    ∃ ν : Lsq K Δ, IsIntegral O ν ∧ QuadraticAlgebra.norm ν = algebraMap O K u := by
  obtain ⟨s, rfl⟩ := h
  have hs : s ≠ 0 := left_ne_zero_of_mul h0
  set x := algebraMap O K u with hx
  let ν : Lsq K (s * s) := ⟨(x + 1) / 2, (x - 1) / (2 * s)⟩
  refine ⟨ν, ⟨(Polynomial.X - Polynomial.C (u : O)) * (Polynomial.X - Polynomial.C 1),
    (Polynomial.monic_X_sub_C _).mul (Polynomial.monic_X_sub_C _), ?_⟩, ?_⟩
  · rw [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
      Polynomial.eval₂_C, IsScalarTower.algebraMap_apply O K (Lsq K (s * s)) u, map_one, ← hx]
    ext <;> simp [ν, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring
  · simp only [QuadraticAlgebra.norm_def, ν]
    field_simp
    ring

end Loc

section Place

variable {F : Type} [Field F] [NumberField F] {v : Pl F} {Δ : Kv v} {N : DX Δ →* (Kv v)ˣ}

private theorem val_one (hN : ∀ g : DX Δ, (Glob.mt g).det = algebraMap _ _ (N g : Kv v)) {g : DX Δ} (hg : g ∈ KD Δ (Ov v)) :
    Valued.v (N g : Kv v) = 1 := by
  have h : ∀ g ∈ KD Δ (Ov v), Valued.v (N g : Kv v) ≤ 1 := fun g hg => by
    have h1 := det_int (Ov v) hg
    rw [hN, isIntegral_algebraMap_iff QuadraticAlgebra.algebraMap_injective] at h1
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
    rw [← hy]
    exact y.2
  have h2 := h _ (inv_mem hg)
  rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (N g).ne_zero))] at h2
  exact le_antisymm (h g hg) h2

private theorem of_val_one (hN : ∀ g : DX Δ, (Glob.mt g).det = algebraMap _ _ (N g : Kv v))
    (h : ∀ u : (Ov v)ˣ, ∃ ν : Lsq (Kv v) Δ, IsIntegral (Ov v) ν ∧ QuadraticAlgebra.norm ν = algebraMap (Ov v) (Kv v) u)
    (x : (Kv v)ˣ) (hx : Valued.v (x : Kv v) = 1) : ∃ k ∈ KD Δ (Ov v), N k = x := by
  obtain ⟨u, hu⟩ := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one (a := (⟨x, hx.le⟩ : Ov v))).2 hx
  obtain ⟨ν, h1, h2⟩ := h u
  obtain ⟨k, hk, e⟩ := unit_ex (Ov v) u ν h1 h2
  refine ⟨k, hk, Units.ext ?_⟩
  rw [hN] at e
  rw [QuadraticAlgebra.algebraMap_injective e, hu]
  rfl

end Place

theorem UpperTheory.V.Z.Sym.Glob.classRep :
    UpperTheory.V.Z.Sym.Glob.ClassRep := by
  intro F _ _ Δ D hD ι hι
  have hΔ : Δ ≠ 0 := by
    haveI := hD.real
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    rintro rfl
    simpa using hD.neg (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
  haveI : ∀ v : Pl F, CharZero (Kv v) := fun v => charZero_of_injective_algebraMap (cv v).injective
  choose Nv hNv using fun v : Pl F => nrd_ex (cv v Δ)
  let P := rpg (fun v : Pl F => DX (cv v Δ)) fun v => KD (cv v Δ) (Ov v)
  let N : DA Δ →* ∀ v : Pl F, (Kv v)ˣ := Pi.monoidHom fun v => (Nv v).comp (P.p v)
  have hN : ∀ g v, N g v = Nv v (P.p v g) := fun _ _ => rfl
  obtain ⟨C, _, c, hc⟩ := narrow F
  have hae : ∀ g : DA Δ, ∀ᶠ v in Filter.cofinite, WithZero.log (Valued.v (N g v : Kv v)) = 0 := fun g =>
    (P.ae g).mono fun v hv => by rw [hN, val_one (hNv v) hv, WithZero.log_one]
  have hloc : ∀ (v : Pl F) (u : (Ov v)ˣ), ∃ ν : Lsq (Kv v) (cv v Δ), IsIntegral (Ov v) ν ∧
      QuadraticAlgebra.norm ν = algebraMap (Ov v) (Kv v) u := fun v u => by
    by_cases hv : v ∈ D.Sg
    · exact split_ex (Ov v) ((map_ne_zero _).2 hΔ) (hD.split v hv) u
    · exact normEx _ _ _ (hD.off v hv) u
  have hidx : D.U2.relIndex (P.box fun v => KD (cv v Δ) (Ov v)) ≠ 0 :=
    box_idx P D.J2v D.Sg (fun v hv => by rw [Dat.J2v, if_pos hv]; exact (hD.sig v hv).levelTwoFiniteIndex)
      fun v hv => by rw [Dat.J2v, if_neg hv]
  obtain ⟨Y, hY, h⟩ := reps ι N D.U2 _ D.Off hidx (fun g => c fun v => WithZero.log (Valued.v (N g v : Kv v)))
    (fun g g' e => by
      obtain ⟨z, hz, hp, e⟩ := hc _ _ (hae g) (hae g') e
      obtain ⟨γ, hγ⟩ := normD F Δ D hD z hp
      have h1 : ∀ v, (N (ι γ) v : Kv v) = cv v z := fun v => by
        apply QuadraticAlgebra.algebraMap_injective (a := cv v Δ) (b := 0)
        rw [hN, ← hNv]
        change (Glob.mt ((ι γ).1 v)).det = _
        rw [hι, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hγ]
        ext <;> simp [lmap]
      have h2 : ∀ v, Valued.v ((((N g' v * N (ι γ) v)⁻¹ * N g v : (Kv v)ˣ)) : Kv v) = 1 := fun v => by
        have a : ∀ x : (Kv v)ˣ, Valued.v (x : Kv v) ≠ 0 := fun x => (map_ne_zero _).2 x.ne_zero
        have b : Valued.v (cv v z) = v.valuation F z := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
        have d : Valued.v (N g v : Kv v) = Valued.v ((N g' v * N (ι γ) v : (Kv v)ˣ) : Kv v) := by
          rw [← WithZero.exp_log (a (N g v)), ← WithZero.exp_log (a (_ * _)), e v, Units.val_mul, map_mul,
            WithZero.log_mul (a _) (a _), h1, b]
        rw [Units.val_mul, map_mul, d, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
      choose k hk ek using fun v => of_val_one (hNv v) (hloc v) _ (h2 v)
      obtain ⟨k', hk'⟩ := P.surj k (Filter.Eventually.of_forall hk)
      refine ⟨γ, k', Subgroup.mem_iInf.2 fun v => ?_, funext fun v => ?_⟩
      · rw [Subgroup.mem_comap, hk']
        exact hk v
      · rw [Pi.mul_apply, Pi.mul_apply, hN k', hk', ek, mul_inv_cancel_left])
    (weakD F Δ D hD ι hι)
  refine ⟨Y, hY, fun g => ?_⟩
  obtain ⟨γ, s, hs, r⟩ := h g
  refine ⟨γ, s, Subgroup.mem_iInf.2 fun v => ?_, r⟩
  have h1 := hNv v (P.p v s)
  rw [← hN, hs, Pi.one_apply, Units.val_one, map_one] at h1
  exact Units.ext h1
end

section
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open MulAction Fib

private lemma normal_of_center {Γ : Type} [Group Γ] {A : Subgroup Γ} (h : A ≤ Subgroup.center Γ) : A.Normal := ⟨fun n hn g => by
  rw [Subgroup.mem_center_iff.mp (h hn) g, mul_inv_cancel_right]
  exact hn⟩

private lemma stab_mk {G : Type} [Group G] (U : Subgroup G) (g : G) :
    stabilizer G (g : G ⧸ U) = U.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_stabilizer_iff, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, MulAction.Quotient.smul_coe, eq_comm,
    QuotientGroup.eq]
  simp [mul_assoc]

private lemma triv_act {Γ G : Type} [Group Γ] [Group G] (ι : Γ →* G) (U : Subgroup G) (z : Γ)
    (h1 : ι z ∈ Subgroup.center G) (h2 : ι z ∈ U) (y : G ⧸ U) : ι z • y = y := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rw [MulAction.Quotient.smul_coe, QuotientGroup.eq, smul_eq_mul, ← Subgroup.mem_center_iff.mp h1 g]
  simpa [mul_assoc] using U.inv_mem h2

private theorem glue (hM : Master) (hTr : TrKer) (hPair : Pair)
    {Γ G : Type} [Group Γ] [Group G] (ι : Γ →* G) (S U U' : Subgroup G) (Γ₁ Γ₀ : Subgroup Γ) (ι₁ : Γ₁ →* S)
    (h1 : ∀ γ, (ι₁ γ : G) = ι γ) (h2 : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S) (h3 : Γ₁.Normal) (h4 : Γ₀ ≤ Subgroup.center Γ)
    (h5' : ∀ z ∈ Γ₀, ι z ∈ Subgroup.center G ∧ ι z ∈ U') (h6 : U ≤ U') (h7 : U.relIndex (U' ⊓ S) ≠ 0)
    (h8 : ∀ x : G, ∃ T : Finset S, ∀ s, ∃ h, ∃ t ∈ T, ∃ u : S, x⁻¹ * u * x ∈ U ∧ s = ι₁ h * t * u)
    (h9 : ∀ x : G, {h | x⁻¹ * ι₁ h * x ∈ U}.Finite)
    (h10 : ∃ T : Finset G, ∀ g, ∃ γ, ∃ s ∈ T, ∃ u ∈ U', g = ι γ * s * u)
    (h11' : ∀ g, Γ₀.relIndex ((U'.map (MulAut.conj g).toMonoidHom).comap ι) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (x : Fin (n + 1) → G),
      (∀ i j γ, ∀ s ∈ S, ∀ u ∈ U', x j = ι γ * s * x i * u → i = j) → (∀ g, ∃ i γ, ∃ s ∈ S, ∃ u ∈ U', g = ι γ * s * x i * u) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (f : G → ℂ) (B : Fin (n + 1) → Base Γ₁ S V)
        (cl : Γ → ℂ) (I : Type) (δ : I → Γ) (Hi : I → Type) [∀ i, Group (Hi i)] (φ : ∀ i, Hi i →* Γ),
      (∀ u ∈ U', ∀ g, f (u⁻¹ * g * u) = f g) → (∀ g, {γ : Γ₁ | f (g⁻¹ * ι γ * g) ≠ 0}.Finite) →
      (∀ i, (B i).ι = ι₁) → (∀ i (s : S), s ∈ (B i).U ↔ (x i)⁻¹ * s * x i ∈ U) → (∀ i, (B i).ω = 1) → (∀ i, (B i).Γ₀ = ⊥) →
      (∀ i, (B i).Fin) → (∀ i, (Base.Tw.one (B i)).IsTest fun g : S => f ((x i)⁻¹ * g * x i)) →
      (∀ h γ, cl (h * γ * h⁻¹) = cl γ) → (∀ g, cl g ≠ 0 → g ∈ Γ₁) → (∀ i (γ : Γ₁), LinearMap.trace ℂ V ((B i).W γ) = cl γ) →
      (∀ i x, x ∈ (φ i).range ↔ x * δ i = δ i * x) → (∀ i i' h, δ i' = h * δ i * h⁻¹ → i = i') →
      (∀ γ g, cl γ * f (g⁻¹ * ι γ * g) ≠ 0 → ∃ i h, γ = h * δ i * h⁻¹) →
      ∑ i, LinearMap.trace ℂ (B i).Forms ((Base.Tw.one (B i)).R fun g : S => f ((x i)⁻¹ * g * x i)) =
        c * ∑ᶠ i, cl (δ i) * gqOn (ι.comp (φ i)) (Γ₀.comap (φ i)) U' fun y => f (y.out⁻¹ * ι (δ i) * y.out) := by
  classical
  have hΓ₀n : Γ₀.Normal := normal_of_center h4
  have htriv : ∀ z ∈ Γ₀, ∀ y : G ⧸ U', ι z • y = y := fun z hz y =>
    triv_act ι U' z (h5' z hz).1 (h5' z hz).2 y
  have hstab : ∀ y : G ⧸ U', Γ₀.relIndex ((stabilizer G y).comap ι) ≠ 0 := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [stab_mk]
    exact h11' g
  obtain ⟨c, hc, hmain⟩ := hM Γ G ι S U U' Γ₁ Γ₀ ι₁ h1 h2 h3 hΓ₀n htriv h6 h7 h8 h9 h10 hstab
  refine ⟨c, hc, ?_⟩
  intro n x hdis hcov V _ _ _ f B cl I δ Hi _ φ hf hfin hBι hBU hω hΓ hBF hT hcl hcl1 htr hφ hδ hsupp
  let Φ : G → ℂ := fun g => ∑ᶠ γ : Γ, cl γ * f (g⁻¹ * ι γ * g)
  have hsub : ∀ g : G, ∑ᶠ γ : Γ₁, cl γ * f (g⁻¹ * ι γ * g) = Φ g := by
    intro g
    have hs : Function.support (fun γ => cl γ * f (g⁻¹ * ι γ * g)) ⊆ (Γ₁ : Set Γ) := by
      intro γ hγ
      exact hcl1 γ (left_ne_zero_of_mul hγ)
    show _ = ∑ᶠ γ : Γ, cl γ * f (g⁻¹ * ι γ * g)
    refine (finsum_set_coe_eq_finsum_mem (f := fun γ => cl γ * f (g⁻¹ * ι γ * g)) (Γ₁ : Set Γ)).trans ?_
    rw [finsum_mem_def, Set.indicator_eq_self.2 hs]
  have hΦl : ∀ (h : Γ) (g : G), Φ (ι h * g) = Φ g := by
    intro h g
    show ∑ᶠ γ : Γ, cl γ * f ((ι h * g)⁻¹ * ι γ * (ι h * g)) = ∑ᶠ γ : Γ, cl γ * f (g⁻¹ * ι γ * g)
    rw [← finsum_comp_equiv (MulAut.conj h).toEquiv]
    apply finsum_congr
    intro γ
    show cl (h * γ * h⁻¹) * f ((ι h * g)⁻¹ * ι (h * γ * h⁻¹) * (ι h * g)) = cl γ * f (g⁻¹ * ι γ * g)
    rw [hcl]
    congr 2
    simp only [map_mul, map_inv]
    group
  have hΦr : ∀ u ∈ U', ∀ g : G, Φ (g * u) = Φ g := by
    intro u hu g
    show ∑ᶠ γ : Γ, cl γ * f ((g * u)⁻¹ * ι γ * (g * u)) = ∑ᶠ γ : Γ, cl γ * f (g⁻¹ * ι γ * g)
    apply finsum_congr
    intro γ
    rw [← hf u hu (g⁻¹ * ι γ * g)]
    congr 2
    group
  have hM' := hmain (Fin (n + 1)) x (fun i => (B i).U) Φ hdis hcov hBU hΦl hΦr
  beta_reduce at hM'
  have hL : ∀ i, LinearMap.trace ℂ (B i).Forms ((Base.Tw.one (B i)).R fun g : S => f ((x i)⁻¹ * g * x i)) =
      gqOn ι₁ ⊥ (B i).U (fun s => Φ (↑(Quotient.out s) * x i)) := by
    intro i
    rw [hTr _ _ _ (B i) (hBF i) (hω i) (hΓ i) _ (hT i), hBι i]
    congr 1
    funext y
    rw [← hsub]
    apply finsum_congr
    intro γ
    rw [htr i γ]
    beta_reduce
    congr 2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, h1]
    group
  have hfinP : ∀ g : G, {γ | cl γ * f (g⁻¹ * ι γ * g) ≠ 0}.Finite := by
    intro g
    refine ((hfin g).image Subtype.val).subset ?_
    intro γ hγ
    have hγ1 := hcl1 γ (left_ne_zero_of_mul hγ)
    exact ⟨⟨γ, hγ1⟩, right_ne_zero_of_mul hγ, rfl⟩
  have hP := hPair Γ G I ι Γ₀ U' cl f δ Hi φ h4 htriv hcl hf hfinP h10 hstab hφ hδ hsupp
  rw [Finset.sum_congr rfl (fun i _ => hL i), hM']
  exact congrArg (fun z => (c : ℂ) * z) hP

end UpperTheory.V.Z.Sym.Glob

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc MulAction Fib

private lemma dx_ext {K : Type} [Field K] {Δ : K} {g g' : DX Δ} (h : mt g = mt g') : g = g' :=
  Subtype.ext (Units.ext h)

private lemma comm_abs {G A : Type} [Group G] [CommGroup A] (d : G →* A) (a b : G) : a * b * a⁻¹ * b⁻¹ ∈ d.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_right_comm (d a), mul_inv_cancel, one_mul,
    mul_inv_cancel]

private lemma comm_mem {F : Type} [Field F] [NumberField F] {Δ : F} (a b : DA Δ) : a * b * a⁻¹ * b⁻¹ ∈ SA Δ := by
  refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_comap.2 ?_
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  exact comm_abs (GeneralLinearGroup.det.comp (DX (cv v Δ)).subtype) _ _

private lemma trz {A : Type} [Group A] (g : A) : LinearMap.trace ℂ PUnit ((1 : Representation ℂ A PUnit) g) = 0 := by
  rw [Subsingleton.elim ((1 : Representation ℂ A PUnit) g) 0, map_zero]

section
variable {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ)

private lemma delta_ne (ok : D.Ok) : Δ ≠ 0 := by
  intro h0
  have w : NumberField.InfinitePlace F := Classical.arbitrary _
  have σ : F →+* ℝ := NumberField.InfinitePlace.embedding_of_isReal (ok.real.isReal w)
  have := ok.neg σ
  rw [h0, map_zero] at this
  exact lt_irrefl _ this

private lemma conK (bK : BaseK) (fK : FinK) (ok : D.Ok) (ι : DX Δ →* DA Δ) (hι : IsIotaD ι) :
    ZD Δ ≤ Subgroup.center (DX Δ) ∧ (∀ z ∈ ZD Δ, ι z ∈ Subgroup.center (DA Δ) ∧ ι z ∈ D.UZ) ∧
    (∃ T : Finset (DA Δ), ∀ g, ∃ γ, ∃ s ∈ T, ∃ u ∈ D.UZ, g = ι γ * s * u) ∧
    ∀ g, (ZD Δ).relIndex ((D.UZ.map (MulAut.conj g).toMonoidHom).comap ι) ≠ 0 := by
  obtain ⟨B, hB, -⟩ := bK F Δ D ok PUnit 1 0 (fun _ _ _ _ => Subsingleton.elim _ _) (fun g _ _ _ => trz g)
  have hF := (fK F Δ D ok PUnit 0 B hB).1
  have hBι : B.ι = ι := by
    ext γ : 1
    apply Subtype.ext
    funext v
    apply dx_ext
    rw [hB.ι γ v, hι γ v]
  have hU := hB.U
  have hΓ := hB.Γ₀
  refine ⟨?_, fun z hz => ?_, ?_, fun g => ?_⟩
  · have := B.cenΓ
    rwa [hΓ] at this
  · rw [← hΓ] at hz
    have h1 := B.cenG z hz
    have h2 := B.memU z hz
    rw [hBι] at h1 h2
    rw [hU] at h2
    exact ⟨h1, h2⟩
  · obtain ⟨T, hT⟩ := hF.cls
    refine ⟨T, fun g => ?_⟩
    have := hT g
    rwa [hU, hBι] at this
  · have := hF.stab g
    rwa [hU, hBι, hΓ] at this

private lemma bι {V : Type} [AddCommGroup V] [Module ℂ V] (ι : DX Δ →* DA Δ) (hι : IsIotaD ι) (ch : F → ℂ) (x : DA Δ)
    (B : Base (SU Δ) (SA Δ) V) (hB : D.IsBS ch x B) (γ : SU Δ) : ((B.ι γ : SA Δ) : DA Δ) = ι γ := by
  refine Subtype.ext (funext fun v => dx_ext ?_)
  rw [hB.ι, hι]

private lemma baseP (bS : BaseS) (ok : D.Ok) (x : DA Δ) : ∃ B : Base (SU Δ) (SA Δ) PUnit, D.IsBS 0 x B := by
  obtain ⟨B, hB, -⟩ := bS F Δ D ok PUnit 1 0 (fun γ _ _ => trz γ) x
  exact ⟨B, hB⟩

private lemma conS (bS : BaseS) (fS : FinS) (ok : D.Ok) (ι : DX Δ →* DA Δ) (hι : IsIotaD ι) :
    ∃ ι₁ : SU Δ →* SA Δ, (∀ γ, ((ι₁ γ : SA Δ) : DA Δ) = ι (γ : DX Δ)) ∧
    (∀ x : DA Δ, ∃ T : Finset (SA Δ), ∀ s, ∃ h, ∃ t ∈ T, ∃ u : SA Δ, x⁻¹ * u * x ∈ D.U2 ∧ s = ι₁ h * t * u) ∧
    ∀ x : DA Δ, {h : SU Δ | x⁻¹ * (ι₁ h : DA Δ) * x ∈ D.U2}.Finite := by
  obtain ⟨B0, hB0⟩ := baseP D bS ok 1
  have hι' : ∀ (x : DA Δ) (B : Base (SU Δ) (SA Δ) PUnit), D.IsBS 0 x B → B.ι = B0.ι := fun x B hB => by
    ext h : 1
    apply Subtype.ext
    rw [bι D ι hι 0 x B hB h, bι D ι hι 0 1 B0 hB0 h]
  refine ⟨B0.ι, fun γ => bι D ι hι 0 1 B0 hB0 γ, fun x => ?_, fun x => ?_⟩
  · obtain ⟨B, hB⟩ := baseP D bS ok x
    obtain ⟨T, hT⟩ := (fS F Δ D ok PUnit 0 x B hB).1.cls
    refine ⟨T, fun s => ?_⟩
    obtain ⟨h, t, ht, u, hu, rfl⟩ := hT s
    exact ⟨h, t, ht, u, (hB.U u).mp hu, by rw [hι' x B hB]⟩
  · obtain ⟨B, hB⟩ := baseP D bS ok x
    have hfin := (fS F Δ D ok PUnit 0 x B hB).1.stab 1
    rw [hB.Γ₀, Subgroup.relIndex_bot_left] at hfin
    have hK := Nat.finite_of_card_ne_zero hfin
    refine (Set.finite_coe_iff.mp hK).subset ?_
    intro h hh
    have hm : B.ι h ∈ B.U := by
      rw [hB.U, hι' x B hB]
      exact hh
    have he : (MulAut.conj (1 : SA Δ)).toMonoidHom (B.ι h) = B.ι h := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, one_mul, inv_one, mul_one]
    exact ⟨B.ι h, hm, he⟩

private lemma conN : (SA Δ).Normal := by
  unfold SA
  exact Subgroup.normal_iInf_normal fun v => Subgroup.Normal.comap (by unfold SU; infer_instance) _

private lemma conF (hSF : SuppFin) (bS : BaseS) (fS : FinS) (ok : D.Ok) (ι : DX Δ →* DA Δ) (hι : IsIotaD ι) (t : Dat.Par F)
    (ht : D.Cone t) (g : DA Δ) : {γ : SU Δ | D.FS t (g⁻¹ * ι γ * g) ≠ 0}.Finite := by
  obtain ⟨B, hB⟩ := baseP D bS ok g
  have h1 := fS F Δ D ok PUnit 0 g B hB
  have h2 := hSF _ _ _ B h1.1 hB.Γ₀ _ (h1.2 t ht) 1
  refine h2.subset ?_
  intro γ hγ
  simp only [Set.mem_setOf_eq, Dat.FSx, inv_one, mul_one, one_mul]
  rw [bι D ι hι 0 g B hB γ]
  exact hγ

private lemma clEx (hH : HasTrLaw) (ch : F → ℂ) : ∃ cl : DX Δ → ℂ, (∀ g s, HasTr g s → cl g = ch s) ∧ (∀ g, cl g ≠ 0 → g ∈ SU Δ) ∧
    ∀ h g, cl (h * g * h⁻¹) = cl g := by
  classical
  let cl : DX Δ → ℂ := fun g => if h : ∃ s, HasTr g s then ch h.choose else 0
  have key : ∀ g s, HasTr g s → cl g = ch s := by
    intro g s hs
    have he : ∃ s, HasTr g s := ⟨s, hs⟩
    show (if h : ∃ s, HasTr g s then ch h.choose else 0) = ch s
    rw [dif_pos he, (hH F Δ g).2.1 _ _ he.choose_spec hs]
  have zero : ∀ g, ¬ (∃ s, HasTr g s) → cl g = 0 := fun g he => dif_neg he
  refine ⟨cl, key, ?_, ?_⟩
  · intro g hg
    by_contra hn
    exact hg (zero g (fun he => hn ((hH F Δ g).1.mpr he)))
  · intro h g
    by_cases he : ∃ s, HasTr g s
    · obtain ⟨s, hs⟩ := he
      rw [key g s hs, key _ s (((hH F Δ g).2.2 h s).mpr hs)]
    · rw [zero g he, zero]
      rintro ⟨s, hs⟩
      exact he ⟨s, ((hH F Δ g).2.2 h s).mp hs⟩

end

set_option maxHeartbeats 3000000 in
private theorem fibre_of (hM : Master) (hTr : TrKer) (hSF : SuppFin) (hPair : Pair) (hReps : Reps) (hLev : LevFin) (hC : FSConj)
    (hSu : FSSupp) (hH : HasTrLaw) (bS : BaseS) (bK : BaseK) (fS : FinS) (fK : FinK) (cR : ClassRep) (eA : EmbAlg) : Fibre := by
  intro F _ _ Δ D ok ι hι x₀ hx₀
  have hΔ := delta_ne D ok
  obtain ⟨hU, hr⟩ := hLev F Δ D ok
  obtain ⟨hZ, hZt, hcls, hstab⟩ := conK D bK fK ok ι hι
  obtain ⟨ι₁, hι₁, hSc, hSf⟩ := conS D bS fS ok ι hι
  have hN1 : (SU Δ).Normal := MonoidHom.normal_ker _
  obtain ⟨c, hc, hall⟩ := glue hM hTr hPair ι (SA Δ) D.U2 D.UZ (SU Δ) (ZD Δ) ι₁ hι₁ comm_mem hN1 hZ hZt hU hr hSc hSf hcls hstab
  obtain ⟨Y, hY, hYc⟩ := cR F Δ D ok ι hι
  obtain ⟨n, x, hx0, hxY, hsep, hcov⟩ := hReps (DX Δ) (DA Δ) ι (SA Δ) D.UZ Y x₀ conN (fun g => by
    obtain ⟨γ, s, hs, y, hy, u, hu, e⟩ := hYc g
    exact ⟨γ, s, hs, y, hy, u, hU hu, e⟩)
  refine ⟨n, x, c, hx0, fun i => ?_, hc, ?_⟩
  · rcases hxY i with h | h
    · rw [h]; exact hx₀
    · exact hY _ h
  intro V _ _ _ ch B hB t ht I τ γ j hinj hi hcv
  obtain ⟨cl, hcl, hcl0, hclc⟩ := clEx hH ch
  have hE := fun i => eA F Δ (τ i) hΔ (hi i).1 (γ i) (hi i).2.1
  have key := hall n x hsep hcov V (D.FS t) B cl I γ (fun i => (Etau F (τ i))ˣ) j
    (fun u hu g => hC F Δ D ok t ht u hu g) (fun g => conF D hSF bS fS ok ι hι t ht g)
    (fun i => by
      ext1 γ'
      exact Subtype.ext ((bι D ι hι ch (x i) (B i) (hB i) γ').trans (hι₁ γ').symm))
    (fun i => (hB i).U) (fun i => (hB i).ω) (fun i => (hB i).Γ₀) (fun i => (fS F Δ D ok V ch (x i) (B i) (hB i)).1)
    (fun i => (fS F Δ D ok V ch (x i) (B i) (hB i)).2 t ht) hclc hcl0
    (fun i γ' => by
      obtain ⟨s, hs⟩ := (hH F Δ γ').1.1 γ'.2
      rw [(hB i).tr γ' s hs, hcl _ s hs])
    (fun i y => ((hE i).2.1 (j i) (hi i).2.2).2.1 y)
    (fun i i' h e => by
      have h1 : HasTr (γ i) (τ i') := ((hH F Δ (γ i)).2.2 h _).1 (e ▸ (hi i').2.1)
      exact hinj ((hH F Δ (γ i)).2.1 _ _ (hi i).2.1 h1))
    (fun γ' g hne => by
      obtain ⟨s, hs⟩ := (hH F Δ γ').1.1 (hcl0 γ' (left_ne_zero_of_mul hne))
      obtain ⟨i, rfl⟩ := hcv γ' s hs (hSu F Δ D ok ι hι t ht γ' s g hs (right_ne_zero_of_mul hne))
      obtain ⟨y, hy⟩ := (hE i).2.2 γ' hs
      exact ⟨i, y⁻¹, by rw [hy, inv_inv]⟩)
  refine key.trans (congrArg _ (finsum_congr fun i => ?_))
  rw [hcl _ _ (hi i).2.1, ((hE i).2.1 (j i) (hi i).2.2).2.2]

end UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Glob.fibre :
    UpperTheory.V.Z.Sym.Glob.Fibre :=
  UpperTheory.V.Z.Sym.Glob.fibre_of UpperTheory.symmetric_fiber_master_formula UpperTheory.symmetric_fiber_trace_kernel UpperTheory.orbitalFiber_support_finite UpperTheory.orbitalFiber_pair_correspondence UpperTheory.orbitalFiber_representatives
    UpperTheory.orbitalFiber_level_finite UpperTheory.orbitalFiber_fixedSet_conj UpperTheory.orbitalFiber_fixedSet_support UpperTheory.orbitalFiber_hasTraceLaw UpperTheory.V.Z.Sym.Glob.baseS UpperTheory.V.Z.Sym.Glob.baseK
    UpperTheory.V.Z.Sym.Glob.finS UpperTheory.V.Z.Sym.Glob.finK UpperTheory.V.Z.Sym.Glob.classRep UpperTheory.V.Z.Sym.Glob.embAlg
end
end
