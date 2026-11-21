import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.GaloisPeriodCyclotomic
import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.BaseThetaVanishing.BaseThZero
import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.BaseAinfPlus
import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.ExistsBeta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
import Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.LocTied6
import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.BaseFixed

section
noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst PfDRPst Matrix

section cont

variable {l : ℕ} [Fact l.Prime]

local notation "φi" => RingEquiv.symm (_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[l]) l) l)

theorem exists_coe_eq_untilt_pFlat (m : ℕ) : ∃ z : PadicAlgCl l,
    (z : ℂ_[l]) = ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) := by
  have hN : l ^ m ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (l : PadicAlgCl l) (Nat.pos_of_ne_zero hN)
  have hπ : ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) ^ l ^ m = (l : ℂ_[l]) := by
    rw [← SubmonoidClass.coe_pow, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow, coe_untilt_pFlat]
  have hyl : algebraMap (PadicAlgCl l) ℂ_[l] y ^ l ^ m = (l : ℂ_[l]) := by
    rw [← map_pow, hy, map_natCast]
  have hy0 : algebraMap (PadicAlgCl l) ℂ_[l] y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hN] at hyl
    exact natCast_p_ne_zero_cp (p := l) hyl.symm
  obtain ⟨w, hw⟩ := exists_coe_eq_of_pow_eq_one hN
    (x := ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) * (algebraMap (PadicAlgCl l) ℂ_[l] y)⁻¹)
    (by rw [mul_pow, inv_pow, hπ, hyl, mul_inv_cancel₀ (natCast_p_ne_zero_cp (p := l))])
  refine ⟨y * w, ?_⟩
  change algebraMap (PadicAlgCl l) ℂ_[l] (y * w) = _
  rw [map_mul, show algebraMap (PadicAlgCl l) ℂ_[l] w = _ from hw, mul_comm, mul_assoc, inv_mul_cancel₀ hy0,
    mul_one]

theorem toZModPow_kummerC_eq (m : ℕ) {g h : GQ l} {z : PadicAlgCl l}
    (hz : (z : ℂ_[l]) = ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l])) (hgh : h z = g z) :
    PadicInt.toZModPow m (kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot h)) =
      PadicInt.toZModPow m (kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot g)) := by
  have e : ∀ σ : GQ l, (toBot σ) • ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) =
      ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) *
        ((PreTilt.untilt (φi^[m] (epsilon l)) : normInteger ℂ_[l]) : ℂ_[l]) ^
          (PadicInt.toZModPow m (kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one
            (toBot σ))).val := fun σ =>
    gal_smul_untilt_iterate_of_eq_mul untilt_epsilon
      (tiltGal_eq_mul_epsPow untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one pFlat_ne_zero
        gal_smul_coe_untilt_pFlat (toBot σ)) m
  have hs : ∀ σ : GQ l, (toBot σ) • ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) =
      ((σ z : PadicAlgCl l) : ℂ_[l]) := fun σ => by
    rw [← hz, ← galCp_apply, galCp_coe]
    rfl
  have hπ0 : ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) ≠ 0 := by
    intro h0
    have hπ : ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) ^ l ^ m = (l : ℂ_[l]) := by
      rw [← SubmonoidClass.coe_pow, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow, coe_untilt_pFlat]
    rw [h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hπ
    exact natCast_p_ne_zero_cp (p := l) hπ.symm
  have h2 := (e h).symm.trans ((hs h).trans (hgh ▸ (hs g).symm |>.trans (e g)))
  have h3 := mul_left_cancel₀ hπ0 h2
  have hprim : IsPrimitiveRoot ((PreTilt.untilt (φi^[m] (epsilon l)) : normInteger ℂ_[l]) : ℂ_[l]) (l ^ m) :=
    IsPrimitiveRoot.coe_submonoidClass_iff.2
      (isPrimitiveRoot_untilt_iterate untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one m)
  exact ZMod.val_injective _ (hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3)

end cont

theorem continuous_κ (l : ℕ) [Fact l.Prime] : Continuous (κ : GQ l → ℚ_[l]) := by
  have hc : Continuous fun g : GQ l =>
      kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot g) := by
    refine continuous_iff_continuousAt.2 fun g0 => Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt : (1 : ℝ) < l))
    obtain ⟨z, hz⟩ := exists_coe_eq_untilt_pFlat (l := l) m
    have : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {z}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
    have hU : IsOpen {h : GQ l | g0⁻¹ * h ∈ (IntermediateField.adjoin ℚ_[l] {z}).fixingSubgroup} :=
      (IntermediateField.fixingSubgroup_isOpen _).preimage (continuous_const_mul _)
    have h1 : g0 ∈ {h : GQ l | g0⁻¹ * h ∈ (IntermediateField.adjoin ℚ_[l] {z}).fixingSubgroup} := by
      simp only [Set.mem_setOf_eq, inv_mul_cancel]
      exact Subgroup.one_mem _
    filter_upwards [hU.mem_nhds h1] with h hh
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh z (IntermediateField.mem_adjoin_simple_self _ _)
    have hgh : h z = g0 z := by
      have := congrArg g0 hfix
      simpa using this
    have e := toZModPow_kummerC_eq m hz hgh
    rw [dist_eq_norm]
    have hmem : kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot h) -
        kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot g0) ∈
          Ideal.span {(l : ℤ_[l]) ^ m} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, e, sub_self]
    calc _ ≤ (l : ℝ) ^ (-(m : ℤ)) := (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 hmem
      _ = (l : ℝ)⁻¹ ^ m := by rw [_root_.zpow_neg, zpow_natCast, inv_pow]
      _ < ε := hm
  exact continuous_subtype_val.comp hc

end period_ring_base
end
end

section
noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst PfDRPst Matrix

theorem base_κ_cont (l : ℕ) [Fact l.Prime] : Continuous (κ : GQ l → ℚ_[l]) := continuous_κ l

theorem base_no_kummer (l : ℕ) [Fact l.Prime] : ∀ L : Fld l, FiniteDimensional ℚ_[l] L → ∀ x : B l,
    ¬ ∀ σ ∈ L.fixingSubgroup, σB σ x - x = qB l (κ σ) * t l := by
  intro L hL x h
  obtain ⟨P, AI, ⟨T0⟩⟩ := GlobalTheory.MemLoc.exists_locPrime_tied l
  obtain ⟨T⟩ := UpperTheory.Lit.Cmp.locTied6 l P AI ⟨T0⟩
  obtain ⟨β, hβ⟩ := UpperTheory.Lit.Drps.exists_beta T
  have := GlobalTheory.Pst.nontrivial_B P
  refine GlobalTheory.Pst.StLat.kummer_not_frac l P AI T0 ⟨L, hL⟩ 1 (T.eB.symm (x + qB l β * t l)) one_ne_zero fun g hg => ?_
  apply T.eB.injective
  rw [map_one, one_mul, one_mul, one_mul, one_mul, map_sub, DualB.tie_σB T, RingEquiv.apply_symm_apply, hβ, map_add,
    ← h g hg]
  ring

end period_ring_base
end
end

section
noncomputable section

namespace period_ring_base

theorem base : PeriodRingBase := fun l _ =>
  { dom := base_dom l
    ι_inj := base_ι_inj l
    σ_one := base_σ_one l
    σ_mul := base_σ_mul l
    σD_one := base_σD_one l
    σD_mul := base_σD_mul l
    σC_one := base_σC_one l
    σC_mul := base_σC_mul l
    φ_σ := base_φ_σ l
    ι_σ := base_ι_σ l
    φ_q := base_φ_q l
    σ_q := base_σ_q l
    ι_q := base_ι_q l
    ι_t := period_image_eq l
    t_unit := base_t_unit l
    frobenius_period := frobenius_period_holds l
    galois_t_transform := galois_period_cyclotomic l
    σ_u := base_σ_u l
    κ_mul := base_κ_mul l
    κ_cont := base_κ_cont l
    χ_cont := base_χ_cont l
    ι_Bst := base_ι_Bst l
    u_Bst := base_u_Bst l
    plus_σ := base_plus_σ l
    th_σ := base_th_σ l
    th_add := base_th_add l
    th_mul := base_th_mul l
    th_q := base_th_q l
    th_zero := base_th_zero l
    t_plus := base_t_plus l
    val := base_val l
    orbit := base_orbit l
    fs_ker := base_fs_ker l
    fs_surj := base_fs_surj l
    ainf_φ := base_ainf_φ l
    ainf_σ := base_ainf_σ l
    ainf_plus := base_ainf_plus l
    ainf_eig := base_ainf_eig l
    fixed := base_fixed' l
    no_kummer := base_no_kummer l }

end period_ring_base
end
end
