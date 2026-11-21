import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharacterTameStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharacterUnitValueStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameUniformizerPowerStatement

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChiTameUnit

theorem exists_int_cong_tg : ∀ (D : D7) (k : Fin 2) (v : D.nd.PlG k), ∃ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), u ∉ (D.naut.plGw k v).asIdeal ∧ ∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1 := by
  intro D k v
  set w := D.naut.plGw k v with hw
  set A := D.nd.plOm.1 w with hAdef
  have hA : IsPlaceOver A w := D.nd.plOm.2 w
  have : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  have hp : (D.host.g k).Prime := D.host.g_prime k
  have hN : normV w = D.host.g k := GlobalTheory.TameLabels.normV_eq_of_split hp (D.nd.g_split k) (D.naut.plGw_over k v)
  have hgw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := D.naut.plGw_over k v
  have hn : 0 < normV w - 1 := by rw [hN]; have := hp.two_le; omega
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt
    (Ideal.pow_lt_self w.asIdeal w.ne_bot w.isPrime.ne_top 2 le_rfl)
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap D.host.E D.nd.Om (ϖ : D.host.E)) hn
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have h0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne', eq_comm, map_eq_zero] at hπ
    exact hϖ0 (by simpa using hπ)
  set ζ := D.ntypes.tg k v π / π with hζ
  have hζn : ζ ^ (normV w - 1) = 1 := by
    rw [hζ, div_pow, ← map_pow, hπ, AlgEquiv.commutes, ← hπ, div_self (pow_ne_zero _ h0)]
  have hv1 : A.valuation ζ = 1 := by
    refine pow_left_injective hn.ne' ?_
    show _ ^ _ = 1 ^ _
    rw [← map_pow, hζn, map_one, one_pow]

  have hζA : ζ ∈ A := (A.valuation_le_one_iff ζ).mp hv1.le
  haveI hcp : CharP (IsLocalRing.ResidueField A) (D.host.g k) := by
    refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    have := (hA _).mpr hgw
    simpa using this
  haveI : Fact (D.host.g k).Prime := ⟨hp⟩
  set z := IsLocalRing.residue A ⟨ζ, hζA⟩ with hz
  have hzp : z ^ (D.host.g k) - z = 0 := by
    have e : (⟨ζ, hζA⟩ : A) ^ (normV w - 1) = 1 := Subtype.ext (by simpa using hζn)
    have e2 : z ^ (normV w - 1) = 1 := by rw [hz, ← map_pow, e, map_one]
    rw [hN] at e2
    have : z ^ (D.host.g k) = z := by
      rw [← Nat.sub_add_cancel hp.one_lt.le, pow_succ, e2, one_mul]
    rw [this, sub_self]
  have hmon : (X ^ (D.host.g k) - X : (ZMod (D.host.g k))[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hp.one_lt)
  have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod (D.host.g k))
  rw [ZMod.card] at hroots
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by
    rw [hroots, FiniteField.X_pow_card_sub_X_natDegree_eq _ hp.one_lt, Finset.card_val, Finset.card_univ,
      ZMod.card])
  have hev := congrArg (fun P => (P.map (ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField A))).eval z) hprod
  simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_pow, eval_multiset_prod, Multiset.map_map, eval_sub, eval_X, eval_C, eval_pow, hzp] at hev
  obtain ⟨a, -, hy0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hev)

  have hcong : A.valuation (ζ - ((a.val : ℕ) : D.nd.Om)) < 1 := by
    have : (⟨ζ, hζA⟩ : A) - ((a.val : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hz, map_natCast, ZMod.natCast_val]
      simpa using hy0
    rw [ValuationSubring.valuation_lt_one_iff] at this
    simpa [-ZMod.natCast_val] using this
  have hu : ((a.val : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro hm
    have h3 := (hA _).mpr hm
    simp only [map_natCast] at h3
    have h4 := Valuation.map_add_lt _ hcong h3
    rw [sub_add_cancel, hv1] at h4
    exact lt_irrefl _ h4
  refine ⟨((a.val : ℕ) : 𝓞 D.host.E), ?_, hu, ϖ, π, h1, h2, hπ, ?_⟩
  · intro h
    apply hu
    have : ((a.val : ℕ) : 𝓞 D.host.E) = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  · have e : algebraMap D.host.E D.nd.Om (((a.val : ℕ) : 𝓞 D.host.E) : D.host.E) = ((a.val : ℕ) : D.nd.Om) := by
      simp only [RingOfIntegers.coe_eq_algebraMap, map_natCast]
    rw [e]
    exact hcong

end GlobalTheory.ChiTameUnit

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalInteger_congr_tameGenerator_character : ∀ (D : D7) (k : Fin 2) (v : D.nd.PlG k), ∃ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), u ∉ (D.naut.plGw k v).asIdeal ∧ ∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1 := by
  atlas_forward_decl GlobalTheory.ChiTameUnit.exists_int_cong_tg
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.PendOf.tame_lab_mu : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ChiTOk D P.cf → ∀ S : Reading P.T, IsTrue P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu ∧ ∃ (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), (u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹) ∧ labAt hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) := by
  intro hP hDZ hL D P hchi S hS i k v hw
  obtain ⟨u, hu0, hunit, hrep⟩ := GlobalTheory.T.exists_globalInteger_congr_tameGenerator_character D k v
  have hrep' : NX.TameRep (D.naut.plGw k v) 1 (D.ntypes.tg k v) u := by
    obtain ⟨ϖ, π, h1, h2, h3, h4⟩ := hrep
    exact ⟨D.nd.plOm.1 (D.naut.plGw k v), D.nd.plOm.2 (D.naut.plGw k v), D.ntypes.tg_mem k v, ϖ, π, h1, h2, h3,
      by rw [zpow_one]; exact h4⟩
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  obtain ⟨c, hc, hcv⟩ := hchi k v j u hu0 hrep'
  have htame := GlobalTheory.T.split_character_tame hL D P S hS i k v hw
  refine ⟨htame, (S i _ hw).mu_ok.1, c, hc, GlobalTheory.T.tame_uniformizer_power hDZ hL D P.ty.grp k v _ _ htame u hu0 hrep c ?_⟩
  rw [GlobalTheory.T.split_character_unit_value hL D P S hS i k v hw j (by simp only [j]; omega) u hu0 hunit]
  exact hcv.symm
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_character_label : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ChiTOk D P.cf → ∀ S : Reading P.T, IsTrue P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu ∧ ∃ (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), (u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹) ∧ labAt hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) := by
  atlas_forward_decl GlobalTheory.PendOf.tame_lab_mu
end
