import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AutomorphicArithmetic.BlochKatoExtensions.PhtCmp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIsoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalArtinHasNormGroups
import GroundTheory.LocalFields.Existence
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharCompatibilities
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimitiveStrandComplementLefschetz
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneWeightSpaceStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightFiltrationStrandDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TemperedWeightSpaceBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneDirectSumOfCompl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TemperedOfTemperedLpSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TemperedTopWeightStrand
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenspaceLeEigenspacePow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPurePairIffMonodromyFiltration
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonodromyFreeSumIrreducibles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealExponentAbsSmoothCharacterLocalField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecUniqueOfLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIsoStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleWdEigenEqualNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedSpecialOfUnitEigen
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedDirectSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharacterEigenProduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSegmentsLanglands
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionRealSubfieldRingEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoPreservesValuation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormVZpowDegEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneRelUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaCellDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCellOfUnipotentIwahoriProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RankinSelbergTestFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubsingletonJacquetIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemStdMaxParabolicOfBlockParabolicLeConj
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasSatGLLocRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyMemFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousChiDet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousSplitCentre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MapSingleAtEmb
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient

section
noncomputable section

open ValuativeRel

namespace GlobalTheory.CongruenceSubgroupIndex

section Defs

variable {K : Type} [Field K] [ValuativeRel K]

theorem valuation_eq_one_of_sub_one_lt {γ : ValueGroupWithZero K} (hγ : γ ≤ 1) {y : K}
    (hy : valuation K (y - 1) < γ) : valuation K y = 1 := by
  have h : valuation K (y - 1) < 1 := hy.trans_le hγ
  simpa using (valuation K).map_one_add_of_lt h

def f0 {K : Type} [Field K] [ValuativeRel K] (γ : ValueGroupWithZero K) (hγ : γ ≤ 1) (h0 : γ ≠ 0) :
    Subgroup Kˣ where
  carrier := {x | valuation K ((x : K) - 1) < γ}
  one_mem' := by simpa using zero_lt_iff.2 h0
  mul_mem' := by
    intro a b ha hb
    have ha' : valuation K ((a : K) - 1) < γ := ha
    have hb' : valuation K ((b : K) - 1) < γ := hb
    have h1 := valuation_eq_one_of_sub_one_lt hγ ha'
    show valuation K (((a * b : Kˣ) : K) - 1) < γ
    have e : ((a * b : Kˣ) : K) - 1 = (a : K) * ((b : K) - 1) + ((a : K) - 1) := by
      rw [Units.val_mul]; ring
    rw [e]
    refine (valuation K).map_add_lt ?_ ha'
    rw [map_mul, h1, one_mul]
    exact hb'
  inv_mem' := by
    intro a ha
    have ha' : valuation K ((a : K) - 1) < γ := ha
    have h1 := valuation_eq_one_of_sub_one_lt hγ ha'
    show valuation K (((a⁻¹ : Kˣ) : K) - 1) < γ
    have e : ((a⁻¹ : Kˣ) : K) - 1 = -((a : K)⁻¹ * ((a : K) - 1)) := by
      rw [Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ a.ne_zero]; ring
    rw [e, Valuation.map_neg, map_mul, map_inv₀, h1, inv_one, one_mul]
    exact ha'

end Defs

section Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem isOpen_ball {γ : ValueGroupWithZero K} (h0 : γ ≠ 0) :
    IsOpen {y : K | valuation K y < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ h0, fun z hz => ?_⟩
  have hz' : valuation K (z - y) < γ := hz
  have : valuation K ((z - y) + y) < γ := (valuation K).map_add_lt hz' hy
  simpa using this

theorem isOpen_congruence_subgroup (γ : ValueGroupWithZero K) (hγ : γ ≤ 1) (h0 : γ ≠ 0) :
    IsOpen (f0 γ hγ h0 : Set Kˣ) :=
  (isOpen_ball h0).preimage (f := fun x : Kˣ => (x : K) - 1)
    (Units.continuous_val.sub continuous_const)

theorem isCompact_units : IsCompact {x : Kˣ | valuation K (x : K) = 1} := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have e : ((↑) : Kˣ → K) '' {x : Kˣ | valuation K (x : K) = 1} =
      {y : K | valuation K y ≤ 1} \ {y : K | valuation K y < 1} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : valuation K (x : K) = 1 := hx
      simp [hx']
    · rintro ⟨h1, h2⟩
      have h : valuation K y = 1 := le_antisymm h1 (not_lt.1 h2)
      have hy : y ≠ 0 := by
        rintro rfl
        simp at h
      exact ⟨Units.mk0 y hy, h, rfl⟩
  rw [e]
  exact (IsNonarchimedeanLocalField.isCompact_closedBall K 1).diff (isOpen_ball one_ne_zero)

theorem valuation_div_zpow {x : Kˣ} (hx : GlobalTheory.SmGL.ord K x = 1) (y : Kˣ) :
    valuation K ((y / x ^ GlobalTheory.SmGL.ord K y : Kˣ) : K) = 1 := by
  let o : Kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun z => .ofAdd (GlobalTheory.SmGL.ord K z)) fun a b => by
    rw [GlobalTheory.SmGL.ord_mul, ofAdd_add]
  have h1 : o (y / x ^ GlobalTheory.SmGL.ord K y) = 1 := by
    rw [map_div, map_zpow, show o x = .ofAdd 1 from congrArg Multiplicative.ofAdd hx, ← ofAdd_zsmul,
      smul_eq_mul, mul_one]
    exact div_self' _
  exact GlobalTheory.SmGL.ord_eq_zero_iff.1 (ofAdd_eq_one.1 h1)

theorem finiteIndex_of_isOpen {H : Subgroup Kˣ} (hH : IsOpen (H : Set Kˣ)) {x : Kˣ}
    (hx : GlobalTheory.SmGL.ord K x = 1) (hxH : x ∈ H) : H.FiniteIndex := by
  haveI : DiscreteTopology (Kˣ ⧸ H) := QuotientGroup.discreteTopology hH
  have hc := (isCompact_units (K := K)).image (QuotientGroup.continuous_mk (N := H))
  have hu : ((↑) : Kˣ → Kˣ ⧸ H) '' {x : Kˣ | valuation K (x : K) = 1} = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨y / x ^ GlobalTheory.SmGL.ord K y, valuation_div_zpow hx y, ?_⟩
    rw [QuotientGroup.eq]
    have : (y / x ^ GlobalTheory.SmGL.ord K y)⁻¹ * y = x ^ GlobalTheory.SmGL.ord K y := by
      rw [inv_div, div_mul_cancel]
    rw [this]
    exact H.zpow_mem hxH _
  rw [hu] at hc
  haveI : Finite (Kˣ ⧸ H) := Set.finite_univ_iff.1 hc.finite_of_discrete
  exact Subgroup.finiteIndex_of_finite_quotient

theorem finiteIndex_zpowers_sup_congruence (γ : ValueGroupWithZero K) (hγ : γ ≤ 1) (h0 : γ ≠ 0) {x : Kˣ}
    (hx : GlobalTheory.SmGL.ord K x = 1) : (Subgroup.zpowers x ⊔ f0 γ hγ h0).FiniteIndex :=
  finiteIndex_of_isOpen (Subgroup.isOpen_mono le_sup_right (isOpen_congruence_subgroup γ hγ h0)) hx
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))

end Local

theorem main : ∃ f0 : {K : Type} → [inst : Field K] → [inst_1 : ValuativeRel K] →
      (γ : ValuativeRel.ValueGroupWithZero K) → γ ≤ (1 : ValuativeRel.ValueGroupWithZero K) →
      γ ≠ (0 : ValuativeRel.ValueGroupWithZero K) → Subgroup Kˣ,
    (∀ {K : Type} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
      [IsNonarchimedeanLocalField K] (γ : ValuativeRel.ValueGroupWithZero K)
      (hγ : γ ≤ (1 : ValuativeRel.ValueGroupWithZero K))
      (h0 : γ ≠ (0 : ValuativeRel.ValueGroupWithZero K)), IsOpen (↑(f0 γ hγ h0) : Set Kˣ)) ∧
    (∀ {K : Type} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
      [inst_3 : IsNonarchimedeanLocalField K] (γ : ValuativeRel.ValueGroupWithZero K)
      (hγ : γ ≤ (1 : ValuativeRel.ValueGroupWithZero K))
      (h0 : γ ≠ (0 : ValuativeRel.ValueGroupWithZero K)) {x : Kˣ}, GlobalTheory.SmGL.ord K x = (1 : ℤ) →
      Subgroup.FiniteIndex (Subgroup.zpowers x ⊔ f0 γ hγ h0)) :=
  ⟨@f0, fun γ hγ h0 => isOpen_congruence_subgroup γ hγ h0,
    fun γ hγ h0 _ hx => finiteIndex_zpowers_sup_congruence γ hγ h0 hx⟩

end GlobalTheory.CongruenceSubgroupIndex

end
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands

namespace GlobalTheory.WeilDeligne.LowTempered

theorem norm_eq_of_mem_absSpace {V : Type} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (r : ℝ) (β : ℂ) (v : V) (hv0 : v ≠ 0)
    (hr : v ∈ absSpace f r) (hβ : f v = β • v) : ‖β‖ = r := by
  by_contra hne
  have hind := (iSupIndep_absSpace f (r := id) Function.injective_id).pairwiseDisjoint hne
  have h1 : v ∈ absSpace f ‖β‖ := by
    have : v ∈ f.eigenspace β := Module.End.mem_eigenspace_iff.2 hβ
    exact (le_iSup₂ (f := fun (α : ℂ) (_ : ‖α‖ = ‖β‖) => f.eigenspace α) β rfl) this
  exact hv0 ((Submodule.disjoint_def.1 hind) v h1 hr)

theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (m : ℕ) (hS : ∀ σ, ∀ v ∈ wtSpace a (-(m : ℤ)), a.ρ σ v ∈ wtSpace a (-(m : ℤ))), ((WD.mk (restrictρ a _ hS)).lpTw ((m : ℝ) / 2)).mono0 ∧ ∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((WD.mk (restrictρ a _ hS)).lpTw ((m : ℝ) / 2)).eig φ, ‖α‖ = 1 := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a m hS
  refine ⟨?_, ?_⟩
  · rw [WD.lpTw_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff]
    simp [WDRep.tw, WDRep.twist_N, restrictρ_N]
  · intro φ hφ α hα
    rw [WD.lpTw_mk, WD.eig_mk] at hα
    set b := restrictρ a _ hS with hb
    have hroot : Module.End.HasEigenvalue ((b.tw ((m : ℝ) / 2)).ρ φ) α :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (Polynomial.isRoot_of_mem_roots hα)
    obtain ⟨v, hv⟩ := hroot.exists_hasEigenvector
    have hfv := Module.End.mem_eigenspace_iff.1 hv.1
    set c : ℂ := (normV w : ℂ) ^ (((m : ℝ) / 2 : ℝ) : ℂ) with hc
    have hq : (0 : ℕ) < normV w := lt_trans one_pos (one_lt_normV w)
    have hcn : ‖c‖ = (normV w : ℝ) ^ ((m : ℝ) / 2) := by
      rw [hc, Complex.norm_natCast_cpow_of_pos hq]; simp
    have hc0 : c ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hcn
      exact (Real.rpow_pos_of_pos (by exact_mod_cast hq) _).ne' hcn.symm
    have htw : (b.tw ((m : ℝ) / 2)).ρ φ = c • b.ρ φ := by
      simp only [WDRep.tw, WDRep.twist_ρ]
      congr 1
      simp [unrChar, qPow, hφ, hc]
    rw [htw] at hfv
    have hfv' : a.ρ φ (v : V) = (α / c) • (v : V) := by
      have := congrArg (fun x : (wtSpace a (-(m : ℤ))) => (x : V)) hfv
      simp only [LinearMap.smul_apply, Submodule.coe_smul, hb, restrictρ_ρ_apply] at this
      rw [div_eq_inv_mul, mul_smul, ← this, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hmem : (v : V) ∈ absSpace (a.ρ φ) ((normV w : ℝ) ^ (((-(m : ℤ) : ℤ) : ℝ) / 2)) := by
      rw [absSpace_eq_of_deg_eq E Ω A w h V a φ (frob h) (hφ.trans deg_frob.symm)]
      exact v.2
    have hv0 : (v : V) ≠ 0 := by
      intro h0; exact hv.2 (Subtype.ext h0)
    have hn := norm_eq_of_mem_absSpace _ _ _ _ hv0 hmem hfv'
    have hα' : α = (α / c) * c := by field_simp
    rw [hα', norm_mul, hn, hcn, ← Real.rpow_add (by exact_mod_cast hq)]
    push_cast
    ring_nf
    simp

end GlobalTheory.WeilDeligne.LowTempered
end

section
namespace GlobalTheory.IsolatedTheoremTwo

theorem main : ∀ {s : Multiset ℂ}, (∀ x ∈ s, ‖x‖ = (1 : ℝ)) → ‖Multiset.prod s‖ = (1 : ℝ) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a s ih =>
    intro h
    rw [Multiset.prod_cons, norm_mul, h a (Multiset.mem_cons_self a s),
      ih (fun x hx => h x (Multiset.mem_cons_of_mem hx)), one_mul]

end GlobalTheory.IsolatedTheoremTwo
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.column_twisted_args_first : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.ChevalleyUnits → GlobalTheory.Published.BrauerDegreeZero → GlobalTheory.Published.LocalConverseGL → GlobalTheory.Published.LanglandsExhaustionGL → GlobalTheory.Published.StandardCosocleGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.HeightCounting.LpCmp hL := by
  intro _ _ _ _ _ _ _ _ _ _
  exact ⟨⟨⟩⟩
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.column_twisted_args_second : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.CuspidalSpectrumGL → GlobalTheory.HeightCounting.CgCmp hL := by
  intro _ _ _ _ _ _ _
  exact ⟨⟨⟩⟩
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.ArchFromLit

theorem archCmp_of_lit : LitLoc → LitAut → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ArchCmp hL := by
  intro hLoc hAut hL
  exact
    { pht := GlobalTheory.PhtCompare.phtCmp
      lp := GlobalTheory.T.column_twisted_args_first hAut.art hLoc.chev hLoc.brauer hLoc.conv hLoc.exh hLoc.cos hLoc.bz hL
      cg := GlobalTheory.T.column_twisted_args_second hL hAut.fin hAut.js.1 hAut.cusp }

end GlobalTheory.ArchFromLit
end
