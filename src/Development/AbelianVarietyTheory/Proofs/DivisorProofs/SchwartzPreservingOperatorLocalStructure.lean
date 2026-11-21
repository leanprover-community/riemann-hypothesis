import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepPureTensorLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorMemSchwartzAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourier
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenProportionalLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeInvariantVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFunctionFactorizableSum

section
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.FinComm.Surj

variable {F : Type} [Field F] [NumberField F]

noncomputable def adAt (v : Pl F) (a : Fv F v) : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v a)

theorem evFin_adAt_self (v : Pl F) (a : Fv F v) : evFin F v (adAt v a) = a := by
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (sndA F (adAt v a)) = a
  exact evalV_singleFin_self v a

theorem mul_adAt_eq_zero (v : Pl F) (a : Fv F v) {u : AF F} (hu : evFin F v u = 0) : u * adAt v a = 0 := by
  have h2 : u.2 * singleFin v a = 0 := by
    apply af_ext
    intro t
    rw [map_mul, map_zero]
    by_cases h : t = v
    · subst h
      have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F t u.2 = 0 := hu
      rw [this, zero_mul]
    · rw [evalV_singleFin_ne h, mul_zero]
  exact Prod.ext (mul_zero _) h2

end GlobalTheory.FinComm.Surj

open GlobalTheory.FinComm.Surj in
theorem GlobalTheory.FinComm.exists_At_locPt_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (v : Pl F)
    (p : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    ∃ w : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) w ∧ GlobalTheory.FinComm.locPt v (M.co.e w) = p := by
  refine ⟨M.co.e.symm (fun i => adAt v (p.1 i), fun i => adAt v (p.2 i)), ?_, ?_⟩
  · intro u hu
    rw [← map_smul]
    convert M.co.e.symm.map_zero using 2
    ext i
    · exact mul_adAt_eq_zero v _ hu
    · exact mul_adAt_eq_zero v _ hu
  · rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext (funext fun i => evFin_adAt_self v _) (funext fun i => evFin_adAt_self v _)
end

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_point_model_eval : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (v : Pl F)
    (p : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)),
    ∃ w : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) w ∧ GlobalTheory.FinComm.locPt v (M.co.e w) = p := by
  atlas_forward_decl GlobalTheory.FinComm.exists_At_locPt_eq
end

section
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.PsiLocal

variable {F : Type} [Field F] [NumberField F]

theorem exists_not_mem_localInvDifferent (v : Pl F) :
    ∃ x : Fv F v, x ∉ GroundTheory.Global.localInvDifferent v := by
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hy0' : algebraMap (𝓞 F) F y ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have ht0' : algebraMap (𝓞 F) F t ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  refine ⟨((algebraMap (𝓞 F) F y * algebraMap (𝓞 F) F t)⁻¹ : F), fun h => ?_⟩
  have h1 := (GroundTheory.Global.coe_mem_localInvDifferent_iff v _).1 h y hy
  have e : (algebraMap (𝓞 F) F y * algebraMap (𝓞 F) F t)⁻¹ * algebraMap (𝓞 F) F y =
      (algebraMap (𝓞 F) F t)⁻¹ := by
    field_simp
  rw [e, map_inv₀] at h1
  have hlt : v.valuation F (algebraMap (𝓞 F) F t) < 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_lt_one_iff_mem t).2 ht
  have hne : v.valuation F (algebraMap (𝓞 F) F t) ≠ 0 := by
    rwa [ne_eq, map_eq_zero]
  have := one_lt_inv_iff₀.2 ⟨zero_lt_iff.2 hne, hlt⟩
  exact absurd h1 (not_le.2 this)

theorem psi_loc_main : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl F,
    Continuous (psiLoc ψ v) ∧ ∃ x : Fv F v, psiLoc ψ v x ≠ 1 := by
  intro F _ _ ψ hψ v
  have hval : ∀ x, psiLoc ψ v x = (GroundTheory.Global.localAdelicChar F v x : ℂ) := by
    intro x
    show ψ (GroundTheory.Global.finitePlaceIncl v x) = _
    exact GlobalTheory.AdelicSvN.Weyl.isStd_eq hψ _
  refine ⟨?_, ?_⟩
  · exact hψ.1.comp (continuous_const.prodMk (continuous_singleFin v))
  · by_contra hc
    push_neg at hc
    have h1 : ∀ x, GroundTheory.Global.localAdelicChar F v x = 1 := fun x => by
      have := hc x
      rw [hval] at this
      exact Circle.ext (by simpa using this)
    obtain ⟨x, hx⟩ := exists_not_mem_localInvDifferent v
    exact hx ((GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff v x).1 fun a _ => h1 _)

end GlobalTheory.PsiLocal
end

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_char_continuous_nontrivial : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl F,
    Continuous (psiLoc ψ v) ∧ ∃ x : Fv F v, psiLoc ψ v x ≠ 1 := by
  atlas_forward_decl GlobalTheory.PsiLocal.psi_loc_main
end

section
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.SchrCyclic

variable {F : Type} [Field F] [NumberField F]

theorem psiLoc_add (ψ : AddChar (AF F) ℂ) (v : Pl F) (a b : Fv F v) :
    psiLoc ψ v (a + b) = psiLoc ψ v a * psiLoc ψ v b := by
  rw [psiLoc, psiLoc, psiLoc, map_add, map_add]; exact AddChar.map_add_eq_mul ψ _ _

theorem psiLoc_zero (ψ : AddChar (AF F) ℂ) (v : Pl F) : psiLoc ψ v 0 = 1 := by
  rw [psiLoc, map_zero, map_zero]; exact AddChar.map_zero_eq_one ψ

theorem mem_of_sep {V Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    (e : Y → V → ℂ) (he : ∀ y a b, e y (a + b) = e y a * e y b)
    (S : Submodule ℂ (V → ℂ)) (hS : ∀ y, ∀ h ∈ S, (fun x => e y x * h x) ∈ S)
    (U : AddSubgroup V) (hU : IsOpen (U : Set V))
    (hsep : ∀ x ∉ U, ∃ y, (∀ u ∈ U, e y u = 1) ∧ e y x ≠ 1)
    {f : V → ℂ} (hf : f ∈ S) (hfc : HasCompactSupport f) :
    (fun x => if x ∈ U then f x else 0) ∈ S := by
  classical
  by_cases hY : Nonempty Y
  swap
  · have hall : ∀ x, x ∈ U := fun x => by
      by_contra h
      obtain ⟨y, -⟩ := hsep x h
      exact hY ⟨y⟩
    convert hf using 1
    funext x
    simp [hall x]
  have := QuotientAddGroup.discreteTopology hU
  have hfin : ((QuotientAddGroup.mk : V → V ⧸ U) '' tsupport f).Finite :=
    (hfc.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  have hsep' : ∀ q : V ⧸ U, ∃ y, q ≠ 0 → (∀ u ∈ U, e y u = 1) ∧ e y q.out ≠ 1 := by
    intro q
    by_cases hq : q = 0
    · exact ⟨Classical.arbitrary _, fun h => (h hq).elim⟩
    · have : q.out ∉ U := fun h => hq (by rw [← QuotientAddGroup.out_eq' q]; exact (QuotientAddGroup.eq_zero_iff _).2 h)
      obtain ⟨y, hy⟩ := hsep _ this
      exact ⟨y, fun _ => hy⟩
  choose y hy using hsep'
  set c : V ⧸ U → ℂ := fun q => e (y q) q.out with hcdef
  set Q := hfin.toFinset.filter (· ≠ 0) with hQ
  have key : ∀ s : Finset (V ⧸ U), (fun x => (∏ q ∈ s, (e (y q) x - c q) / (1 - c q)) * f x) ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hf
    | insert q s hq ih =>
      have h2 := hS (y q) _ ih
      have : (fun x => (∏ r ∈ insert q s, (e (y r) x - c r) / (1 - c r)) * f x) =
          (1 - c q)⁻¹ • (fun x => e (y q) x * ((∏ r ∈ s, (e (y r) x - c r) / (1 - c r)) * f x)) +
          (-(c q) * (1 - c q)⁻¹) • (fun x => (∏ r ∈ s, (e (y r) x - c r) / (1 - c r)) * f x) := by
        funext x
        simp only [Finset.prod_insert hq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [this]
      exact S.add_mem (S.smul_mem _ h2) (S.smul_mem _ ih)
  convert key Q using 1
  funext x
  by_cases hx : x ∈ tsupport f
  · by_cases hxU : x ∈ U
    · rw [if_pos hxU, Finset.prod_eq_one, one_mul]
      intro q hq
      have hq0 : q ≠ 0 := (Finset.mem_filter.1 hq).2
      rw [(hy q hq0).1 x hxU, div_self (sub_ne_zero.2 (Ne.symm (hy q hq0).2))]
    · have hq0 : (QuotientAddGroup.mk x : V ⧸ U) ≠ 0 := fun h => hxU ((QuotientAddGroup.eq_zero_iff _).1 h)
      rw [if_neg hxU, Finset.prod_eq_zero (i := (QuotientAddGroup.mk x : V ⧸ U)), zero_mul]
      · exact Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ⟨x, hx, rfl⟩, hq0⟩
      · have hw : -(QuotientAddGroup.mk x : V ⧸ U).out + x ∈ U :=
          QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
        have : e (y (QuotientAddGroup.mk x)) x = c (QuotientAddGroup.mk x) := by
          have h5 : e (y (QuotientAddGroup.mk x)) ((QuotientAddGroup.mk x : V ⧸ U).out +
              (-(QuotientAddGroup.mk x : V ⧸ U).out + x)) = e (y (QuotientAddGroup.mk x)) (QuotientAddGroup.mk x : V ⧸ U).out := by
            rw [he, (hy _ hq0).1 _ hw, mul_one]
          rw [add_neg_cancel_left] at h5
          exact h5
        rw [this, sub_self, zero_div]
  · rw [image_eq_zero_of_notMem_tsupport hx]
    simp

theorem exists_periodic {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    (hB : ∀ N ∈ 𝓝 (0 : V), ∃ W : AddSubgroup V, IsOpen (W : Set V) ∧ (W : Set V) ⊆ N)
    {φ : V → ℂ} (hφ : IsLocallyConstant φ) (hc : HasCompactSupport φ) :
    ∃ N ∈ 𝓝 (0 : V), ∀ W : AddSubgroup V, (W : Set V) ⊆ N → ∀ x, ∀ w ∈ W, φ (x + w) = φ x := by
  classical
  have hK : IsCompact (tsupport φ) := hc
  have hloc : ∀ z : V, ∃ W : AddSubgroup V, IsOpen (W : Set V) ∧ ∀ w ∈ W, φ (z + w) = φ z := by
    intro z
    have ho : IsOpen {u : V | φ (z + u) = φ z} :=
      (hφ.comp_continuous (continuous_const.add continuous_id)).isOpen_fiber (φ z)
    obtain ⟨W, hWo, hWs⟩ := hB _ (ho.mem_nhds (by simp))
    exact ⟨W, hWo, fun w hw => hWs hw⟩
  choose W hWo hW using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z => (fun x => -z + x) ⁻¹' (W z : Set V))
    (fun z => (hWo z).preimage (continuous_const.add continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [(W x).zero_mem]⟩)
  refine ⟨⋂ z ∈ t, (W z : Set V), (Filter.biInter_finset_mem t).2 fun z _ => (hWo z).mem_nhds (W z).zero_mem,
    fun W' hW' => ?_⟩
  have hin : ∀ x ∈ tsupport φ, ∀ w ∈ W', φ (x + w) = φ x := by
    intro x hx w hw
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 (ht hx)
    have hwz : w ∈ W z := Set.mem_iInter₂.1 (hW' hw) z hz
    have hxz' : -z + x ∈ W z := hxz
    have e1 := hW z _ ((W z).add_mem hxz' hwz)
    have e2 := hW z _ hxz'
    rw [← add_assoc, add_neg_cancel_left] at e1
    rw [add_neg_cancel_left] at e2
    rw [e1, e2]
  intro x w hw
  by_cases hx : x ∈ tsupport φ
  · exact hin x hx w hw
  · by_cases hxw : x + w ∈ tsupport φ
    · have := hin _ hxw (-w) (W'.neg_mem hw)
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxw]

theorem eq_one_of_pow_near {u : ℂ} (hu : ∀ n : ℕ, ‖u ^ n - 1‖ < 1 / 2) : u = 1 := by
  have key : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖u - 1‖ ≤ ‖u ^ 2 ^ k - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : u ^ 2 ^ (k + 1) - 1 = (u ^ 2 ^ k - 1) * (2 + (u ^ 2 ^ k - 1)) := by rw [pow_succ, pow_mul]; ring
      have h2 : (3 / 2 : ℝ) ≤ ‖2 + (u ^ 2 ^ k - 1)‖ := by
        have := norm_sub_norm_le (2 : ℂ) (-(u ^ 2 ^ k - 1))
        rw [norm_neg, sub_neg_eq_add, Complex.norm_two] at this
        linarith [hu (2 ^ k)]
      rw [h1, norm_mul, pow_succ, mul_right_comm]
      exact mul_le_mul ih h2 (by norm_num) (norm_nonneg _)
  by_contra hne
  have hpos : 0 < ‖u - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖u - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ hpos] at hk
  linarith [key k, hu (2 ^ k)]

theorem exists_cond (ψ : AddChar (AF F) ℂ) (v : Pl F) (hc : Continuous (psiLoc ψ v))
    (hn : ∃ x : Fv F v, psiLoc ψ v x ≠ 1) :
    ∃ z : Fv F v, psiLoc ψ v z ≠ 1 ∧ ∀ s : Fv F v, Valued.v s < Valued.v z → psiLoc ψ v s = 1 := by
  classical
  let χA : AddChar (Fv F v) ℂ :=
    { toFun := psiLoc ψ v, map_zero_eq_one' := psiLoc_zero ψ v, map_add_eq_mul' := psiLoc_add ψ v }
  have hsmall : ∃ N ∈ 𝓝 (0 : Fv F v), ∀ s ∈ N, psiLoc ψ v s = 1 := by
    have hc' : Continuous fun s => ‖psiLoc ψ v s - 1‖ := by fun_prop
    have h1 : {s : Fv F v | ‖psiLoc ψ v s - 1‖ < 1 / 2} ∈ 𝓝 0 :=
      (isOpen_lt hc' continuous_const).mem_nhds (by simp [psiLoc_zero])
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 h1
    refine ⟨{x | (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict x < γ},
      (Valued.isClopen_ball _ _).isOpen.mem_nhds (by simp [zero_lt_iff]), fun s hs => ?_⟩
    have hn : ∀ n : ℕ, (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict (n • s) < γ := by
      intro n
      induction n with
      | zero => simp [zero_lt_iff]
      | succ n ih =>
        rw [succ_nsmul]
        exact Valuation.map_add_lt _ ih hs
    refine eq_one_of_pow_near fun n => ?_
    rw [show psiLoc ψ v s ^ n = psiLoc ψ v (n • s) from (AddChar.map_nsmul_eq_pow χA n s).symm]
    exact hγ (hn n)
  obtain ⟨N, hN, hNχ⟩ := hsmall
  have hopen : IsOpen {s : Fv F v | psiLoc ψ v s = 1} := by
    refine isOpen_iff_mem_nhds.2 fun s hs => ?_
    rw [← map_add_left_nhds_zero]
    exact Filter.mem_map.2 (Filter.mem_of_superset hN fun u hu => by
      show psiLoc ψ v (s + u) = 1
      rw [psiLoc_add, show psiLoc ψ v s = 1 from hs, hNχ u hu, one_mul])
  obtain ⟨w, hw⟩ := hn
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hw (psiLoc_zero ψ v)
  have hball : IsCompact {s : Fv F v | Valued.v s ≤ Valued.v w} := by
    have : {s : Fv F v | Valued.v s ≤ Valued.v w} =
        (fun o => w * o) '' (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext s
      constructor
      · intro hs
        refine ⟨s / w, ?_, by field_simp⟩
        rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
        exact div_le_one_of_le₀ hs zero_le'
      · rintro ⟨o, ho, rfl⟩
        show Valued.v (w * o) ≤ Valued.v w
        rw [map_mul]
        exact mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ho)
    rw [this]
    exact (isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)).image
      (continuous_mul_left w)
  set C := {s : Fv F v | Valued.v s ≤ Valued.v w} ∩ {s | psiLoc ψ v s ≠ 1} with hC
  have hCc : IsCompact C := hball.inter_right (show IsClosed {s : Fv F v | psiLoc ψ v s ≠ 1} from hopen.isClosed_compl)
  have hloc : ∀ s ∈ C, {t : Fv F v | Valued.v t = Valued.v s} ∈ 𝓝 s := by
    intro s hs
    have hs0 : s ≠ 0 := fun h => hs.2 (h ▸ psiLoc_zero ψ v)
    have hr : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict s ≠ 0 :=
      (Valuation.ne_zero_iff _).2 hs0
    refine Valued.mem_nhds.2 ⟨Units.mk0 _ hr, fun t ht => ?_⟩
    have h1 : Valued.v (t - s) < Valued.v s := (Valuation.restrict_lt_iff _).1 ht
    exact Valuation.map_eq_of_sub_lt _ h1
  obtain ⟨t, htC, hcov⟩ := hCc.elim_nhds_subcover _ hloc
  have hwC : w ∈ C := ⟨show Valued.v w ≤ Valued.v w from le_rfl, hw⟩
  have htne : t.Nonempty := by
    obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.1 (hcov hwC)
    exact ⟨x, hx⟩
  obtain ⟨z, hzt, hzmin⟩ := t.exists_min_image (fun x => Valued.v x) htne
  refine ⟨z, (htC z hzt).2, fun s hs => ?_⟩
  by_contra hχs
  by_cases hsw : Valued.v s ≤ Valued.v w
  · obtain ⟨x, hx, hsx⟩ := Set.mem_iUnion₂.1 (hcov ⟨hsw, hχs⟩)
    have h1 : Valued.v z ≤ Valued.v x := hzmin x hx
    have h2 : Valued.v s = Valued.v x := hsx
    rw [← h2] at h1
    exact absurd hs (not_lt.2 h1)
  · exact hsw (le_trans hs.le (htC z hzt).1)

theorem exists_sub (ψ : AddChar (AF F) ℂ) (v : Pl F) {z : Fv F v} (hz : psiLoc ψ v z ≠ 1)
    (hzs : ∀ s : Fv F v, Valued.v s < Valued.v z → psiLoc ψ v s = 1) {κ : Type} [Fintype κ]
    {N : Set (κ → Fv F v)} (hN : N ∈ 𝓝 (0 : κ → Fv F v)) :
    ∃ U : AddSubgroup (κ → Fv F v), IsOpen (U : Set (κ → Fv F v)) ∧ (U : Set (κ → Fv F v)) ⊆ N ∧
      ∀ x ∉ U, ∃ t, (∀ u ∈ U, psiLoc ψ v (u ⬝ᵥ t) = 1) ∧ psiLoc ψ v (x ⬝ᵥ t) ≠ 1 := by
  have hN' : N ∈ Filter.pi fun _ : κ => 𝓝 (0 : Fv F v) := by simpa [nhds_pi] using hN
  obtain ⟨⟨I, γ⟩, -, hsub⟩ := (Filter.hasBasis_pi fun _ : κ => Valued.hasBasis_nhds_zero (Fv F v) (WithZero (Multiplicative ℤ))).mem_iff.1 hN'
  have hz0 : z ≠ 0 := by rintro rfl; exact hz (psiLoc_zero ψ v)
  let U : AddSubgroup (κ → Fv F v) :=
    { carrier := {x | ∀ i, (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict (x i) < ((γ i : _) : _)}
      zero_mem' := fun i => by
        simp only [Pi.zero_apply, map_zero]
        exact zero_lt_iff.2 (γ i).ne_zero
      add_mem' := fun hx hy i => Valuation.map_add_lt _ (hx i) (hy i)
      neg_mem' := fun hx i => by simpa only [Pi.neg_apply, Valuation.map_neg] using hx i }
  refine ⟨U, ?_, fun x hx => hsub fun i _ => hx i, fun x hx => ?_⟩
  · have : (U : Set (κ → Fv F v)) = Set.univ.pi fun i => {y | (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict y < ((γ i : _) : _)} := by
      ext x; simp [U]
    rw [this]
    exact isOpen_set_pi Set.finite_univ fun i _ => (Valued.isClopen_ball _ _).isOpen
  · have hx' : ∃ i, ((γ i : _) : _) ≤ (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).restrict (x i) := by
      by_contra h
      push_neg at h
      exact hx h
    obtain ⟨i, hi⟩ := hx'
    have hxi : x i ≠ 0 := by
      intro h
      rw [h, map_zero] at hi
      exact (γ i).ne_zero (le_antisymm hi zero_le')
    refine ⟨Pi.single i (z / x i), fun u hu => ?_, ?_⟩
    · rw [dotProduct_single]
      apply hzs
      have h1 : Valued.v (u i) < Valued.v (x i) := (Valuation.restrict_lt_iff _).1 (lt_of_lt_of_le (hu i) hi)
      have h2 : Valued.v (u i / x i) < 1 := by
        rw [map_div₀]
        exact (div_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hxi))).2 h1
      rw [show u i * (z / x i) = (u i / x i) * z by ring, map_mul]
      exact mul_lt_of_lt_one_left (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hz0)) h2
    · rw [dotProduct_single, mul_div_cancel₀ _ hxi]
      exact hz

theorem mem_span_locOp : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : Pl F), Continuous (psiLoc ψ v) →
    (∃ x : Fv F v, psiLoc ψ v x ≠ 1) → ∀ {κ : Type} [Fintype κ] (φ₀ φ : (κ → Fv F v) → ℂ), φ₀ ∈ SB _ → φ₀ ≠ 0 →
    φ ∈ SB _ → φ ∈ Submodule.span ℂ (Set.range fun p => GlobalTheory.FinComm.locOp ψ v p φ₀) := by
  intro F _ _ ψ v hc hn κ _ φ₀ φ h0 hne hφ
  set S := Submodule.span ℂ (Set.range fun p => GlobalTheory.FinComm.locOp ψ v p φ₀) with hS
  have htr : ∀ a, ∀ h ∈ S, (fun x => h (x + a)) ∈ S := by
    intro a h hh
    induction hh using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨⟨x₁, y⟩, rfl⟩ := hg
      have : (fun x => GlobalTheory.FinComm.locOp ψ v (x₁, y) φ₀ (x + a)) =
          psiLoc ψ v (a ⬝ᵥ y / 2) • GlobalTheory.FinComm.locOp ψ v (x₁ + a, y) φ₀ := by
        funext x
        simp only [GlobalTheory.FinComm.locOp, Pi.smul_apply, smul_eq_mul]
        rw [← mul_assoc, ← psiLoc_add]
        congr 1
        · congr 1
          simp only [add_dotProduct]
          have h2 : (2 : Fv F v) ≠ 0 := by
            have := (map_ne_zero (algebraMap F (Fv F v))).2 (two_ne_zero (α := F))
            rwa [map_ofNat] at this
          linear_combination (-(a ⬝ᵥ y)) * inv_mul_cancel₀ h2
        · congr 1
          abel
      rw [this]
      exact S.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)
    | zero => exact S.zero_mem
    | add g₁ g₂ _ _ ih₁ ih₂ => exact S.add_mem ih₁ ih₂
    | smul c g _ ih => exact S.smul_mem c ih
  have hmod : ∀ t, ∀ h ∈ S, (fun x => psiLoc ψ v (x ⬝ᵥ t) * h x) ∈ S := by
    intro t h hh
    induction hh using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨⟨x₁, y⟩, rfl⟩ := hg
      have : (fun x => psiLoc ψ v (x ⬝ᵥ t) * GlobalTheory.FinComm.locOp ψ v (x₁, y) φ₀ x) =
          psiLoc ψ v (-(x₁ ⬝ᵥ t) / 2) • GlobalTheory.FinComm.locOp ψ v (x₁, y + t) φ₀ := by
        funext x
        simp only [GlobalTheory.FinComm.locOp, Pi.smul_apply, smul_eq_mul]
        rw [← mul_assoc, ← mul_assoc, ← psiLoc_add, ← psiLoc_add]
        congr 2
        simp only [dotProduct_add]
        ring
      rw [this]
      exact S.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)
    | zero =>
      convert S.zero_mem using 1
      funext x
      simp
    | add g₁ g₂ _ _ ih₁ ih₂ =>
      convert S.add_mem ih₁ ih₂ using 1
      funext x
      simp [mul_add]
    | smul c g _ ih =>
      convert S.smul_mem c ih using 1
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  obtain ⟨z, hz, hzs⟩ := exists_cond ψ v hc hn
  have hB : ∀ N ∈ 𝓝 (0 : κ → Fv F v), ∃ W : AddSubgroup (κ → Fv F v), IsOpen (W : Set (κ → Fv F v)) ∧ (W : Set (κ → Fv F v)) ⊆ N := by
    intro N hN
    obtain ⟨U, h1, h2, -⟩ := exists_sub ψ v hz hzs hN
    exact ⟨U, h1, h2⟩
  obtain ⟨c, hc0⟩ : ∃ c, φ₀ c ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  set f : (κ → Fv F v) → ℂ := fun x => φ₀ (x + c) with hfdef
  have hfS : f ∈ S := by
    have : f = GlobalTheory.FinComm.locOp ψ v (c, 0) φ₀ := by
      funext x
      simp [f, GlobalTheory.FinComm.locOp, psiLoc_zero]
    rw [this]
    exact Submodule.subset_span ⟨_, rfl⟩
  have hfc : HasCompactSupport f := h0.2.comp_homeomorph (Homeomorph.addRight c)
  have hfl : IsLocallyConstant f := h0.1.comp_continuous (continuous_add_right c)
  have hf0 : f 0 ≠ 0 := by simpa [f] using hc0
  have hN1 : {u | f u = f 0} ∈ 𝓝 (0 : κ → Fv F v) := (hfl.isOpen_fiber (f 0)).mem_nhds rfl
  obtain ⟨N2, hN2, hper⟩ := exists_periodic hB hφ.1 hφ.2
  obtain ⟨U, hUo, hUs, hsep⟩ := exists_sub ψ v hz hzs (Filter.inter_mem hN1 hN2)
  have h1U : (fun x => if x ∈ U then f x else 0) ∈ S :=
    mem_of_sep (fun t x => psiLoc ψ v (x ⬝ᵥ t)) (fun t a b => by rw [add_dotProduct, psiLoc_add]) S hmod U hUo
      hsep hfS hfc
  have hind : ∀ a : κ → Fv F v, (fun x => if x + a ∈ U then (1 : ℂ) else 0) ∈ S := by
    intro a
    have h2 : (fun x => if x ∈ U then (1 : ℂ) else 0) ∈ S := by
      have : (fun x => if x ∈ U then (1 : ℂ) else 0) = (f 0)⁻¹ • (fun x => if x ∈ U then f x else 0) := by
        funext x
        by_cases hx : x ∈ U
        · have : f x = f 0 := (hUs hx).1
          simp only [hx, if_true, Pi.smul_apply, smul_eq_mul, this, inv_mul_cancel₀ hf0]
        · simp [hx]
      rw [this]
      exact S.smul_mem _ h1U
    exact htr a _ h2
  have hper' : ∀ x, ∀ w ∈ U, φ (x + w) = φ x := hper U fun y hy => (hUs hy).2
  have := QuotientAddGroup.discreteTopology hUo
  have hfin : ((QuotientAddGroup.mk : (κ → Fv F v) → (κ → Fv F v) ⧸ U) '' tsupport φ).Finite :=
    (hφ.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  have hsum : φ = ∑ q ∈ hfin.toFinset, φ q.out • (fun x => if x + -q.out ∈ U then (1 : ℂ) else 0) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    have hmem : ∀ q : (κ → Fv F v) ⧸ U, x + -q.out ∈ U ↔ q = QuotientAddGroup.mk x := by
      intro q
      rw [add_comm, ← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
    have hval : φ (QuotientAddGroup.mk x : (κ → Fv F v) ⧸ U).out = φ x := by
      have h3 : x + -(QuotientAddGroup.mk x : (κ → Fv F v) ⧸ U).out ∈ U := (hmem _).2 rfl
      have h4 := hper' x _ (U.neg_mem h3)
      rw [neg_add, neg_neg, add_neg_cancel_left] at h4
      exact h4
    rw [Finset.sum_eq_single (QuotientAddGroup.mk x)]
    · rw [if_pos ((hmem _).2 rfl), hval]
    · intro q _ hq
      rw [if_neg fun h => hq ((hmem q).1 h)]
    · intro hx
      have hx' : x ∉ tsupport φ := fun h => hx (hfin.mem_toFinset.2 ⟨x, h, rfl⟩)
      split_ifs
      · rw [hval, image_eq_zero_of_notMem_tsupport hx']
      · rfl
  rw [hsum]
  exact S.sum_mem fun q _ => S.smul_mem _ (hind _)

end GlobalTheory.SchrCyclic
end
end

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_span_translates_of_nonzero_schwartz : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : Pl F), Continuous (psiLoc ψ v) →
    (∃ x : Fv F v, psiLoc ψ v x ≠ 1) → ∀ {κ : Type} [Fintype κ] (φ₀ φ : (κ → Fv F v) → ℂ), φ₀ ∈ SB _ → φ₀ ≠ 0 →
    φ ∈ SB _ → φ ∈ Submodule.span ℂ (Set.range fun p => GlobalTheory.FinComm.locOp ψ v p φ₀) := by
  atlas_forward_decl GlobalTheory.SchrCyclic.mem_span_locOp
end

section
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.FinComm.VacLaw

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem eq_atPlace_of_at (v : Pl F) {z : κ → AF F} (hz : At (evFin F v) z) (i : κ) :
    z i = GlobalTheory.EmbChart.atPlace v (evFin F v (z i)) := by
  have h0 : evFin F v (1 - GlobalTheory.EmbChart.atPlace v 1) = 0 := by
    rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
  have h := congrFun (hz _ h0) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul, one_mul, sub_eq_zero] at h
  rw [GlobalTheory.EmbChart.atPlace_mul_right, one_mul] at h
  exact h

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_atPlace (v : Pl F) (a : Fv F v) : evI F (GlobalTheory.EmbChart.atPlace v a) = 0 := by
  rw [GlobalTheory.EmbChart.atPlace_apply]
  exact map_zero _

theorem evFin_atPlace_ne {v u : Pl F} (h : u ≠ v) (a : Fv F v) : evFin F u (GlobalTheory.EmbChart.atPlace v a) = 0 := by
  rw [GlobalTheory.EmbChart.atPlace_apply]
  exact evalV_singleFin_ne h a

theorem eventually_int (x : κ → AF F) :
    ∀ᶠ u in cofinite, ∀ i, evFin F u (x i) ∈ u.adicCompletionIntegers F :=
  Filter.eventually_all.mpr fun i => (x i).2.2

theorem finite_mulSupport (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (x : κ → AF F) : (Function.mulSupport fun u => φ u (fun i => evFin F u (x i))).Finite := by
  have h : ∀ᶠ u in cofinite, φ u (fun i => evFin F u (x i)) = 1 := by
    filter_upwards [hφ, eventually_int x] with u hu hx
    rw [hu]
    simp [indO, Set.indicator, hx]
  exact (Filter.eventually_cofinite.mp h).subset fun u hu hp => hu hp

theorem tens_update (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (v : Pl F) : tens (evFin F v) (φ v) (pure f (Function.update φ v fun _ => 1)) = pure f φ := by
  funext x
  have hfin := finite_mulSupport φ hφ x
  unfold tens GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  rw [← mul_finprod_cond_ne v hfin]
  have : (∏ᶠ u, Function.update φ v (fun _ => 1) u (fun i => evFin F u (x i))) =
      ∏ᶠ (u) (_ : u ≠ v), φ u (fun i => evFin F u (x i)) := by
    have hfin' : (Function.mulSupport fun u =>
        Function.update φ v (fun _ => (1 : ℂ)) u (fun i => evFin F u (x i))).Finite := by
      refine hfin.subset fun u hu => ?_
      by_cases e : u = v
      · subst e; simp at hu
      · simpa [Function.update_of_ne e] using hu
    rw [← mul_finprod_cond_ne v hfin', Function.update_self, one_mul]
    exact finprod_congr fun u => finprod_congr fun hu => by rw [Function.update_of_ne hu]
  rw [this]
  ring

theorem pure_update_add_at (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x z : κ → AF F)
    (hz : At (evFin F v) z) :
    pure f (Function.update φ v fun _ => 1) (x + z) = pure f (Function.update φ v fun _ => 1) x := by
  have hI : (fun i => evI F ((x + z) i)) = fun i => evI F (x i) := by
    funext i
    rw [Pi.add_apply, evI_add, eq_atPlace_of_at v hz i, evI_atPlace, add_zero]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  rw [hI]
  congr 1
  refine finprod_congr fun u => ?_
  by_cases e : u = v
  · subst e; simp
  · rw [Function.update_of_ne e]
    congr 1
    funext i
    rw [Pi.add_apply, map_add, eq_atPlace_of_at v hz i, evFin_atPlace_ne e, add_zero]

end GlobalTheory.FinComm.VacLaw

namespace GlobalTheory.FinComm

open GlobalTheory.FinComm.VacLaw

theorem vac_law : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ →
    ∃ c : Pl F → Matrix (Fin n) (Fin d) (AE F E) → ℂ, ∀ v, ∀ γ ∈ latAtV X W v, ∀ f : SInf F (Fin n × Fin d),
      M.co.rho ψ γ (pure f M.vac) = c v γ • pure f M.vac := by
  intro F E _ _ _ _ _ σ n d X W M ψ hM
  have hvacO : ∀ᶠ u in cofinite, M.vac u = indO u := by
    filter_upwards [hM.std] with u hu
    rw [hu]
    rfl
  have hvacSB : ∀ u, M.vac u ∈ SB _ := fun u => (hM.vac u).1
  refine ⟨fun v γ => ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (((hM.vac v).2.2.choose : 𝓞 E) : E))
    (incM F X.J) (incM F W.J) γ γ), fun v γ hγ f => ?_⟩
  have hact := ((hM.vac v).2.2.choose_spec.2) γ hγ
  have hpv : pure f M.vac ∈ schA F _ := GlobalTheory.T.pure_tensor_mem_schwartz_adelic f M.vac hvacSB hvacO
  have hten := tens_update f M.vac hvacO v
  have hrest : Rest (evFin F v) (M.vac v) (pure f (Function.update M.vac v fun _ => 1)) :=
    ⟨fun x z hz => pure_update_add_at f M.vac v x z hz, hten ▸ hpv⟩
  have h := hact _ hrest
  rw [hten] at h
  rw [h, ← hten]
  funext x
  simp [tens, mul_assoc]

end GlobalTheory.FinComm
end
end

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_rep_lattice_scalar_action : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ →
    ∃ c : Pl F → Matrix (Fin n) (Fin d) (AE F E) → ℂ, ∀ v, ∀ γ ∈ latAtV X W v, ∀ f : SInf F (Fin n × Fin d),
      M.co.rho ψ γ (pure f M.vac) = c v γ • pure f M.vac := by
  atlas_forward_decl GlobalTheory.FinComm.vac_law
end

section
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

noncomputable section

namespace GlobalTheory.VacEigenLine

theorem eigen_line : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    M.IsGood B.ψ → ∀ (v : Pl F) (t : Matrix (Fin n) (Fin d) (AE F E) → ℂ),
    (∀ γ ∈ latAtV X W v, locOp B.ψ v (locPt v (M.co.e γ)) (M.vac v) = t γ • M.vac v) →
    ∀ φ ∈ SB (Fin n × Fin d → Fv F v), (∀ γ ∈ latAtV X W v, locOp B.ψ v (locPt v (M.co.e γ)) φ = t γ • φ) →
      ∃ a : ℂ, φ = a • M.vac v := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hM v t hvac φ _ hφ
  classical
  have hAt := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  let χ : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → ℂ := fun l =>
    if h : ∃ γ ∈ latAtV X W v, GlobalTheory.LatVac.locCo M.co v γ = l then t h.choose else 0
  have loc : ∀ f : (Fin n × Fin d → Fv F v) → ℂ,
      (∀ γ ∈ latAtV X W v, locOp B.ψ v (locPt v (M.co.e γ)) f = t γ • f) →
      ∀ l ∈ (latAtV X W v).map (GlobalTheory.LatVac.locCo M.co v), ∀ ξ,
        GlobalTheory.LatVac.psiAt B.ψ v (ξ ⬝ᵥ l.2 + (2 : Fv F v)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ := by
    intro f hf l hl ξ
    have h : ∃ γ ∈ latAtV X W v, GlobalTheory.LatVac.locCo M.co v γ = l := AddSubgroup.mem_map.mp hl
    have key := congrFun (hf _ h.choose_spec.1) ξ
    have e : locPt v (M.co.e h.choose) = l := h.choose_spec.2
    simp only [χ, dif_pos h]
    rw [e] at key
    simp only [locOp, Pi.smul_apply, smul_eq_mul] at key
    rw [GlobalTheory.LatVac.psiAt_apply, ← div_eq_inv_mul]
    exact key
  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X W v M.co hX.lat hW.lat
  have hsd := GlobalTheory.LatVac.DualLoc.map_selfDual v M.co B.ψ _ hAt
    (GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B n d X W r s r' s' hB hX hW v)
  have hfill := GlobalTheory.SelfDualFirstProjAny.exists_pair_of_annihilator_any F v _ (GlobalTheory.LatVac.psiAt B.ψ v)
    (GlobalTheory.VacAny.continuous_psiV hB.std.1 v)
    (fun _ => GlobalTheory.StdCharFromIsStd.norm_psi hB.std _) (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hB.std v) _ c hc0 hsd
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  exact GlobalTheory.heisenbergEigen_proportional (GlobalTheory.LatVac.psiAt B.ψ v) _ χ (M.vac v) φ (loc _ hvac) (loc φ hφ)
    (hM.vac v).2.1 hfill

end GlobalTheory.VacEigenLine

end
end

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_vacuum_eigen_lattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    M.IsGood B.ψ → ∀ (v : Pl F) (t : Matrix (Fin n) (Fin d) (AE F E) → ℂ),
    (∀ γ ∈ latAtV X W v, locOp B.ψ v (locPt v (M.co.e γ)) (M.vac v) = t γ • M.vac v) →
    ∀ φ ∈ SB (Fin n × Fin d → Fv F v), (∀ γ ∈ latAtV X W v, locOp B.ψ v (locPt v (M.co.e γ)) φ = t γ • φ) →
      ∃ a : ℂ, φ = a • M.vac v := by
  atlas_forward_decl GlobalTheory.VacEigenLine.eigen_line
end

section
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

noncomputable section

open scoped Classical

namespace GlobalTheory.VacEig

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_schwartz_one (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ Φ : SchwartzMap V ℂ, Φ 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

theorem eventually_int' (x : κ → AF F) :
    ∀ᶠ u in cofinite, ∀ i, evFin F u (x i) ∈ u.adicCompletionIntegers F :=
  Filter.eventually_all.mpr fun i => (x i).2.2

theorem finite_mulSupport' (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (x : κ → AF F) : (Function.mulSupport fun u => φ u (fun i => evFin F u (x i))).Finite := by
  have h : ∀ᶠ u in cofinite, φ u (fun i => evFin F u (x i)) = 1 := by
    filter_upwards [hφ, eventually_int' x] with u hu hx
    rw [hu]
    simp [indO, Set.indicator, hx]
  exact (Filter.eventually_cofinite.mp h).subset fun u hu hp => hu hp

theorem pure_split (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (v : Pl F) (x : κ → AF F) :
    pure f φ x = φ v (fun i => evFin F v (x i)) *
      (f (fun i => evI F (x i)) * ∏ᶠ (u) (_ : u ≠ v), φ u (fun i => evFin F u (x i))) := by
  have hfin := finite_mulSupport' _ hφ x
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  rw [← mul_finprod_cond_ne v hfin]
  ring

theorem pure_update_split (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (v : Pl F) (g : (κ → Fv F v) → ℂ) (x : κ → AF F) :
    pure f (Function.update φ v g) x = g (fun i => evFin F v (x i)) *
      (f (fun i => evI F (x i)) * ∏ᶠ (u) (_ : u ≠ v), φ u (fun i => evFin F u (x i))) := by
  have hφ' : ∀ᶠ u in cofinite, Function.update φ v g u = indO u := by
    filter_upwards [hφ, (Set.finite_singleton v).compl_mem_cofinite] with u hu hv
    rw [Function.update_of_ne hv, hu]
  rw [pure_split f _ hφ' v x, Function.update_self]
  congr 2
  exact finprod_congr fun u => finprod_congr fun hu => by rw [Function.update_of_ne hu]

theorem vac_eig : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ →
    ∀ c : Pl F → Matrix (Fin n) (Fin d) (AE F E) → ℂ,
    (∀ v, ∀ γ ∈ latAtV X W v, ∀ f : SInf F (Fin n × Fin d),
      M.co.rho ψ γ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = c v γ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) →
    ∀ v, ∀ γ ∈ latAtV X W v, locOp ψ v (locPt v (M.co.e γ)) (M.vac v) = c v γ • M.vac v := by
  intro F E _ _ _ _ _ σ n d X W M ψ hM c hc v γ hγ
  have hvacO : ∀ᶠ u in cofinite, M.vac u = indO u := by
    filter_upwards [hM.std] with u hu
    rw [hu]
    rfl
  obtain ⟨f, hf⟩ := exists_schwartz_one (Fin n × Fin d → mixedEmbedding.mixedSpace F)
  have e2 := hc v γ hγ f
  rw [GlobalTheory.T.weil_rep_pure_tensor_local M ψ v γ (at_latAtV hγ) f M.vac hvacO] at e2
  choose w hw using fun u => Function.ne_iff.mp (hM.vac u).2.1
  have hT : {u | M.vac u ≠ indO u ∧ u ≠ v}.Finite :=
    (Filter.eventually_cofinite.mp hvacO).subset fun u hu => hu.1
  set T := hT.toFinset with hTdef
  funext z
  set y : Fin n × Fin d → Af F := fun i => singleFin v (z i) + ∑ u ∈ T, singleFin u (w u i) with hy
  set x := mkPt (fun _ => (0 : mixedEmbedding.mixedSpace F)) y with hx
  have hxv : (fun i => evFin F v (x i)) = z := by
    funext i
    rw [hx, evFin_mkPt, hy]
    simp only [map_add, map_sum, evalV_singleFin_self]
    rw [Finset.sum_eq_zero, add_zero]
    intro u hu
    have : u ≠ v := (hT.mem_toFinset.mp hu).2
    exact evalV_singleFin_ne (Ne.symm this) _
  have hxu : ∀ u, u ≠ v → M.vac u (fun i => evFin F u (x i)) ≠ 0 := by
    intro u huv
    have hcomp : ∀ i, evFin F u (x i) = ∑ u' ∈ T, evalV F u (singleFin u' (w u' i)) := by
      intro i
      rw [hx, evFin_mkPt, hy]
      simp only [map_add, map_sum, evalV_singleFin_ne huv, zero_add]
    by_cases huT : u ∈ T
    · have : (fun i => evFin F u (x i)) = w u := by
        funext i
        rw [hcomp, Finset.sum_eq_single_of_mem u huT, evalV_singleFin_self]
        intro u' _ hne
        exact evalV_singleFin_ne (Ne.symm hne) _
      rw [this]
      exact hw u
    · have hstd : M.vac u = indO u := by
        by_contra h
        exact huT (hT.mem_toFinset.mpr ⟨h, huv⟩)
      have : (fun i => evFin F u (x i)) = 0 := by
        funext i
        rw [hcomp, Finset.sum_eq_zero]
        · rfl
        intro u' hu'
        have hne : u ≠ u' := fun h => huT (h ▸ hu')
        exact evalV_singleFin_ne hne _
      rw [this, hstd]
      simp [indO, Set.indicator, zero_mem]
  have hR : (f fun i => evI F (x i)) * ∏ᶠ (u) (_ : u ≠ v), M.vac u (fun i => evFin F u (x i)) ≠ 0 := by
    refine mul_ne_zero ?_ (finprod_ne_zero fun u => ?_)
    · have : (fun i => evI F (x i)) = 0 := by
        funext i
        rw [hx, evI_mkPt]
        rfl
      rw [this, hf]
      exact one_ne_zero
    · rw [finprod_eq_if]
      split_ifs with huv
      · exact hxu u huv
      · exact one_ne_zero
  have h := congrFun e2 x
  rw [Pi.smul_apply, smul_eq_mul, pure_update_split f M.vac hvacO v _ x, pure_split f M.vac hvacO v x, hxv] at h
  rw [Pi.smul_apply, smul_eq_mul]
  exact mul_right_cancel₀ hR (by linear_combination h)

end GlobalTheory.VacEig
end
end

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_eigen_at_all_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ →
    ∀ c : Pl F → Matrix (Fin n) (Fin d) (AE F E) → ℂ,
    (∀ v, ∀ γ ∈ latAtV X W v, ∀ f : SInf F (Fin n × Fin d),
      M.co.rho ψ γ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = c v γ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) →
    ∀ v, ∀ γ ∈ latAtV X W v, locOp ψ v (locPt v (M.co.e γ)) (M.vac v) = c v γ • M.vac v := by
  atlas_forward_decl GlobalTheory.VacEig.vac_eig
end

section
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

namespace GlobalTheory.VacLine

theorem slice_schA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (Ψ : (κ → AF F) → ℂ), Ψ ∈ schA F κ →
    (∀ y : κ → Af F, ∃ f : SInf F κ, ∀ x, slice Ψ x y = f x) ∧ ∀ x, slice Ψ x ∈ SB (κ → Af F) := by
  intro F _ _ κ _ Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    have key : ∀ x y, slice (pureA F f g) x y = f x * g y := by
      intro x y
      simp only [slice, pureA, mkPt, RingEquiv.apply_symm_apply]
    refine ⟨fun y => ⟨g y • f, fun x => ?_⟩, fun x => ?_⟩
    · rw [key, SchwartzMap.smul_apply, smul_eq_mul, mul_comm]
    · have : slice (pureA F f g) x = f x • g := by
        funext y; rw [key]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ hg
  | zero =>
    refine ⟨fun y => ⟨0, fun x => rfl⟩, fun x => ?_⟩
    exact Submodule.zero_mem _
  | add Φ Φ' _ _ h h' =>
    refine ⟨fun y => ?_, fun x => ?_⟩
    · obtain ⟨f, hf⟩ := h.1 y
      obtain ⟨f', hf'⟩ := h'.1 y
      exact ⟨f + f', fun x => by
        show slice Φ x y + slice Φ' x y = (f + f') x
        rw [hf, hf', SchwartzMap.add_apply]⟩
    · have : slice (Φ + Φ') x = slice Φ x + slice Φ' x := rfl
      rw [this]
      exact Submodule.add_mem _ (h.2 x) (h'.2 x)
  | smul a Φ _ h =>
    refine ⟨fun y => ?_, fun x => ?_⟩
    · obtain ⟨f, hf⟩ := h.1 y
      exact ⟨a • f, fun x => by
        show a • slice Φ x y = (a • f) x
        rw [hf, SchwartzMap.smul_apply]⟩
    · have : slice (a • Φ) x = a • slice Φ x := rfl
      rw [this]
      exact Submodule.smul_mem _ _ (h.2 x)

end GlobalTheory.VacLine
end

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_adelic_slice_smooth : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (Ψ : (κ → AF F) → ℂ), Ψ ∈ schA F κ →
    (∀ y : κ → Af F, ∃ f : SInf F κ, ∀ x, slice Ψ x y = f x) ∧ ∀ x, slice Ψ x ∈ SB (κ → Af F) := by
  atlas_forward_decl GlobalTheory.VacLine.slice_schA
end

section
section
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

namespace GlobalTheory.VacLine.RhoSlice

variable {F : Type} [Field F] [NumberField F]

theorem at_mul {v : Pl F} {b : AF F} (hb : At (evFin F v) b) (a : AF F) : At (evFin F v) (a * b) := by
  intro u hu
  rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u b, hb u hu, mul_zero]

theorem at_add {v : Pl F} {a b : AF F} (ha : At (evFin F v) a) (hb : At (evFin F v) b) :
    At (evFin F v) (a + b) := by
  intro u hu
  rw [smul_add, ha u hu, hb u hu, add_zero]

theorem at_dot {κ : Type} [Fintype κ] {v : Pl F} (a b : κ → AF F) (hb : ∀ i, At (evFin F v) (b i)) :
    At (evFin F v) (a ⬝ᵥ b) := by
  intro u hu
  simp only [dotProduct, Finset.smul_sum]
  exact Finset.sum_eq_zero fun i _ => at_mul (hb i) (a i) u hu

theorem singleFin_one_mul (v : Pl F) (y : Af F) : singleFin v 1 * y = singleFin v (evalV F v y) := by
  refine af_ext fun u => ?_
  rw [map_mul]
  by_cases h : u = v
  · subst h; rw [evalV_singleFin_self, evalV_singleFin_self, one_mul]
  · rw [evalV_singleFin_ne h, evalV_singleFin_ne h, zero_mul]

theorem evFin_inr_singleFin (v : Pl F) (c : Fv F v) :
    evFin F v (LinearMap.inr F (Ainf F) (Af F) (singleFin v c)) = c :=
  evalV_singleFin_self v c

theorem eq_inr_of_at {v : Pl F} {a : AF F} (ha : At (evFin F v) a) :
    a = LinearMap.inr F (Ainf F) (Af F) (singleFin v (evFin F v a)) := by
  have h1 := ha (1 - (show AF F from LinearMap.inr F (Ainf F) (Af F) (singleFin v 1)))
    (by rw [map_sub, map_one, evFin_inr_singleFin, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h1
  refine h1.trans (Prod.ext ?_ ?_)
  · show (0 : Ainf F) * a.1 = 0
    exact zero_mul _
  · show singleFin v 1 * a.2 = singleFin v (evFin F v a)
    exact singleFin_one_mul v a.2

theorem evFin_invOf_two (v : Pl F) : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]

end GlobalTheory.VacLine.RhoSlice

namespace GlobalTheory.VacLine.RhoSlice

theorem at_coord {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {v : Pl F} {w : Matrix (Fin n) (Fin d) (AE F E)}
    (hw : At (evFin F v) w) (i : Fin n × Fin d) :
    At (evFin F v) ((M.co.e w).1 i) ∧ At (evFin F v) ((M.co.e w).2 i) := by
  have h : ∀ u : AF F, evFin F v u = 0 → u • M.co.e w = 0 := fun u hu => by
    rw [← LinearEquiv.map_smul, hw u hu, map_zero]
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have := congrArg (fun p => p.1 i) (h u hu)
    simpa using this
  · have := congrArg (fun p => p.2 i) (h u hu)
    simpa using this

theorem rho_slice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F)
    (w : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) w →
    ∀ (Φ : (Fin n × Fin d → AF F) → ℂ) (x : Fin n × Fin d → mixedEmbedding.mixedSpace F),
      slice (M.co.rho ψ w Φ) x = finOp ψ v (locPt v (M.co.e w)) (slice Φ x) := by
  intro F E _ _ _ _ _ σ n d X W M ψ v w hw Φ x
  funext y
  have hc := at_coord M hw
  have hz : At (evFin F v) (mkPt x y ⬝ᵥ (M.co.e w).2 + ⅟(2 : AF F) * ((M.co.e w).1 ⬝ᵥ (M.co.e w).2)) :=
    at_add (at_dot _ _ fun i => (hc i).2) (at_mul (at_dot _ _ fun i => (hc i).2) _)
  show ψ (mkPt x y ⬝ᵥ (M.co.e w).2 + ⅟(2 : AF F) * ((M.co.e w).1 ⬝ᵥ (M.co.e w).2)) * Φ (mkPt x y + (M.co.e w).1) = _
  rw [show ψ (mkPt x y ⬝ᵥ (M.co.e w).2 + ⅟(2 : AF F) * ((M.co.e w).1 ⬝ᵥ (M.co.e w).2)) =
    psiLoc ψ v (evFin F v (mkPt x y ⬝ᵥ (M.co.e w).2 + ⅟(2 : AF F) * ((M.co.e w).1 ⬝ᵥ (M.co.e w).2))) from
    congrArg ψ (eq_inr_of_at hz)]
  unfold finOp slice locPt
  congr 2
  · simp only [dotProduct, map_add, map_mul, map_sum, evFin_invOf_two, evFin_mkPt]
    ring
  · funext i
    show mkPt x y i + (M.co.e w).1 i = _
    rw [eq_inr_of_at (hc i).1]
    exact Prod.ext (add_zero _) rfl

end GlobalTheory.VacLine.RhoSlice
end
end

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_rep_slice_finite_op : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F)
    (w : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) w →
    ∀ (Φ : (Fin n × Fin d → AF F) → ℂ) (x : Fin n × Fin d → mixedEmbedding.mixedSpace F),
      slice (M.co.rho ψ w Φ) x = finOp ψ v (locPt v (M.co.e w)) (slice Φ x) := by
  atlas_forward_decl GlobalTheory.VacLine.RhoSlice.rho_slice
end

section
section
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine
open scoped Classical

namespace GlobalTheory.VacFactor

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem mem_SB_iff' {X : Type} [TopologicalSpace X] (f : X → ℂ) :
    f ∈ SB X ↔ IsLocallyConstant f ∧ HasCompactSupport f := Iff.rfl

theorem pt_ext {a b : κ → Af F} (h : ∀ u i, evalV F u (a i) = evalV F u (b i)) : a = b :=
  funext fun i => Subtype.ext (funext fun u => h u i)

def setAt (y : κ → Af F) (v : Pl F) (z : κ → Fv F v) : κ → Af F :=
  fun i => y i + singleFin v (z i - evalV F v (y i))

theorem evalV_setAt_self (y : κ → Af F) (v : Pl F) (z : κ → Fv F v) (i : κ) :
    evalV F v (setAt y v z i) = z i := by
  rw [setAt, map_add, evalV_singleFin_self]; ring

theorem evalV_setAt_ne (y : κ → Af F) {v u : Pl F} (h : u ≠ v) (z : κ → Fv F v) (i : κ) :
    evalV F u (setAt y v z i) = evalV F u (y i) := by
  rw [setAt, map_add, evalV_singleFin_ne h, add_zero]

theorem setAt_eval (y : κ → Af F) (v : Pl F) : setAt y v (fun i => evalV F v (y i)) = y := by
  funext i; simp [setAt]

theorem setAt_add (y : κ → Af F) (v : Pl F) (z p : κ → Fv F v) :
    (setAt y v z + fun i => singleFin v (p i)) = setAt y v (z + p) := by
  apply pt_ext
  intro u i
  by_cases h : u = v
  · subst h
    simp only [Pi.add_apply, map_add, evalV_setAt_self, evalV_singleFin_self]
  · simp only [Pi.add_apply, map_add, evalV_setAt_ne y h, evalV_singleFin_ne h, add_zero]

def setOn (S : Finset (Pl F)) (y : κ → Af F) (z₀ : ∀ v : Pl F, κ → Fv F v) : κ → Af F :=
  fun i => y i + ∑ v ∈ S, singleFin v (z₀ v i - evalV F v (y i))

theorem evalV_setOn_mem {S : Finset (Pl F)} (y : κ → Af F) (z₀ : ∀ v : Pl F, κ → Fv F v) {u : Pl F} (hu : u ∈ S)
    (i : κ) : evalV F u (setOn S y z₀ i) = z₀ u i := by
  rw [setOn, map_add, map_sum, Finset.sum_eq_single u (fun w _ hw => evalV_singleFin_ne (Ne.symm hw) _)
    (fun h => absurd hu h), evalV_singleFin_self]
  ring

theorem evalV_setOn_not {S : Finset (Pl F)} (y : κ → Af F) (z₀ : ∀ v : Pl F, κ → Fv F v) {u : Pl F} (hu : u ∉ S)
    (i : κ) : evalV F u (setOn S y z₀ i) = evalV F u (y i) := by
  rw [setOn, map_add, map_sum, Finset.sum_eq_zero (fun w hw => evalV_singleFin_ne (by rintro rfl; exact hu hw) _),
    add_zero]

theorem setOn_empty (y : κ → Af F) (z₀ : ∀ v : Pl F, κ → Fv F v) : setOn ∅ y z₀ = y := by
  funext i; simp [setOn]

theorem setAt_setOn {S : Finset (Pl F)} (y : κ → Af F) (z₀ : ∀ v : Pl F, κ → Fv F v) {w : Pl F} (hw : w ∉ S) :
    setAt (setOn S y z₀) w (z₀ w) = setOn (insert w S) y z₀ := by
  apply pt_ext
  intro u i
  by_cases h : u = w
  · subst h
    rw [evalV_setAt_self, evalV_setOn_mem y z₀ (Finset.mem_insert_self u S)]
  · rw [evalV_setAt_ne _ h]
    by_cases hS : u ∈ S
    · rw [evalV_setOn_mem y z₀ hS, evalV_setOn_mem y z₀ (Finset.mem_insert_of_mem hS)]
    · rw [evalV_setOn_not y z₀ hS, evalV_setOn_not y z₀ (by simp [h, hS])]

theorem slice_mem_SB {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) (y : κ → Af F) (v : Pl F) :
    (fun z : κ → Fv F v => g (setAt y v z)) ∈ SB (κ → Fv F v) := by
  obtain ⟨hlc, hcs⟩ := (mem_SB_iff' g).mp hg
  have hcont : Continuous fun z : κ → Fv F v => setAt y v z :=
    continuous_pi fun i => continuous_const.add
      ((continuous_singleFin v).comp ((continuous_apply i).sub continuous_const))
  have hE : Continuous fun x : κ → Af F => fun i => evalV F v (x i) :=
    continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
  refine (mem_SB_iff' _).mpr ⟨hlc.comp_continuous hcont, ?_⟩
  refine HasCompactSupport.intro (hcs.isCompact.image hE) fun z hz => ?_
  by_contra h
  exact hz ⟨setAt y v z, subset_tsupport _ h, funext fun i => evalV_setAt_self y v z i⟩

theorem locOp_slice (ψ : AddChar (AF F) ℂ) (g : (κ → Af F) → ℂ) (y : κ → Af F) (v : Pl F)
    (p : (κ → Fv F v) × (κ → Fv F v)) (c : ℂ) (h : finOp ψ v p g = c • g) :
    locOp ψ v p (fun z => g (setAt y v z)) = c • fun z => g (setAt y v z) := by
  funext z
  have e := congrFun h (setAt y v z)
  have hz : (fun i => evalV F v (setAt y v z i)) = z := funext fun i => evalV_setAt_self y v z i
  simp only [finOp, Pi.smul_apply, smul_eq_mul, hz, setAt_add] at e
  simp only [locOp, Pi.smul_apply, smul_eq_mul]
  exact e

theorem eigen_place (ψ : AddChar (AF F) ℂ) (v : Pl F) (vacv : (κ → Fv F v) → ℂ)
    (Qv : Set (((κ → Fv F v) × (κ → Fv F v)) × ℂ))
    (hline : ∀ φ ∈ SB (κ → Fv F v), (∀ q ∈ Qv, locOp ψ v q.1 φ = q.2 • φ) → ∃ a : ℂ, φ = a • vacv)
    {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) (heig : ∀ q ∈ Qv, finOp ψ v q.1 g = q.2 • g)
    (y : κ → Af F) (z₁ : κ → Fv F v) :
    g y * vacv z₁ = g (setAt y v z₁) * vacv (fun i => evalV F v (y i)) := by
  obtain ⟨a, ha⟩ := hline _ (slice_mem_SB hg y v) fun q hq => locOp_slice ψ g y v q.1 q.2 (heig q hq)
  have h1 := congrFun ha (fun i => evalV F v (y i))
  have h2 := congrFun ha z₁
  simp only [Pi.smul_apply, smul_eq_mul, setAt_eval] at h1 h2
  rw [h1, h2]; ring

theorem eigen_finset (ψ : AddChar (AF F) ℂ) (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (Q : ∀ v : Pl F, Set (((κ → Fv F v) × (κ → Fv F v)) × ℂ))
    (hline : ∀ v, ∀ φ ∈ SB (κ → Fv F v), (∀ q ∈ Q v, locOp ψ v q.1 φ = q.2 • φ) → ∃ a : ℂ, φ = a • vac v)
    {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) (heig : ∀ v, ∀ q ∈ Q v, finOp ψ v q.1 g = q.2 • g)
    (z₀ : ∀ v : Pl F, κ → Fv F v) (y : κ → Af F) (S : Finset (Pl F)) :
    g y * ∏ v ∈ S, vac v (z₀ v) = g (setOn S y z₀) * ∏ v ∈ S, vac v (fun i => evalV F v (y i)) := by
  induction S using Finset.induction_on with
  | empty => simp [setOn_empty]
  | insert w S hw ih =>
    have e := eigen_place ψ w (vac w) (Q w) (hline w) hg (heig w) (setOn S y z₀) (z₀ w)
    rw [setAt_setOn y z₀ hw] at e
    have hyw : (fun i => evalV F w (setOn S y z₀ i)) = fun i => evalV F w (y i) :=
      funext fun i => evalV_setOn_not y z₀ hw i
    rw [hyw] at e
    rw [Finset.prod_insert hw, Finset.prod_insert hw]
    linear_combination (vac w (z₀ w)) * ih + (∏ v ∈ S, vac v (fun i => evalV F v (y i))) * e

theorem finprod_split (S : Finset (Pl F)) (y : κ → Af F) (A : Pl F → ℂ) :
    (∏ᶠ u, if u ∈ S then A u else indO u (fun i => evalV F u (y i))) =
      (∏ u ∈ S, A u) * ∏ᶠ u, if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i)) := by
  have hf1 : Function.mulSupport (fun u => if u ∈ S then A u else (1 : ℂ)) ⊆ (S : Set (Pl F)) := by
    intro u hu
    by_contra h
    exact hu (by simp only [Finset.mem_coe] at h; simp [h])
  have hint : ∀ᶠ u in cofinite, ∀ i, evalV F u (y i) ∈ HeightOneSpectrum.adicCompletionIntegers F u :=
    Filter.eventually_all.mpr fun i => (y i).2
  have hf2 : (Function.mulSupport fun u => if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i))).Finite := by
    have h : ∀ᶠ u in cofinite, (if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i))) = 1 := by
      filter_upwards [hint] with u hu
      split_ifs
      · rfl
      · simp [indO, Set.indicator, hu]
    exact (Filter.eventually_cofinite.mp h).subset fun u hu hp => hu hp
  have hsplit : (fun u => if u ∈ S then A u else indO u (fun i => evalV F u (y i))) =
      fun u => (if u ∈ S then A u else (1 : ℂ)) * (if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i))) := by
    funext u; split_ifs <;> simp
  rw [hsplit, finprod_mul_distrib ((S.finite_toSet).subset hf1) hf2, finprod_eq_prod_of_mulSupport_subset _ hf1]
  congr 1
  exact Finset.prod_congr rfl fun u hu => if_pos hu

theorem eq_smul_vacProd : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ) (Q : ∀ v : Pl F, Set (((κ → Fv F v) × (κ → Fv F v)) × ℂ)),
    (∀ v, vac v ∈ SB (κ → Fv F v)) → (∀ v, vac v ≠ 0) → (∀ᶠ v in cofinite, vac v = indO v) →
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), (∀ q ∈ Q v, locOp ψ v q.1 φ = q.2 • φ) → ∃ a : ℂ, φ = a • vac v) →
    ∀ g ∈ SB (κ → Af F), (∀ v, ∀ q ∈ Q v, finOp ψ v q.1 g = q.2 • g) → ∃ a : ℂ, g = a • vacProd vac := by
  intro F _ _ κ _ ψ vac Q _ hne hvacO hline g hg heig
  obtain ⟨m, φ, -, hφstd, hrep⟩ := GlobalTheory.SBRestrProd.sb_eq_sum_restrProd g hg
  have hgood : ∀ᶠ v in cofinite, (∀ j, φ j v = indO v) ∧ vac v = indO v :=
    (Filter.eventually_all.mpr hφstd).and hvacO
  have hfin := Filter.eventually_cofinite.mp hgood
  set S := hfin.toFinset with hSdef
  have hout : ∀ u, u ∉ S → (∀ j, φ j u = indO u) ∧ vac u = indO u := by
    intro u hu
    by_contra h
    exact hu (hfin.mem_toFinset.mpr h)
  have hz : ∀ v, ∃ z, vac v z ≠ 0 := fun v => Function.ne_iff.mp (hne v)
  choose z₀ hz₀ using hz
  have hP0 : (∏ v ∈ S, vac v (z₀ v)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => hz₀ v
  set R : (κ → Af F) → ℂ := fun y => ∏ᶠ u, if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i)) with hR
  set c : ℂ := ∑ j, ∏ u ∈ S, φ j u (z₀ u) with hc
  have hvac : ∀ y, vacProd vac y = (∏ u ∈ S, vac u (fun i => evalV F u (y i))) * R y := by
    intro y
    rw [← finprod_split S y]
    unfold vacProd
    refine finprod_congr fun u => ?_
    split_ifs with h
    · rfl
    · rw [(hout u h).2]
  have hgS : ∀ y, g (setOn S y z₀) = c * R y := by
    intro y
    rw [hrep, hc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← finprod_split S y]
    refine finprod_congr fun u => ?_
    split_ifs with h
    · congr 1
      exact funext fun i => evalV_setOn_mem y z₀ h i
    · rw [(hout u h).1 j]
      congr 1
      exact funext fun i => evalV_setOn_not y z₀ h i
  refine ⟨c / ∏ v ∈ S, vac v (z₀ v), funext fun y => ?_⟩
  have key := eigen_finset ψ vac Q hline hg heig z₀ y S
  rw [hgS] at key
  rw [Pi.smul_apply, smul_eq_mul, hvac]
  field_simp
  linear_combination key

end GlobalTheory.VacFactor
end
end

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_unique_product_eigen : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ) (Q : ∀ v : Pl F, Set (((κ → Fv F v) × (κ → Fv F v)) × ℂ)),
    (∀ v, vac v ∈ SB (κ → Fv F v)) → (∀ v, vac v ≠ 0) → (∀ᶠ v in cofinite, vac v = indO v) →
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), (∀ q ∈ Q v, locOp ψ v q.1 φ = q.2 • φ) → ∃ a : ℂ, φ = a • vac v) →
    ∀ g ∈ SB (κ → Af F), (∀ v, ∀ q ∈ Q v, finOp ψ v q.1 g = q.2 • g) → ∃ a : ℂ, g = a • vacProd vac := by
  atlas_forward_decl GlobalTheory.VacFactor.eq_smul_vacProd
end

section
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

namespace GlobalTheory.VacLine

theorem vacProd_ne_zero_somewhere : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, vac v ≠ 0) →
    (∀ᶠ v in cofinite, vac v = indO v) → ∃ y : κ → Af F, vacProd vac y ≠ 0 := by
  intro F _ _ κ vac hne hcof
  classical
  have hS : {v : Pl F | ¬ vac v = indO v}.Finite := Filter.eventually_cofinite.mp hcof
  have hz : ∀ v, ∃ z : κ → Fv F v, vac v z ≠ 0 := fun v => by
    by_contra h
    push_neg at h
    exact hne v (funext h)
  choose z hz using hz
  set S := hS.toFinset with hSdef
  refine ⟨fun i => ∑ v ∈ S, singleFin v (z v i), ?_⟩
  have hev : ∀ (u : Pl F) (i : κ), evalV F u (∑ v ∈ S, singleFin v (z v i)) = if u ∈ S then z u i else 0 := by
    intro u i
    rw [map_sum]
    split_ifs with hu
    · rw [Finset.sum_eq_single u]
      · exact GlobalTheory.AdelicU.evalV_singleFin_self u (z u i)
      · intro b _ hb
        exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hb) _
      · intro h; exact absurd hu h
    · apply Finset.sum_eq_zero
      intro b hb
      exact GlobalTheory.AdelicU.evalV_singleFin_ne (fun h : u = b => hu (h ▸ hb)) _
  unfold vacProd
  have hsub : Function.mulSupport (fun u : Pl F => vac u fun i => evalV F u (∑ v ∈ S, singleFin v (z v i))) ⊆ (S : Set (Pl F)) := by
    intro u hu
    by_contra hnot
    apply hu
    have hmem : u ∉ S := hnot
    have hvu : vac u = indO u := by
      by_contra h
      exact hmem (by rw [hSdef, Set.Finite.mem_toFinset]; exact h)
    simp only [hev, hmem, if_false]
    rw [hvu]
    simp [indO, Set.indicator, zero_mem]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, Finset.prod_ne_zero_iff]
  intro u hu
  have : (fun i => evalV F u (∑ v ∈ S, singleFin v (z v i))) = z u := by
    funext i; rw [hev, if_pos hu]
  rw [this]
  exact hz u

end GlobalTheory.VacLine
end

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_product_exists_nonzero : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, vac v ≠ 0) →
    (∀ᶠ v in cofinite, vac v = indO v) → ∃ y : κ → Af F, vacProd vac y ≠ 0 := by
  atlas_forward_decl GlobalTheory.VacLine.vacProd_ne_zero_somewhere
end

section
section
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

namespace GlobalTheory.VacLine

theorem vac_line : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ c : Pl F → Matrix (Fin n) (Fin d) (AE F E) → ℂ,
      (∀ v, ∀ γ ∈ latAtV X W v, ∀ f : SInf F (Fin n × Fin d), M.co.rho B.ψ γ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = c v γ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) →
      ∀ Ψ ∈ schA F (Fin n × Fin d), (∀ v, ∀ γ ∈ latAtV X W v, M.co.rho B.ψ γ Ψ = c v γ • Ψ) →
        ∃ f₁ : SInf F (Fin n × Fin d), Ψ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ M.vac := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hM c hc Ψ hΨ hΨc
  have hstd : ∀ᶠ v in cofinite, M.vac v = indO v := by
    filter_upwards [hM.std] with u hu
    rw [hu]
    rfl
  have hveig := GlobalTheory.T.vacuum_eigen_at_all_places M B.ψ hM c hc
  let Q : ∀ v : Pl F, Set (((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) × ℂ) :=
    fun v => {q | ∃ γ ∈ latAtV X W v, q = (locPt v (M.co.e γ), c v γ)}
  have hline : ∀ v, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), (∀ q ∈ Q v, locOp B.ψ v q.1 φ = q.2 • φ) →
      ∃ a : ℂ, φ = a • M.vac v := by
    intro v φ hφ hq
    refine GlobalTheory.T.local_vacuum_eigen_lattice B X W M r s r' s' hB hX hW hM v (c v) (hveig v) φ hφ fun γ hγ => ?_
    exact hq (locPt v (M.co.e γ), c v γ) ⟨γ, hγ, rfl⟩
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.vacuum_product_exists_nonzero M.vac (fun v => (hM.vac v).2.1) hstd
  obtain ⟨hF, hSB⟩ := GlobalTheory.T.schwartz_adelic_slice_smooth Ψ hΨ
  obtain ⟨f₀, hf₀⟩ := hF y₀
  have heig : ∀ x, ∀ v, ∀ q ∈ Q v, finOp B.ψ v q.1 (slice Ψ x) = q.2 • slice Ψ x := by
    intro x v q hq
    obtain ⟨γ, hγ, rfl⟩ := hq
    rw [← GlobalTheory.T.weil_rep_slice_finite_op M B.ψ v γ (at_latAtV hγ) Ψ x, hΨc v γ hγ]
    rfl
  have hfac : ∀ x, ∃ a : ℂ, slice Ψ x = a • vacProd M.vac := fun x =>
    GlobalTheory.T.vacuum_unique_product_eigen B.ψ M.vac Q (fun v => (hM.vac v).1) (fun v => (hM.vac v).2.1) hstd hline (slice Ψ x) (hSB x) (heig x)
  choose a ha using hfac
  refine ⟨(vacProd M.vac y₀)⁻¹ • f₀, ?_⟩
  funext z
  have hz := mkPt_eq z
  have h1 : Ψ (mkPt (fun i => evI F (z i)) (fun i => (z i).2)) =
      a (fun i => evI F (z i)) * vacProd M.vac (fun i => (z i).2) := congrFun (ha _) _
  have h2 : f₀ (fun i => evI F (z i)) = a (fun i => evI F (z i)) * vacProd M.vac y₀ := by
    rw [← hf₀]; exact congrFun (ha _) y₀
  rw [← hz, pure_mkPt, h1, SchwartzMap.smul_apply, h2, smul_eq_mul]
  field_simp

end GlobalTheory.VacLine
end
end

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_rep_scalar_char_of_signature : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ c : Pl F → Matrix (Fin n) (Fin d) (AE F E) → ℂ,
      (∀ v, ∀ γ ∈ latAtV X W v, ∀ f : SInf F (Fin n × Fin d), M.co.rho B.ψ γ (pure f M.vac) = c v γ • pure f M.vac) →
      ∀ Ψ ∈ schA F (Fin n × Fin d), (∀ v, ∀ γ ∈ latAtV X W v, M.co.rho B.ψ γ Ψ = c v γ • Ψ) →
        ∃ f₁ : SInf F (Fin n × Fin d), Ψ = pure f₁ M.vac := by
  atlas_forward_decl GlobalTheory.VacLine.vac_line
end

section
section
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.FinComm

section Pure

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem eventually_int (x : κ → AF F) :
    ∀ᶠ u in cofinite, ∀ i, evFin F u (x i) ∈ u.adicCompletionIntegers F :=
  Filter.eventually_all.mpr fun i => (x i).2.2

theorem finite_mulSupport (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (x : κ → AF F) : (Function.mulSupport fun u => φ u (fun i => evFin F u (x i))).Finite := by
  have h : ∀ᶠ u in cofinite, φ u (fun i => evFin F u (x i)) = 1 := by
    filter_upwards [hφ, eventually_int x] with u hu hx
    rw [hu]
    simp [indO, Set.indicator, hx]
  exact (Filter.eventually_cofinite.mp h).subset fun u hu hp => hu hp

theorem pure_update (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (v : Pl F) (g : (κ → Fv F v) → ℂ) (x : κ → AF F) :
    pure f (Function.update φ v g) x = g (fun i => evFin F v (x i)) *
      (f (fun i => evI F (x i)) * ∏ᶠ (u) (_ : u ≠ v), φ u (fun i => evFin F u (x i))) := by
  have hφ' : ∀ᶠ u in cofinite, Function.update φ v g u = indO u := by
    filter_upwards [hφ, (Set.finite_singleton v).compl_mem_cofinite] with u hu hv
    rw [Function.update_of_ne hv, hu]
  have hfin := finite_mulSupport _ hφ' x
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  rw [← mul_finprod_cond_ne v hfin, Function.update_self]
  have : (∏ᶠ (u) (_ : u ≠ v), Function.update φ v g u (fun i => evFin F u (x i))) =
      ∏ᶠ (u) (_ : u ≠ v), φ u (fun i => evFin F u (x i)) :=
    finprod_congr fun u => finprod_congr fun hu => by rw [Function.update_of_ne hu]
  rw [this]
  ring

theorem pure_update_zero (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ)
    (hφ : ∀ᶠ u in cofinite, φ u = indO u) (v : Pl F) : pure f (Function.update φ v 0) = 0 := by
  funext x
  rw [pure_update f φ hφ]
  simp

theorem pure_update_add (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ)
    (hφ : ∀ᶠ u in cofinite, φ u = indO u) (v : Pl F) (g h : (κ → Fv F v) → ℂ) :
    pure f (Function.update φ v (g + h)) = pure f (Function.update φ v g) + pure f (Function.update φ v h) := by
  funext x
  simp only [Pi.add_apply, pure_update f φ hφ]
  ring

theorem pure_update_smul (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ)
    (hφ : ∀ᶠ u in cofinite, φ u = indO u) (v : Pl F) (a : ℂ) (g : (κ → Fv F v) → ℂ) :
    pure f (Function.update φ v (a • g)) = a • pure f (Function.update φ v g) := by
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, pure_update f φ hφ]
  ring

end Pure

variable {F : Type} [Field F] [NumberField F]

theorem at_of_mem_latAtV {E : Type} [Field E] [NumberField E] [Algebra F E] {n d : ℕ} {X : Spc F E n}
    {W : Spc F E d} {v : Pl F} {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    At (evFin F v) γ := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, x, -, y, -, rfl⟩ := hz
    intro u hu
    rw [← smul_assoc, ha u hu, zero_smul]
  | zero => intro u _; exact smul_zero u
  | add z z' _ _ hz hz' => intro u hu; rw [smul_add, hz u hu, hz' u hu, add_zero]
  | neg z _ hz => intro u hu; rw [smul_neg, hz u hu, neg_zero]

theorem commutant_pure : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ A : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ), (∀ Φ ∈ schA F (Fin n × Fin d), A Φ ∈ schA F (Fin n × Fin d)) →
    (∀ (v : Pl F) (w : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) w →
      ∀ Φ ∈ schA F (Fin n × Fin d), A (M.co.rho B.ψ w Φ) = M.co.rho B.ψ w (A Φ)) →
    ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = M.vac v) → ∃ f₁ : SInf F (Fin n × Fin d), A (pure f φ) = pure f₁ φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hM A hA hcomm f φ hφSB hφv
  have hvacO : ∀ᶠ u in cofinite, M.vac u = indO u := by
    filter_upwards [hM.std] with u hu
    rw [hu]
    rfl
  have hvacSB : ∀ u, M.vac u ∈ SB _ := fun u => (hM.vac u).1
  obtain ⟨c, hc⟩ := GlobalTheory.T.weil_rep_lattice_scalar_action M B.ψ hM
  have hpv : pure f M.vac ∈ schA F _ := GlobalTheory.T.pure_tensor_mem_schwartz_adelic f M.vac hvacSB hvacO
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.T.weil_rep_scalar_char_of_signature B X W M r s r' s' hB hX hW hM c hc (A (pure f M.vac)) (hA _ hpv)
    fun v γ hγ => by rw [← hcomm v γ (at_of_mem_latAtV hγ) _ hpv, hc v γ hγ f, map_smul]
  have key : ∀ S : Finset (Pl F), ∀ φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) →
      (∀ v ∉ S, φ v = M.vac v) → A (pure f φ) = pure f₁ φ := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro φ _ h
      obtain rfl : φ = M.vac := funext fun v => h v (Finset.notMem_empty v)
      exact hf₁
    | insert v S hvS ih =>
      intro φ hSB hS
      have h0SB : ∀ u, Function.update φ v (M.vac v) u ∈ SB _ := fun u => by
        by_cases h : u = v
        · subst h; rw [Function.update_self]; exact hvacSB u
        · rw [Function.update_of_ne h]; exact hSB u
      have h0S : ∀ u ∉ S, Function.update φ v (M.vac v) u = M.vac u := fun u hu => by
        by_cases h : u = v
        · subst h; rw [Function.update_self]
        · rw [Function.update_of_ne h]; exact hS u (by simp [h, hu])
      have h0O : ∀ᶠ u in cofinite, Function.update φ v (M.vac v) u = indO u := by
        filter_upwards [hvacO, S.finite_toSet.compl_mem_cofinite] with u hu huS
        rw [h0S u huS, hu]
      have hIH := ih _ h0SB h0S
      have hmem0 := GlobalTheory.T.pure_tensor_mem_schwartz_adelic f _ h0SB h0O
      obtain ⟨hc1, hne⟩ := GlobalTheory.T.standard_char_continuous_nontrivial B.ψ hB.std v
      have hφv : φ v ∈ Submodule.span ℂ (Set.range fun p => locOp B.ψ v p (M.vac v)) :=
        GlobalTheory.T.local_span_translates_of_nonzero_schwartz B.ψ v hc1 hne (M.vac v) (φ v) (hvacSB v) (hM.vac v).2.1 (hSB v)
      have hφeq : φ = Function.update (Function.update φ v (M.vac v)) v (φ v) := by
        rw [Function.update_idem, Function.update_eq_self]
      have step : ∀ g ∈ Submodule.span ℂ (Set.range fun p => locOp B.ψ v p (M.vac v)),
          A (pure f (Function.update (Function.update φ v (M.vac v)) v g)) =
            pure f₁ (Function.update (Function.update φ v (M.vac v)) v g) := by
        intro g hg
        induction hg using Submodule.span_induction with
        | mem g hg =>
          obtain ⟨p, rfl⟩ := hg
          obtain ⟨w, hw, hwp⟩ := GlobalTheory.T.exists_local_point_model_eval M v p
          have e1 := GlobalTheory.T.weil_rep_pure_tensor_local M B.ψ v w hw f _ h0O
          have e2 := GlobalTheory.T.weil_rep_pure_tensor_local M B.ψ v w hw f₁ _ h0O
          rw [hwp, Function.update_self, Function.update_idem] at e1 e2
          simp only [Function.update_idem]
          rw [← e1, hcomm v w hw _ hmem0, hIH, e2]
        | zero => rw [pure_update_zero f _ h0O, pure_update_zero f₁ _ h0O, map_zero]
        | add g h _ _ hg hh =>
          rw [pure_update_add f _ h0O, pure_update_add f₁ _ h0O, map_add, hg, hh]
        | smul a g _ hg => rw [pure_update_smul f _ h0O, pure_update_smul f₁ _ h0O, map_smul, hg]
      rw [hφeq]
      exact step _ hφv
  have hfin : {v | φ v ≠ M.vac v}.Finite := Filter.eventually_cofinite.mp hφv
  exact ⟨f₁, key hfin.toFinset φ hφSB fun v hv => by
    by_contra h
    exact hv (hfin.mem_toFinset.mpr h)⟩

end GlobalTheory.FinComm
end
end

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_preserving_operator_local_structure : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ A : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ), (∀ Φ ∈ schA F (Fin n × Fin d), A Φ ∈ schA F (Fin n × Fin d)) →
    (∀ (v : Pl F) (w : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) w →
      ∀ Φ ∈ schA F (Fin n × Fin d), A (M.co.rho B.ψ w Φ) = M.co.rho B.ψ w (A Φ)) →
    ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = M.vac v) → ∃ f₁ : SInf F (Fin n × Fin d), A (pure f φ) = pure f₁ φ := by
  atlas_forward_decl GlobalTheory.FinComm.commutant_pure
end
