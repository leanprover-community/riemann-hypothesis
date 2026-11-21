import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AbsNormGeTwo
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnramifiedFactorEqOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalFactorsPosTypicalGeneral
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdFull
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolVFinal
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CanonicalAnalyticData

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.ProdConvCut

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)

def ProdConvNew : Prop :=
  (∀ v, (TypAt X v → 0 < MX X u u' ψ v) ∧ 0 < localVolumeUnit X ψ v ∧ 0 < ZZX X u u' ψ v ∧ (∀ l, 0 < PPX X u u' ψ l v) ∧
    0 < alX X u u' v) ∧
  True ∧ True ∧
  Multipliable (fun v : OrdX X => localVolumeUnit X ψ v.1) ∧ 0 < ∏' v : OrdX X, localVolumeUnit X ψ v.1 ∧
  Multipliable (ZZX X u u' ψ) ∧ 0 < ∏' v : PlX X, ZZX X u u' ψ v ∧
  (∀ l, Multipliable (PPX X u u' ψ l) ∧ 0 < ∏' v : PlX X, PPX X u u' ψ l v) ∧
  Multipliable (fun v : OrdX X => alX X u u' v.1) ∧ 0 < ∏' v : OrdX X, alX X u u' v.1 ∧
  Multipliable (jacX X) ∧ 0 < ∏' v : PlX X, jacX X v

private theorem multipliable_and_tprod_pos_of_finite_mulSupport {ι : Type*} (f : ι → ℝ) (hpos : ∀ i, 0 < f i) (hfin : (Function.mulSupport f).Finite) :
    Multipliable f ∧ 0 < ∏' i, f i := by
  refine ⟨multipliable_of_finite_mulSupport hfin, ?_⟩
  rw [tprod_eq_prod' (s := hfin.toFinset) (by simp)]
  exact Finset.prod_pos fun i _ => hpos i

theorem prodConvNew_of (h1 : VolOneAEC X u u' ψ)
    (hpos : ∀ v, 0 < localVolumeUnit X ψ v ∧ 0 < ZZX X u u' ψ v ∧ (∀ l, 0 < PPX X u u' ψ l v) ∧ 0 < jacX X v)
    (hM : ∀ v, TypAt X v → 0 < MX X u u' ψ v) (hal : ∀ v, 0 < alX X u u' v) (h3 : AlConvC X u u') :
    ProdConvNew X u u' ψ := by
  have hS : ∀ g : PlX X → ℝ, (∀ v, g v ≠ 1 → ¬ (localVolumeUnit X ψ v = 1 ∧ ZZX X u u' ψ v = 1 ∧
      (∀ l, PPX X u u' ψ l v = 1) ∧ jacX X v = 1)) → (Function.mulSupport g).Finite :=
    fun g hg => h1.subset fun v hv => hg v hv
  have hU : (Function.mulSupport fun v : OrdX X => localVolumeUnit X ψ v.1).Finite := by
    refine (h1.preimage Subtype.val_injective.injOn).subset fun v hv => ?_
    intro h
    exact hv h.1
  have hZ := hS (ZZX X u u' ψ) fun v hv h => hv h.2.1
  have hP : ∀ l, (Function.mulSupport (PPX X u u' ψ l)).Finite := fun l => hS _ fun v hv h => hv (h.2.2.1 l)
  have hJ := hS (jacX X) fun v hv h => hv h.2.2.2
  have rU := multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v : OrdX X => (hpos v.1).1) hU
  have rZ := multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v => (hpos v).2.1) hZ
  have rJ := multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v => (hpos v).2.2.2) hJ
  exact ⟨fun v => ⟨hM v, (hpos v).1, (hpos v).2.1, (hpos v).2.2.1, hal v⟩, trivial, trivial, rU.1, rU.2, rZ.1, rZ.2,
    fun l => multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v => (hpos v).2.2.1 l) (hP l), h3.1, h3.2, rJ.1, rJ.2⟩

theorem prodConvNew_gen (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ)
    (hs : IsStdChar ψ) (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w)
    (hpos : ∀ v, (¬ TypAt X v → 0 < localVolumeUnit X ψ v) ∧ 0 < ZZX X u u' ψ v ∧ (∀ l, 0 < PPX X u u' ψ l v) ∧
      0 < jacX X v) :
    ProdConvNew X u u' ψ := by
  have hk : 1 ≤ D.R.k := Formalism.MainNotions.S.k_pos (D := D)
  refine prodConvNew_of X u u' ψ (VolOneAEC_holds (X := X) (u := u) (u' := u') (ψ := ψ) hψ hs) (fun v => ⟨?_, (hpos v).2.1,
    (hpos v).2.2.1, (hpos v).2.2.2⟩) (fun v h => (local_factors_pos_typical_general X hb ψ hψ hs hloc u u' v h).1)
    (fun v => lt_of_lt_of_le (Real.exp_pos _) (alX_bounds (X := X) (u := u) (u' := u') hk v).1)
    (AlConvC_holds (X := X) (u := u) (u' := u'))
  by_cases h : TypAt X v
  · exact (local_factors_pos_typical_general X hb ψ hψ hs hloc u u' v h).2
  · exact (hpos v).1 h


end Formalism.L2.SG.Pf.ProdConvCut2
end
end

section
noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.ProdConvCut2

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcVal
  Formalism.L2.SG.Pf.NcVal.VolOrdW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pp_pos_typ_gen {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (ψ : AddChar (AF X.B.I.F) ℂ)
    (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) (u u' : D.what₂.Word) (v : PlX X) (hv : TypAt X v)
    (l : Fin (D.R.rS + 1)) : 0 < PPX X u u' ψ l v := by
  have hTF := Formalism.L2.SG.Pf.typFacts_holds X hb u u' ⟨v, hv⟩

  have hnt : X.B.I.cm.sig ≠ AlgHom.id X.B.I.F X.B.I.E := by
    have hmax : v.asIdeal.IsMaximal := v.isMaximal
    obtain ⟨P, hPmax, -⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 X.B.I.E) v.asIdeal
      (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp
          (FaithfulSMul.algebraMap_injective (𝓞 X.B.I.F) (𝓞 X.B.I.E))]
        exact bot_le)
    obtain ⟨θ, t, htθ, hnot⟩ := X.B.I.cm.cmUnram.2.2 P hPmax
    intro h
    apply hnot
    have hθ : (t : X.B.I.E) = θ := by
      have h1 : X.B.I.cm.sig (θ : X.B.I.E) = star (θ : X.B.I.E) := rfl
      rw [h, AlgHom.id_apply] at h1
      have htθ' : (t : X.B.I.E) = star (θ : X.B.I.E) := htθ
      rw [htθ', ← h1]
    have : θ - t = 0 := by ext; simp [hθ]
    rw [this]
    exact P.zero_mem

  have hid : ∃ x : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1 := by
    by_contra h
    have he := hTF.2.2.1
    unfold etaV at he
    rw [if_neg h] at he
    exact absurd he (by decide)
  have hS : PI.UnitaryGroupMassFormula.LocJacTyp.SplitHyp X.B.I.cm.sig v := ⟨X.B.I.cm.deg2, hnt, hid⟩
  have hg : 0 < gAt X v := hTF.1.pos
  have hA := SdW.sdFromAnn_holds ψ v (dV v) hψ X.B.I.cm.deg2 (dV_ne_zero v)
    (annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different hψ hs v) Unit
  haveI := hA.1
  have hP := PI.UnitaryGroupMassFormula.LocJacTyp.parabolic_volume X.B.I.cm.sig v (gAt X v) D.R.rS (Tw u) (Tw u')
    (absV v (dV v) ^ Fintype.card Unit) hS hg hTF.2.2.2.1 (sdE (E := X.B.I.E) ψ v Unit) hA.1 hA.2.2 l
  have hP' : ((sdE (E := X.B.I.E) ψ v Unit) ((fun c : Unit → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E => c ()) ⁻¹'
      PPTyp X.B.I.cm.sig v (gAt X v) D.R.rS (Tw u) (Tw u') l)).toReal =
      absV v (dV v) ^ Fintype.card Unit * PI.LocJacTyp.absV v (gAt X v : Fv X.B.I.F v) ^ 3 *
        (PI.LocJacTyp.absV v (PI.LocJacTyp.alp v D.R.rS l) ^ 4)⁻¹ := hP
  unfold PPX volC
  rw [if_pos hv, hP']
  have hd : 0 < absV v (dV v) := absV_pos v (dV_ne_zero v)
  have hgv : (gAt X v : Fv X.B.I.F v) ≠ 0 := by exact_mod_cast hg.ne'
  have h1 : 0 < PI.LocJacTyp.absV v (gAt X v : Fv X.B.I.F v) := PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v hgv
  have ha : PI.LocJacTyp.alp v D.R.rS l ≠ 0 := alp_ne_zero v D.R.rS l
  have h2 : 0 < PI.LocJacTyp.absV v (PI.LocJacTyp.alp v D.R.rS l) := PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v ha
  positivity


end Formalism.L2.SG.Pf.ProdConvCut2
end
end

section
noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.LocalPositivity

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcVal
  Formalism.L2.SG.Pf.NcVal.VolOrdW Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.SG.TypedSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem pos_of_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 < a / b) : 0 < a ∧ 0 < b := by
  rcases div_pos_iff.1 h with h' | h'
  · exact h'
  · exact absurd ha (not_le.2 h'.1)

theorem localVolumeUnit_pos_and_ZZX_pos (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ)
    (hTT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hg : ∀ v, TypAt X v → 0 < gAt X v) (v : PlX X) :
    0 < localVolumeUnit X ψ v ∧ 0 < ZZX X u u' ψ v := by
  have hU : 0 ≤ localVolumeUnit X ψ v := ENNReal.toReal_nonneg
  have hZ : 0 ≤ ZZX X u u' ψ v := ENNReal.toReal_nonneg
  by_cases hv : TypAt X v
  · have e := volTypV_holds X u u' ψ hψ hs hTT v hv
    exact pos_of_div hU hZ (by rw [e]; exact pow_pos (by exact_mod_cast hg v hv) _)
  · have e := volOrdV_holds X u u' ψ hψ hs v hv
    exact pos_of_div hU hZ (by rw [e]; exact Real.rpow_pos_of_pos (absV_pos v (dV_ne_zero v)) _)

theorem pp_pos_ord (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) {v : PlX X} (hv : ¬ TypAt X v)
    (l : Fin (D.R.rS + 1)) : 0 < PPX X u u' ψ l v := by
  have hN : SdNormDV X ψ := sdNormDV_of X ψ (annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different) hψ hs
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH, -, hO⟩ := hN v hv Unit
  have := hH
  have hset : (fun c : Unit → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E => c ()) ⁻¹' PPOrd (E := X.B.I.E) v D.R.rS l =
      Set.univ.pi fun _ : Unit => {c | sc (E := X.B.I.E) v (alp v D.R.rS l ^ 2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [PPOrd, Set.mem_pi]
    exact ⟨fun h i => h, fun h => h ()⟩
  unfold PPX volC
  rw [if_neg hv, hset, SdW.boxScaleL_holds v Unit hfin (sdE (E := X.B.I.E) ψ v Unit)
    (fun _ : Unit => alp v D.R.rS l ^ 2) (fun _ => pow_ne_zero _ (alp_ne_zero v D.R.rS l)), hO]
  refine mul_pos (pow_pos (absV_pos v (dV_ne_zero v)) _) (Finset.prod_pos fun q _ => ?_)
  exact inv_pos.2 (pow_pos (absV_pos v (pow_ne_zero _ (alp_ne_zero v D.R.rS l))) 2)

theorem jac_pos (hg : ∀ v, TypAt X v → 0 < gAt X v) (v : PlX X) : 0 < jacX X v := by
  unfold jacX jacS
  refine Finset.prod_pos fun l _ => ?_
  have hx : (∏ i ∈ Finset.univ.filter (fun i : Fin (D.R.rS + 1) => (i : ℕ) ≤ (l : ℕ)), alp v D.R.rS i ^ 2) *
      (if TypAt X v then ((gAt X v : Fv X.B.I.F v)⁻¹) ^ ((l : ℕ) + 1) else 1) ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (alp_ne_zero v D.R.rS i)) ?_
    split_ifs with ht
    · refine pow_ne_zero _ (inv_ne_zero ?_)
      exact_mod_cast (hg v ht).ne'
    · exact one_ne_zero
  exact pow_pos (pow_pos (absV_pos v hx) 2) 2

end Formalism.L2.SG.Pf.LocalPositivity
end
end

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol

theorem level_congr_mod_sq (D : D7) (u u' : D.what₂.Word) :
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD Formalism.MainNotions.S.Lat.gS D ^ 2] := by
  have h : Formalism.MainNotions.S.Lat.gS D ^ 2 ∣ D.modT := by unfold Formalism.MainNotions.S.Lat.gS; exact D.gg_dvd_modT
  exact (D.T_modEq_of_dvd u h).trans (D.T_modEq_of_dvd u' h).symm


theorem prodConvNew_holds_gen {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ)
    (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w) (u u' : D.what₂.Word) : ProdConvNew X u u' ψ := by
  have hg : ∀ v, TypAt X v → 0 < gAt X v := fun v hv =>
    (Formalism.L2.SG.Pf.typFacts_holds X hb u u' ⟨v, hv⟩).1.pos
  have hUZ := Formalism.L2.SG.Pf.LocalPositivity.localVolumeUnit_pos_and_ZZX_pos X u u' ψ hψ hs (level_congr_mod_sq D u u') hg
  refine prodConvNew_gen X u u' ψ hb hψ hs hloc fun v => ⟨fun _ => (hUZ v).1, (hUZ v).2, fun l => ?_,
    Formalism.L2.SG.Pf.LocalPositivity.jac_pos X hg v⟩
  by_cases hv : TypAt X v
  · exact pp_pos_typ_gen X hb ψ hψ hs u u' v hv l
  · exact Formalism.L2.SG.Pf.LocalPositivity.pp_pos_ord X u u' ψ hψ hs hv l



end Formalism.L2.SG.Pf.ProdConvCut2
end
end

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol

theorem prodConv_holds_gen {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ)
    (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w) (u u' : D.what₂.Word) : ProdConv X u u' ψ :=
  prodConvNew_holds_gen X hb ψ hψ hs hloc u u'

theorem prodConv_holds {D : D7} (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u u' : D.what₂.Word) : ProdConv T.X u u' T.ψ :=
  prodConv_holds_gen T.X T.hb T.ψ T.ψ_char T.ψ_std T.locCompat u u'

theorem prodConvAll_holds : Formalism.L2.SG.PoincareAmplitudeLowerBounds.ProdConvAll :=
  fun _ T u u' _ _ => prodConv_holds T u u'

theorem prodConv_onTied :
    Formalism.L2.SG.NGAnalytic.MassDataLemmas.OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' _ hb X0 ψ hT
  exact prodConv_holds_gen X hb ψ hT.2.1 hT.2.2.1 hT.2.2.2.2.1 u u'

end Formalism.L2.SG.Pf.ProdConvCut2
end
end
