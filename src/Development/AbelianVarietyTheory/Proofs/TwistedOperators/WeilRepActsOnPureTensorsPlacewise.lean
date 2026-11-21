import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenLevelFixingThetaFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryComponentAtPlaceLawsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryClosureLocalComponentsOpen
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorStableUnitaryGroupsAtPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPureTensorBaseVectorAndLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulConjSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorPureTensorPlaceByPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorInnerProductEqFinprodLocalInnerProduct

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitary_closure_local_components_open : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → (∀ g : GA D V, {p : Place D | ¬ (gAt V p g ∈ U ∧ gAt V p g ∈ GfC V)}.Finite) ∧ Submonoid.closure ({g : GA D V | ∃ p, gAt V p g = g} ∪ {k : GA D V | k ∈ U ∧ k ∈ GfC V ∧ ∀ p, gAt V p k ∈ U ∧ gAt V p k ∈ GfC V}) = ⊤ := by
  first | exact @GlobalTheory.PlaceGen.gen_by_local | exact GlobalTheory.PlaceGen.gen_by_local | (intros; apply GlobalTheory.PlaceGen.gen_by_local <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pureTensor_innerProduct_eq_finprod_localInnerProducts : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x₁ x₂ : Place D → WO S T → ℂ) (f₁ f₂ : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₁ f₁ → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₂ f₂ → (Function.mulSupport fun p => ipO μ 𝓕 (x₁ p) (x₂ p)).Finite ∧ ipO μ 𝓕 f₁ f₂ = ∏ᶠ p, ipO μ 𝓕 (x₁ p) (x₂ p) := by
  first | exact @GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod | exact GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod | (intros; apply GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor.OmPure

theorem ipO_om_left {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : OmT S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕)
    (g : GA D S) (h : GA D T) {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') :
    ipO μ 𝓕 (om (g, h) f) f' = ipO μ 𝓕 f (om (g⁻¹, h⁻¹) f') := by
  have e : om (g, h) (om (g⁻¹, h⁻¹) f') = f' := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  have k : ipO μ 𝓕 (om (g, h) f) (om (g, h) (om (g⁻¹, h⁻¹) f')) = ipO μ 𝓕 f (om (g⁻¹, h⁻¹) f') :=
    GlobalTheory.WeilInner.om_inner D ψ S T χS χT om hW μ 𝓕 hμ (g, h) f _ hf (hW.om_pres _ _ hf')
  rwa [e] at k

theorem isPure_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (g : GA D S) (h : GA D T), {p : Place D | om (gAt S p g, gAt T p h) f₀ ≠ f₀}.Finite → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g⁻¹, gAt T p h⁻¹) f₀) (om (g⁻¹, h⁻¹) f₀) → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ g h hfin hinv x f hx
  have hpres := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hW.std S T).1
  have h0 := base_theta hB
  refine ⟨⟨fun p => GlobalTheory.T.localFactor_stable_unitaryGroupsAtPlace D ψ θ S T χS χT om sS sT ΛS ΛT hW (base_inf hB) p _ (hx.1.1 p) g h, ?_⟩,
    hW.om_pres _ _ hx.2.1, fun w => ?_⟩
  · refine (hfin.union hx.1.2).subset fun p hp => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    exact hp (by simp only [hc.2, hc.1])
  · have hy := GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ _ _ hinv (actO S T g⁻¹ h⁻¹ w)
    have hp := GlobalTheory.T.pureTensor_innerProduct_eq_finprod_localInnerProducts D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ _ _ _ _ hx hy
    have e : (fun p => ipO μ 𝓕 (om (gAt S p g, gAt T p h) (x p)) (heisO ψ S T (wAt p w) f₀)) =
        fun p => ipO μ 𝓕 (x p) (heisO ψ S T (wAt p (actO S T g⁻¹ h⁻¹ w)) (om (gAt S p g⁻¹, gAt T p h⁻¹) f₀)) := by
      funext p
      rw [ipO_om_left hW hμ _ _ (hx.1.1 p).1 (hpres _ _ h0), ← gAt_inv, ← gAt_inv, hW.om_heis _ _ _ _ h0,
        ((GlobalTheory.T.adelicUnitaryComponentAtPlace_laws D).2 S T p g⁻¹ h⁻¹ w).2]
    refine ⟨by rw [e]; exact hp.1, ?_⟩
    rw [e, ipO_om_left hW hμ _ _ hx.2.1 (hpres _ _ h0), hW.om_heis _ _ _ _ h0]
    exact hp.2

end GlobalTheory.PlaceTensor.OmPure
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_placeByPlace_on_pureTensors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (g : GA D S) (h : GA D T), {p : Place D | om (gAt S p g, gAt T p h) f₀ ≠ f₀}.Finite → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g⁻¹, gAt T p h⁻¹) f₀) (om (g⁻¹, h⁻¹) f₀) → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f) := by
  atlas_forward_decl GlobalTheory.PlaceTensor.OmPure.isPure_om
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor.PureOm

theorem isPure_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ (g : GA D S) (h : GA D T), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ
  obtain ⟨U, U', hU, hU', hfix⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D ψ hW.std S T om (GlobalTheory.Ker.isWeak_of_datum hW)
    hW.om_cont f₀ (base_theta hB)
  have hgen := GlobalTheory.T.weilRepresentation_placeByPlace_on_pureTensors D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ
  obtain ⟨hp0, hploc⟩ := GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ
  have hstab := GlobalTheory.T.localFactor_stable_unitaryGroupsAtPlace D ψ θ S T χS χT om sS sT ΛS ΛT hW (base_inf hB)
  have hgat := (GlobalTheory.T.adelicUnitaryComponentAtPlace_laws D).1
  let Good : GA D S → GA D T → Prop := fun g h => ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ),
    IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f)
  have om1 : ∀ u : WO S T → ℂ, om (1, 1) u = u := fun u => by
    have : om (1, 1) = 1 := map_one om
    rw [this]; rfl
  have omm : ∀ (g g' : GA D S) (h h' : GA D T) (u : WO S T → ℂ),
      om (g * g', h * h') u = om (g, h) (om (g', h') u) := fun g g' h h' u => by
    have : om (g * g', h * h') = om (g, h) * om (g', h') := map_mul om (g, h) (g', h')
    rw [this]; rfl
  have G1 : Good 1 1 := fun x f hx => by
    simpa only [gAt_one, om1] using hx
  have Gmul : ∀ g h g' h', Good g h → Good g' h' → Good (g * g') (h * h') := fun g h g' h' a b x f hx => by
    simpa only [gAt_mul, omm] using a _ _ (b x f hx)
  have Gloc : ∀ q g h, gAt S q g = g → gAt T q h = h → Good g h := fun q g h hg hh => by
    have e1 : ∀ p, p ≠ q → gAt S p g = 1 := fun p hp => by
      rw [← hg]; exact (hgat S q g).2.2 p hp
    have e2 : ∀ p, p ≠ q → gAt T p h = 1 := fun p hp => by
      rw [← hh]; exact (hgat T q h).2.2 p hp
    refine hgen g h ?_ ?_
    · refine (Set.finite_singleton q).subset fun p hp => ?_
      by_contra hpq
      exact hp (by rw [e1 p hpq, e2 p hpq, om1])
    · have := hploc q (fun p => om (gAt S p g⁻¹, gAt T p h⁻¹) f₀) (hstab q f₀ (base_isLocal hB q) _ _)
        (fun p hp => by simp only [gAt_inv, e1 p hp, e2 p hp, inv_one, om1])
      have e : om (gAt S q g⁻¹, gAt T q h⁻¹) f₀ = om (g⁻¹, h⁻¹) f₀ := by rw [gAt_inv, gAt_inv, hg, hh]
      simp only [e] at this
      exact this
  have Gfin : ∀ g h, (g ∈ U ∧ g ∈ GfC S ∧ ∀ p, gAt S p g ∈ U ∧ gAt S p g ∈ GfC S) →
      (h ∈ U' ∧ h ∈ GfC T ∧ ∀ p, gAt T p h ∈ U' ∧ gAt T p h ∈ GfC T) → Good g h := fun g h hg hh => by
    refine hgen g h ?_ ?_
    · refine Set.finite_empty.subset fun p hp => ?_
      exact hp (hfix _ (hg.2.2 p).1 (hg.2.2 p).2 _ (hh.2.2 p).1 (hh.2.2 p).2)
    · have e : (fun p => om (gAt S p g⁻¹, gAt T p h⁻¹) f₀) = fun _ => f₀ := funext fun p => by
        rw [gAt_inv, gAt_inv]
        exact hfix _ (inv_mem (hg.2.2 p).1) (inv_mem (hg.2.2 p).2) _ (inv_mem (hh.2.2 p).1) (inv_mem (hh.2.2 p).2)
      rw [e, hfix _ (inv_mem hg.1) (inv_mem hg.2.1) _ (inv_mem hh.1) (inv_mem hh.2.1)]
      exact hp0
  have GS : ∀ g, Good g 1 := fun g => by
    have hg : g ∈ Submonoid.closure _ := (GlobalTheory.T.adelicUnitary_closure_local_components_open D S U hU).2 ▸ Submonoid.mem_top g
    induction hg using Submonoid.closure_induction with
    | mem g hg =>
      rcases hg with ⟨q, hq⟩ | hg
      · exact Gloc q g 1 hq (gAt_one T q)
      · exact Gfin g 1 hg ⟨one_mem _, one_mem _, fun p => by rw [gAt_one]; exact ⟨one_mem _, one_mem _⟩⟩
    | one => exact G1
    | mul a b _ _ ha hb => simpa only [mul_one] using Gmul _ _ _ _ ha hb
  have GT : ∀ h, Good 1 h := fun h => by
    have hh : h ∈ Submonoid.closure _ := (GlobalTheory.T.adelicUnitary_closure_local_components_open D T U' hU').2 ▸ Submonoid.mem_top h
    induction hh using Submonoid.closure_induction with
    | mem h hh =>
      rcases hh with ⟨q, hq⟩ | hh
      · exact Gloc q 1 h (gAt_one S q) hq
      · exact Gfin 1 h ⟨one_mem _, one_mem _, fun p => by rw [gAt_one]; exact ⟨one_mem _, one_mem _⟩⟩ hh
    | one => exact G1
    | mul a b _ _ ha hb => simpa only [mul_one] using Gmul _ _ _ _ ha hb
  intro x f hx g h
  have := Gmul _ _ _ _ (GS g) (GT h)
  rw [mul_one, one_mul] at this
  exact this x f hx

end GlobalTheory.PlaceTensor.PureOm
end
