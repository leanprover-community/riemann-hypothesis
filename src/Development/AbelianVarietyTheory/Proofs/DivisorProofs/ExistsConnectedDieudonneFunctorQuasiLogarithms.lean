import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstLiftXPowFrob
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectedPDivGroupChartOfIsConn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawOfIsLawOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfAddFormalGroupLawEvalPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDifferentialsConnectedPDivGroupCoordina
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFormalGroupCocycleIffMemCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFormalGroupLawCoboundaryOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogReduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPullbackTeichmullerLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffSubstZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WittFrobeniusPowEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffSubstOfZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionCommutesFormalGroupLawCoboundaries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePowerSeriesOfCompatibleSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEvalCommutesSubstAndAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupFormalLawCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearPDivGroupHomEvalTwoVariableSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapFormalGroupLawQuasiLogarithms

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMapOf_add_formalGroupLawEvalPoints : ∀ (p : ℕ) (k : Type) [CommRing k] (d e : ℕ) (G H : PDivGroup p k) (c : Chart G d) (c' : Chart H e), ∀ (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (f g : G ⟶ H) (φ ψ : Fin e → MvPowerSeries (Fin d) k), c'.IsLawOf ν → c.IsMapOf c' f φ → c.IsMapOf c' g ψ → c.IsMapOf c' (f + g) (op ν φ ψ) := by
  first | exact @GlobalTheory.Katz.Chart.isMapOf_add | exact GlobalTheory.Katz.Chart.isMapOf_add | (intros; apply GlobalTheory.Katz.Chart.isMapOf_add <;> assumption)
end

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

noncomputable section

namespace GlobalTheory.Katz

theorem exists_rigMap (p : ℕ) (k : Type) [Field k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d) :
    ∃ ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] G.RigExt,
      (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) →
        (∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) := by
  classical
  let L : MvPowerSeries (Fin d ⊕ Fin d) k →ₗ[k] (∀ n, G.A n ⊗[k] G.A n) :=
    LinearMap.pi fun n => (c.ev₂ n).toLinearMap
  let S : Submodule k (MvPowerSeries (Fin d ⊕ Fin d) k) := G.cocycles.comap L
  let T₀ : S →ₗ[k] G.cocycles := L.restrict (fun x hx => hx)
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T₀
  have hU := (GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c).1
  let U : (Fin d → k) →ₗ[k] G.omega :=
    { toFun := fun w => ⟨fun n => ∑ i, w i • dUnit k (c.x n i), hU w⟩
      map_add' := fun a b => Subtype.ext (funext fun n => by
        simp [add_smul, Finset.sum_add_distrib])
      map_smul' := fun r a => Subtype.ext (funext fun n => by
        simp [Finset.smul_sum, smul_smul]) }
  refine ⟨G.rigMk ∘ₗ T.prodMap U, fun s w z u hz hu => ?_⟩
  have hs : s ∈ S := by
    change L s ∈ G.cocycles
    have : L s = z.1 := funext fun n => (hz n).symm
    rw [this]; exact z.2
  have h1 : T s = z := by
    have := LinearMap.congr_fun hT ⟨s, hs⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    exact Subtype.ext (funext fun n => (hz n).symm)
  have h2 : U w = u := Subtype.ext (funext fun n => (hu n).symm)
  simp [h1, h2]

end GlobalTheory.Katz
end
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidifiedExtension_of_series_pair : ∀ (p : ℕ) (k : Type) [Field k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∃ ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] G.RigExt, (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) → (∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) := by
  atlas_forward_decl GlobalTheory.Katz.exists_rigMap
end

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem GlobalTheory.Katz.isRigOf_rigMk : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] G.RigExt), c.IsLawOf μ → (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) → (∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) → IsRigOf μ ρ := by
  intro p k _ d G c μ ρ hμ hρ
  have hcoc := GlobalTheory.T.isSymmetricFormalGroupCocycle_iff_mem_cocycles p k d G c μ hμ
  have hdu := GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d
  have hlaw := ((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).2
  have hom := GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c
  have hone := GlobalTheory.T.functions_eq_series_in_chart p k d G c
  have hpres := (GlobalTheory.T.chart_square_coordinates_present_levels p k d G c).2
  constructor
  · intro v
    obtain ⟨⟨z, u⟩, rfl⟩ := Submodule.mkQ_surjective _ v
    obtain ⟨s, hs, -⟩ := hpres z.1 (fun n => (z.2 n).2)
    obtain ⟨w, hw, -⟩ := hom.2 u
    have hz : (fun n => c.ev₂ n s) = z.1 := funext hs
    refine ⟨s, w, (hcoc s).2 (hz ▸ z.2), ?_⟩
    exact hρ s w z u (fun n => (hs n).symm) hw
  · intro s w hs
    let z : G.cocycles := ⟨fun n => c.ev₂ n s, (hcoc s).1 hs⟩
    let u : G.omega := ⟨fun n => ∑ i, w i • dUnit k (c.x n i), hom.1 w⟩
    rw [hρ s w z u (fun _ => rfl) (fun _ => rfl)]
    change Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    constructor
    · rintro ⟨B, hB⟩
      rw [LinearMap.prod_apply, Prod.mk.injEq] at hB
      obtain ⟨b, hb, -⟩ := hone.2.2 B.1 B.2
      refine ⟨b, ?_, ?_⟩
      · have hz2 : ∀ n, pullbackTwo (G.res n) (c.ev₂ (n + 1) s) = c.ev₂ n s := fun n => hone.2.1 n s
        obtain ⟨t, -, ht⟩ := hpres (fun n => c.ev₂ n s) hz2
        have h1 := ht s (fun _ => rfl)
        have h2 := ht (cob1 μ b) (fun n => by
          rw [(hlaw n b).2, hb n]
          exact (congrArg (fun y : G.cocycles => y.1 n) hB.1))
        exact h1.trans h2.symm
      · obtain ⟨w', -, hw'⟩ := hom.2 u
        have e1 := hw' w (fun _ => rfl)
        have e2 := hw' (lin b) (fun n => by
          rw [← (hdu (G.A n) (c.x n) (c.nil n) (c.aug n) b).2]
          change _ = dUnit k (c.ev n b)
          rw [hb n]
          exact (congrArg (fun y : G.omega => y.1 n) hB.2).symm)
        exact e1.trans e2.symm
    · rintro ⟨b, rfl, rfl⟩
      refine ⟨⟨fun n => c.ev n b, fun n => hone.1 n b⟩, ?_⟩
      rw [LinearMap.prod_apply, Prod.mk.injEq]
      constructor
      · apply Subtype.ext; funext n
        exact ((hlaw n b).2).symm
      · apply Subtype.ext; funext n
        exact (hdu (G.A n) (c.x n) (c.nil n) (c.aug n) b).2
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedExtension_presentation_of_series_pairs : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] G.RigExt), c.IsLawOf μ → (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) → (∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) → IsRigOf μ ρ := by
  atlas_forward_decl GlobalTheory.Katz.isRigOf_rigMk
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_formalGroupLawCoboundaryOne_eq_zero : ∀ (p : ℕ) (k : Type) [CommRing k] (h : (p : k) = 0) (d : ℕ) (G : PDivGroup p k) (c : Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ b, cob1 μ b = 0 → b = 0 := by
  first | exact @GlobalTheory.Katz.eq_zero_of_cob1_eq_zero | exact GlobalTheory.Katz.eq_zero_of_cob1_eq_zero | (intros; apply GlobalTheory.Katz.eq_zero_of_cob1_eq_zero <;> assumption)
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_pullback_teichmullerLift : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d e : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (hμ : IsLaw μ) (hν : IsLaw ν) (φ : Fin e → MvPowerSeries (Fin d) k), IsHom μ ν φ → ∀ f ∈ quasiLog p hν, subst (fun j => Katz.lift p (φ j)) f ∈ quasiLog p hμ ∧ (∀ c, Red p (cob1 (fun j => Katz.lift p (ν j)) f) c → Red p (cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f)) (pull2 φ c)) ∧ ∀ w, RedV p (lin f) w → RedV p (lin (subst (fun j => Katz.lift p (φ j)) f)) (pullLin φ w) := by
  first | exact @GlobalTheory.KatzPull.quasiLog_pull | exact GlobalTheory.KatzPull.quasiLog_pull | (intros; apply GlobalTheory.KatzPull.quasiLog_pull <;> assumption)
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Katz.ModHom

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]

theorem red_lift {σ : Type} (g : MvPowerSeries σ k) : Red p (Katz.lift p g) g := by
  intro α
  exact ⟨WittVector.teichmuller p (coeff α g), coeff_lift p g α, by
    simp [WittVector.constantCoeff_apply]⟩

def substW {σ τ : Type} [Finite σ] (u : σ → MvPowerSeries τ (Fr p k)) (hu : ∀ i, constantCoeff (u i) = 0) :
    MvPowerSeries σ (Fr p k) →ₗ[WittVector p k] MvPowerSeries τ (Fr p k) where
  toFun f := subst u f
  map_add' f g := subst_add (hasSubst_of_constantCoeff_zero hu) f g
  map_smul' r f := by
    rw [← algebraMap_smul (Fr p k) r f, subst_smul (hasSubst_of_constantCoeff_zero hu),
      algebraMap_smul]
    rfl

variable [PerfectRing k p]

def modMap {d e : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k}
    {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k} (hμ : IsLaw μ) (hν : IsLaw ν)
    {φ : Fin e → MvPowerSeries (Fin d) k} (hφ : IsHom μ ν φ) : Mod p hν →ₗ[WittVector p k] Mod p hμ :=
  Submodule.mapQ _ _
    (((substW p (fun j => Katz.lift p (φ j)) fun j => constantCoeff_lift p (hφ.const j)).comp
      (quasiLog p hν).subtype).codRestrict (quasiLog p hμ)
      fun f => (GlobalTheory.T.quasiLogarithm_pullback_teichmullerLift p k d e μ ν hμ hν φ hφ f.1 f.2).1)
    (by
      intro f hf
      rw [Submodule.mem_comap]
      change f.1 ∈ intBy p k (Fin e) 1 at hf
      change subst (fun j => Katz.lift p (φ j)) f.1 ∈ intBy p k (Fin d) 1
      exact (GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin e) (Fin d) _ φ (fun j => constantCoeff_lift p (hφ.const j))
        (fun j => red_lift p (φ j))).2 1 f.1 hf)

theorem modMap_mk {d e : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k}
    {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k} (hμ : IsLaw μ) (hν : IsLaw ν)
    {φ : Fin e → MvPowerSeries (Fin d) k} (hφ : IsHom μ ν φ) (f : quasiLog p hν) :
    ∃ g : quasiLog p hμ, g.1 = subst (fun j => Katz.lift p (φ j)) f.1 ∧
      modMap p hμ hν hφ (Submodule.Quotient.mk f) = Submodule.Quotient.mk g :=
  ⟨_, rfl, rfl⟩

end GlobalTheory.Katz.ModHom

theorem GlobalTheory.Katz.ModHom.map_exists : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d e : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (hμ : IsLaw μ) (hν : IsLaw ν) (φ : Fin e → MvPowerSeries (Fin d) k), IsHom μ ν φ → ∃ m : Mod p hν →ₗ[WittVector p k] Mod p hμ, ∀ f : quasiLog p hν, ∃ g : quasiLog p hμ, g.1 = subst (fun j => Katz.lift p (φ j)) f.1 ∧ m (Submodule.Quotient.mk f) = Submodule.Quotient.mk g := by
  intro p _ k _ _ _ d e μ ν hμ hν φ hφ
  exact ⟨GlobalTheory.Katz.ModHom.modMap p hμ hν hφ, GlobalTheory.Katz.ModHom.modMap_mk p hμ hν hφ⟩
end
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem wittModule_free_finite_of_reduction : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (M V : Type) [AddCommGroup M] [Module (WittVector p k) M] [AddCommGroup V] [Module k V] [Module.Finite k V] (r : M →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] V), IsHausdorff (Ideal.span {(p : WittVector p k)}) M → (∀ m : M, (p : WittVector p k) • m = 0 → m = 0) → Function.Surjective r → (∀ m, r m = 0 → ∃ n, m = p • n) → Module.Free (WittVector p k) M ∧ Module.Finite (WittVector p k) M := by
  intro p _ k _ _ _ M V _ _ _ _ _ r hH htf hr hker
  classical
  let I : Ideal (WittVector p k) := Ideal.span {(p : WittVector p k)}
  have hpow : ∀ (j : ℕ) (m : M), ((p : WittVector p k) ^ j) • m = 0 → m = 0 := by
    intro j
    induction j with
    | zero => intro m h; simpa using h
    | succ j ih =>
      intro m h
      rw [pow_succ, mul_smul] at h
      exact htf m (ih _ h)
  haveI : Module.IsTorsionFree (WittVector p k) M :=
    Module.IsTorsionFree.of_smul_eq_zero fun a m h => by
      by_cases ha : a = 0
      · exact Or.inl ha
      right
      obtain ⟨j, u, rfl⟩ := WittVector.exists_eq_pow_p_mul' a ha
      rw [mul_smul] at h
      have h1 := hpow j _ h
      rw [← Units.smul_def] at h1
      exact (smul_eq_zero_iff_eq u).mp h1
  haveI : IsHausdorff I M := hH
  let b := Module.finBasis k V
  choose m hm using fun i => hr (b i)
  let F : (Fin (Module.finrank k V) → WittVector p k) →ₗ[WittVector p k] M :=
    Fintype.linearCombination (WittVector p k) m
  haveI : IsPrecomplete I (Fin (Module.finrank k V) → WittVector p k) :=
    GlobalTheory.isPrecomplete_pi I _
  have hs : Function.Surjective F := by
    apply surjective_of_mkQ_comp_surjective (I := I)
    intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    refine ⟨fun i => WittVector.teichmuller p (b.repr (r x) i), ?_⟩
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    have h0 : r (F (fun i => WittVector.teichmuller p (b.repr (r x) i)) - x) = 0 := by
      rw [map_sub, Fintype.linearCombination_apply, map_sum]
      simp only [map_smulₛₗ, hm, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
      rw [sub_eq_zero]
      exact b.sum_repr (r x)
    obtain ⟨y, hy⟩ := hker _ h0
    rw [hy]
    have : ((p : WittVector p k)) • y ∈ (I • ⊤ : Submodule (WittVector p k) M) :=
      Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
    simpa [Nat.cast_smul_eq_nsmul] using this
  haveI : Module.Finite (WittVector p k) M := Module.Finite.of_surjective F hs
  exact ⟨Module.free_of_finite_type_torsion_free', inferInstance⟩

end GlobalTheory
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem mod_noPTorsion : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ), (∀ b, cob1 μ b = 0 → b = 0) → ∀ m : Mod p h, (p : WittVector p k) • m = 0 → m = 0 := by
  intro p _ k _ _ _ d μ h hb m hm
  obtain ⟨R1, R2, -, -, -, R6, ZariskiNoetherianInduction⟩ := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d)
  obtain ⟨-, R2', -, -, -, R6', R7'⟩ := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  obtain ⟨-, C1, -, -⟩ := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ h.const
  induction m using Submodule.Quotient.induction_on with
  | H x =>
  obtain ⟨f, hf⟩ := x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hm
  rw [Submodule.Quotient.mk_eq_zero]
  change (p : WittVector p k) • f ∈ intBy p k (Fin d) 1 at hm
  change f ∈ intBy p k (Fin d) 1
  obtain ⟨b, hB⟩ := (R1 _).1 hm
  have hL : ∀ i, constantCoeff (lift p (μ i)) = 0 := fun i => constantCoeff_lift p (h.const i)
  have hcob : cob1 (fun i => lift p (μ i)) ((p : WittVector p k) • f) =
      (p : WittVector p k) • cob1 (fun i => lift p (μ i)) f := by
    rw [← algebraMap_smul (Fr p k) (p : WittVector p k) f, formalCoboundary_smul hL, algebraMap_smul]
  have hcp : cob1 (fun i => lift p (μ i)) ((p : WittVector p k) • f) ∈ intBy p k _ (p : WittVector p k) := by
    rw [hcob, R7']; exact ⟨_, hf.2, rfl⟩
  have h0 : cob1 μ b = 0 := R2' _ _ _ (C1 _ _ hB).1 ((R6' _).1 hcp)
  have hb0 : b = 0 := hb b h0
  subst hb0
  obtain ⟨g, hg, hfg⟩ := (ZariskiNoetherianInduction _ _).1 ((R6 _).2 hB)
  have hp : (algebraMap (WittVector p k) (Fr p k) (p : WittVector p k)) ≠ 0 := by
    rw [map_natCast]
    intro h0
    have := IsFractionRing.injective (WittVector p k) (Fr p k)
    apply WittVector.p_nonzero (p := p) (R := k)
    apply this; rw [map_natCast, map_zero]; exact h0
  have : f = g := by
    ext α
    have := congrArg (coeff α) hfg
    rw [← algebraMap_smul (Fr p k) (p : WittVector p k) f, ← algebraMap_smul (Fr p k) (p : WittVector p k) g,
      map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
    exact mul_left_cancel₀ hp this
  rw [this]; exact hg

end GlobalTheory.Katz
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace Katz

theorem existsUnique_semiHom_ev (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k')
    (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e)
    (s : SemiHom σ G' G) :
    ∃! φ : Fin d → MvPowerSeries (Fin e) k', ∀ n j, c'.ev n (φ j) = s.app n (c.x n j) := by
  have h := fun j : Fin d => existsUnique_evA_eq_of_presents k' (Fin e) G'.A c'.x c'.nil
    (fun n => (G'.res n : G'.A (n + 1) →ₐ[k'] G'.A n)) c'.res c'.presents
    (fun n => s.app n (c.x n j)) (fun n => by
      change G'.res n (s.app (n + 1) (c.x (n + 1) j)) = _
      rw [s.res_app, c.res])
  choose φ hφ hu using h
  refine ⟨φ, fun n j => hφ j n, fun ψ hψ => funext fun j => hu j (ψ j) fun n => hψ n j⟩

end Katz

end GlobalTheory
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_powerSeries_semilinear_pDivGroupHom_chart : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G), ∃! φ : Fin d → MvPowerSeries (Fin e) k', ∀ n j, c'.ev n (φ j) = s.app n (c.x n j) := by
  first | (exact @GlobalTheory.Katz.existsUnique_semiHom_ev) | (exact GlobalTheory.Katz.existsUnique_semiHom_ev) | (intros; apply GlobalTheory.Katz.existsUnique_semiHom_ev  <;> assumption)
end

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

theorem semiHom_constantCoeff_and_ev : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (φ : Fin d → MvPowerSeries (Fin e) k'), (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ j, constantCoeff (φ j) = 0) ∧ ∀ n g, c'.ev n (subst φ (MvPowerSeries.map σ g)) = s.app n (c.ev n g) := by
  intro p k k' _ _ σ d e G G' c c' s φ hφ
  have hconst : ∀ j, constantCoeff (φ j) = 0 := fun j => by
    have h1 := (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k' e (G'.A 0) (c'.x 0) (c'.nil 0) (c'.aug 0) (φ j)).1
    change Coalgebra.counit (R := k') (c'.ev 0 (φ j)) = _ at h1
    rw [← h1, hφ 0 j, (s.app 0).counit_map, c.aug, map_zero]
  refine ⟨hconst, fun n g => ?_⟩
  have hy : ∀ j, IsNilpotent (s.app n (c.x n j)) := fun j => (c.nil n j).map (s.app n).toRingHom
  have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k' (Fin d) (G'.A n)).1 (Fin e) (c'.ev n)
    (fun t => by
      change IsNilpotent (evA k' (c'.x n) (c'.nil n) (X t))
      rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact c'.nil n t) φ hconst _ hy (fun j => hφ n j) (MvPowerSeries.map σ g)
  rw [h1]
  letI : Algebra k (G'.A n) := ((algebraMap k' (G'.A n)).comp σ).toAlgebra
  let S : G.A n →ₐ[k] G'.A n :=
    { (s.app n).toRingHom with commutes' := fun r => (s.app n).map_algebraMap r }
  have h2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A n)).2 (G'.A n) S (c.x n) (c.nil n) _ hy (fun _ => rfl) g
  change _ = S (evA k (c.x n) (c.nil n) g)
  rw [h2]
  let M : MvPowerSeries (Fin d) k →ₐ[k] G'.A n :=
    { (evA k' _ hy : MvPowerSeries (Fin d) k' →+* G'.A n).comp (MvPowerSeries.map σ) with
      commutes' := fun r => by
        change evA k' _ hy (MvPowerSeries.map σ (algebraMap k _ r)) = algebraMap k' _ (σ r)
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          MvPowerSeries.map_C, ← (evA k' _ hy).commutes (σ r), MvPowerSeries.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply] }
  have hM : M = evA k _ hy := GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k (Fin d) (G'.A n) M _
    (fun i => by
      change IsNilpotent (evA k' _ hy (MvPowerSeries.map σ (X i)))
      rw [MvPowerSeries.map_X, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact hy i)
    (fun i => by
      change evA k' _ hy (MvPowerSeries.map σ (X i)) = _
      rw [MvPowerSeries.map_X, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate])
  exact AlgHom.congr_fun hM g

end GlobalTheory.Katz
end
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinearPDivGroupHom_chart_constantCoeff_subst : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (φ : Fin d → MvPowerSeries (Fin e) k'), (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ j, constantCoeff (φ j) = 0) ∧ ∀ n g, c'.ev n (subst φ (MvPowerSeries.map σ g)) = s.app n (c.ev n g) := by
  atlas_forward_decl GlobalTheory.Katz.semiHom_constantCoeff_and_ev
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinearPDivGroupHom_eval_two_variable_series : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (φ : Fin d → MvPowerSeries (Fin e) k'), (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → ∀ n t, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ t)) = (s.app n).two (c.ev₂ n t) := by
  first | exact @GlobalTheory.Katz.semiHom_ev₂_pull2 | exact GlobalTheory.Katz.semiHom_ev₂_pull2 | (intros; apply GlobalTheory.Katz.semiHom_ev₂_pull2 <;> assumption)
end

section
section
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem isHom_map_of_semiHom_ev (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k')
    (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e)
    (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k)
    (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k') (φ : Fin d → MvPowerSeries (Fin e) k')
    (hμ : c.IsLawOf μ) (hν : c'.IsLawOf ν) (hφ : ∀ n j, c'.ev n (φ j) = s.app n (c.x n j))
 :
    IsHom ν (fun i => MvPowerSeries.map σ (μ i)) φ := by
  have hL := (GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k' e G' c').2 ν hν
  have h2 := GlobalTheory.T.semilinearPDivGroupHom_eval_two_variable_series p k k' σ d e G G' c c' s φ hφ
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have h0 := (GlobalTheory.Katz.counit_dUnit_evA k' e (G'.A 0) (c'.x 0) (c'.nil 0) (c'.aug 0) (φ j)).1
    change Coalgebra.counit (R := k') (c'.ev 0 (φ j)) = _ at h0
    rw [← h0, hφ 0 j, (s.app 0).counit_map, c.aug 0 j, map_zero]
  · let z : ∀ n, G'.A n ⊗[k'] G'.A n := fun n => Coalgebra.comul (R := k') (s.app n (c.x n j))
    have hz : ∀ n, pullbackTwo (G'.res n) (z (n + 1)) = z n := fun n => by
      simp only [z]
      rw [pullTwo_comul, s.res_app, c.res]
    have hl : ∀ n, c'.ev₂ n (subst ν (φ j)) = z n := fun n => by
      rw [(hL.2 n (φ j)).1, hφ n j]
    have hr : ∀ n, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ (μ j))) = z n := fun n => by
      rw [h2 n (μ j), hμ n j, SemiBialgHom.two_comul]
    exact ((GlobalTheory.T.chart_square_coordinates_present_levels p k' e G' c').2 z hz).unique hl hr

end GlobalTheory.Katz
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedPDivGroupChart_semilinearHom_isFormalGroupHom : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k') (φ : Fin d → MvPowerSeries (Fin e) k'), c.IsLawOf μ → c'.IsLawOf ν → (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → IsHom ν (fun i => MvPowerSeries.map σ (μ i)) φ := by
  atlas_forward_decl GlobalTheory.Katz.isHom_map_of_semiHom_ev
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem GlobalTheory.Katz.rig_pull_natural_semi : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (φ : Fin d → MvPowerSeries (Fin e) k') (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] G.RigExt) (ρ' : MvPowerSeries (Fin e ⊕ Fin e) k' × (Fin e → k') →ₗ[k'] G'.RigExt), c.IsLawOf μ → (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ t w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i)) → ρ (t, w) = G.rigMk (z, u)) → (∀ t w (z : G'.cocycles) (u : G'.omega), (∀ n, z.1 n = c'.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit k' (c'.x n i)) → ρ' (t, w) = G'.rigMk (z, u)) → ∀ t w, IsCoc μ t → ρ' (pull2 φ (MvPowerSeries.map σ t), pullLin φ (fun i => σ (w i))) = s.rig (ρ (t, w)) := by
  intro p k k' _ _ σ d e G G' c c' s μ φ ρ ρ' hμ hφ hρ hρ' t w ht
  have hz : (fun n => c.ev₂ n t) ∈ G.cocycles := (GlobalTheory.T.isSymmetricFormalGroupCocycle_iff_mem_cocycles p k d G c μ hμ t).1 ht
  have hu : (fun n => ∑ i, w i • dUnit k (c.x n i)) ∈ G.omegaSub := (GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c).1 w
  rw [hρ t w ⟨_, hz⟩ ⟨_, hu⟩ (fun _ => rfl) (fun _ => rfl), SemiHom.rig_mk]
  have hev : ∀ n, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ t)) = (s.app n).two (c.ev₂ n t) := by
    intro n
    exact GlobalTheory.Katz.semiHom_ev₂_pull2 p k k' σ d e G G' c c' s φ hφ n t
  refine hρ' _ _ _ _ (fun n => ?_) (fun n => ?_)
  · rw [SemiHom.cocycles_val, hev n]
  · rw [SemiHom.omega_val]
    change (s.app n).cot (∑ i, w i • dUnit k (c.x n i)) = _
    rw [map_sum]
    simp only [map_smulₛₗ, SemiBialgHom.cot_d]
    have hd : ∀ i, dUnit k' (s.app n (c.x n i)) = ∑ l, lin (φ i) l • dUnit k' (c'.x n l) := fun i => by
      rw [← hφ n i]
      exact (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k' e (G'.A n) (c'.x n) (c'.nil n) (c'.aug n) (φ i)).2
    simp only [hd, Finset.smul_sum, smul_smul, pullLin, Finset.sum_smul]
    exact Finset.sum_comm
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedExtension_presentation_natural_semilinear : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (φ : Fin d → MvPowerSeries (Fin e) k') (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] G.RigExt) (ρ' : MvPowerSeries (Fin e ⊕ Fin e) k' × (Fin e → k') →ₗ[k'] G'.RigExt), c.IsLawOf μ → (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ t w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i)) → ρ (t, w) = G.rigMk (z, u)) → (∀ t w (z : G'.cocycles) (u : G'.omega), (∀ n, z.1 n = c'.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit k' (c'.x n i)) → ρ' (t, w) = G'.rigMk (z, u)) → ∀ t w, IsCoc μ t → ρ' (pull2 φ (MvPowerSeries.map σ t), pullLin φ (fun i => σ (w i))) = s.rig (ρ (t, w)) := by
  first | (exact @GlobalTheory.Katz.rig_pull_natural_semi) | (exact GlobalTheory.Katz.rig_pull_natural_semi) | (intros; apply GlobalTheory.Katz.rig_pull_natural_semi  <;> assumption)
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

section Pull

variable {p : ℕ} [Fact p.Prime]

theorem semiPull_exists {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] (σ : k →+* k') {d e : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k}
    {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k'} (hμ : IsLaw μ) (hν : IsLaw ν)
    (φ : Fin d → MvPowerSeries (Fin e) k') (hφ : IsHom ν (fun i => MvPowerSeries.map σ (μ i)) φ) :
    ∃ m : Mod p hμ →ₛₗ[WittVector.map (p := p) σ] Mod p hν, ∀ f : quasiLog p hμ, ∃ g : quasiLog p hν,
      g.1 = subst (fun j => Katz.lift p (φ j)) (MvPowerSeries.map (frMap p σ) f.1) ∧
      m (Submodule.Quotient.mk f) = Submodule.Quotient.mk g := by
  have hσμ := GlobalTheory.T.isCommFormalGroupLaw_map k k' σ d μ hμ
  have hB := GlobalTheory.T.map_formalGroupLawQuasiLogarithms p k k' σ d μ hμ hσμ
  obtain ⟨m1, hm1⟩ := GlobalTheory.Katz.ModHom.map_exists p k' e d ν _ hν hσμ φ hφ
  let L0 : quasiLog p hμ →ₛₗ[WittVector.map (p := p) σ] quasiLog p hσμ :=
    { toFun := fun f => ⟨MvPowerSeries.map (frMap p σ) f.1, (hB f.1 f.2).1⟩
      map_add' := fun f g => Subtype.ext (map_add _ _ _)
      map_smul' := fun r f => Subtype.ext (by
        ext α
        change coeff α (MvPowerSeries.map (frMap p σ) (r • f.1)) =
          coeff α ((WittVector.map (p := p) σ r) • MvPowerSeries.map (frMap p σ) f.1)
        rw [← algebraMap_smul (Fr p k) r f.1, ← algebraMap_smul (Fr p k') (WittVector.map (p := p) σ r),
          coeff_map, coeff_smul, coeff_smul, coeff_map]
        simp only [smul_eq_mul, map_mul, frMap_algebraMap]) }
  let m0 : Mod p hμ →ₛₗ[WittVector.map (p := p) σ] Mod p hσμ :=
    Submodule.mapQ _ _ L0 (fun f hf => (hB f.1 f.2).2.1 hf)
  refine ⟨m1.comp m0, fun f => ?_⟩
  obtain ⟨g, hg, hmg⟩ := hm1 (L0 f)
  exact ⟨g, hg, hmg⟩

end Pull

section Chart

variable {p : ℕ} [Fact p.Prime]

def IsChartPull {k k' : Type} [Field k] [CharP k p] [Field k'] [CharP k' p] {σ : k →+* k'}
    {G : PDivGroup p k} {G' : PDivGroup p k'} {d e : ℕ} (c : Chart G d) (c' : Chart G' e)
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k'}
    (hμ : IsLaw μ) (hν : IsLaw ν) (s : SemiHom σ G' G) (m : Mod p hμ → Mod p hν) : Prop :=
  ∀ φ : Fin d → MvPowerSeries (Fin e) k', (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) →
    ∀ f : quasiLog p hμ, ∃ g : quasiLog p hν,
      g.1 = subst (fun j => Katz.lift p (φ j)) (MvPowerSeries.map (frMap p σ) f.1) ∧
      m (Submodule.Quotient.mk f) = Submodule.Quotient.mk g

theorem chartPull_exists {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] {σ : k →+* k'} {G : PDivGroup p k} {G' : PDivGroup p k'} {d e : ℕ}
    (c : Chart G d) (c' : Chart G' e) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k}
    {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k'} (hμ : IsLaw μ) (hν : IsLaw ν) (hc : c.IsLawOf μ)
    (hc' : c'.IsLawOf ν) (s : SemiHom σ G' G) :
    ∃ m : Mod p hμ →ₛₗ[WittVector.map (p := p) σ] Mod p hν, IsChartPull c c' hμ hν s m := by
  obtain ⟨φ, hφ, huniq⟩ := GlobalTheory.T.existsUnique_powerSeries_semilinear_pDivGroupHom_chart p k k' σ d e G G' c c' s
  obtain ⟨m, hm⟩ := semiPull_exists σ hμ hν φ (GlobalTheory.T.connectedPDivGroupChart_semilinearHom_isFormalGroupHom p k k' σ d e G G' c c' s μ ν φ hc hc' hφ)
  refine ⟨m, fun ψ hψ f => ?_⟩
  rw [huniq ψ hψ]
  exact hm f

theorem mk_eq_mk_of_sub {k : Type} [Field k] [CharP k p] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} {hμ : IsLaw μ} (f g : quasiLog p hμ)
    (h : f.1 - g.1 ∈ intBy p k (Fin d) 1) :
    (Submodule.Quotient.mk f : Mod p hμ) = Submodule.Quotient.mk g :=
  by
  refine (Submodule.Quotient.eq _).2 ?_
  change ((f - g : quasiLog p hμ) : MvPowerSeries (Fin d) (Fr p k)) ∈ intBy p k (Fin d) 1
  rw [Submodule.coe_sub]
  exact h

theorem chartPull_comp {k k' k'' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] [Field k''] [CharP k'' p] [PerfectRing k'' p] {σ : k →+* k'} {τ : k' →+* k''}
    {υ : k →+* k''} {G : PDivGroup p k} {G' : PDivGroup p k'} {G'' : PDivGroup p k''} {d e e' : ℕ}
    (c : Chart G d) (c' : Chart G' e) (c'' : Chart G'' e')
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k'}
    {κ : Fin e' → MvPowerSeries (Fin e' ⊕ Fin e') k''} (hμ : IsLaw μ) (hν : IsLaw ν) (hκ : IsLaw κ)
    (s : SemiHom σ G' G) (t : SemiHom τ G'' G') (u : SemiHom υ G'' G)
    (hu : ∀ n a, u.app n a = t.app n (s.app n a))
    (ms : Mod p hμ → Mod p hν) (mt : Mod p hν → Mod p hκ) (mu : Mod p hμ → Mod p hκ)
    (hs : IsChartPull c c' hμ hν s ms) (ht : IsChartPull c' c'' hν hκ t mt)
    (hmu : IsChartPull c c'' hμ hκ u mu) (x : Mod p hμ) : mu x = mt (ms x) := by
  obtain rfl := ringHom_eq_of_app s t u hu
  induction x using Submodule.Quotient.induction_on with | _ f => ?_
  obtain ⟨φs, hφs, -⟩ := GlobalTheory.T.existsUnique_powerSeries_semilinear_pDivGroupHom_chart p k k' σ d e G G' c c' s
  obtain ⟨φt, hφt, -⟩ := GlobalTheory.T.existsUnique_powerSeries_semilinear_pDivGroupHom_chart p k' k'' τ e e' G' G'' c' c'' t
  have h3s := GlobalTheory.T.semilinearPDivGroupHom_chart_constantCoeff_subst p k k' σ d e G G' c c' s φs hφs
  have h3t := GlobalTheory.T.semilinearPDivGroupHom_chart_constantCoeff_subst p k' k'' τ e e' G' G'' c' c'' t φt hφt
  let ψ : Fin d → MvPowerSeries (Fin e) k'' := fun j => MvPowerSeries.map τ (φs j)
  have hψ0 : ∀ j, constantCoeff (ψ j) = 0 := fun j => by
    simp only [ψ, constantCoeff_map, h3s.1 j, map_zero]
  have hφu : ∀ n j, c''.ev n (subst φt (ψ j)) = u.app n (c.x n j) := fun n j => by
    rw [h3t.2 n, hφs, hu]
  obtain ⟨gs, hgs, hms⟩ := hs φs hφs f
  obtain ⟨gt, hgt, hmt⟩ := ht φt hφt gs
  obtain ⟨gu, hgu, hmu'⟩ := hmu (fun j => subst φt (ψ j)) hφu f
  rw [hmu', hms, hmt]
  refine mk_eq_mk_of_sub gu gt ?_
  have hσμ := GlobalTheory.T.isCommFormalGroupLaw_map k k'' (τ.comp σ) d μ hμ
  have hF := (GlobalTheory.T.map_formalGroupLawQuasiLogarithms p k k'' (τ.comp σ) d μ hμ hσμ f.1 f.2).1
  have key := (GlobalTheory.Katz.PullQuasiLog.main p k'' e d (fun i => MvPowerSeries.map (τ.comp σ) (μ i)) hσμ _ hF).2.1
    e' φt ψ (h3t.1) hψ0
  rw [hgu, hgt, hgs, map_subst_lift p τ φs h3s.1, MvPowerSeries.map_map, ← frMap_comp]
  exact key

end Chart

section ChartRules

variable {p : ℕ} [Fact p.Prime]

theorem chartPull_id {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G : PDivGroup p k} {d : ℕ}
    (c : Chart G d) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (hμ : IsLaw μ)
    (m : Mod p hμ → Mod p hμ) (hm : IsChartPull c c hμ hμ (SemiHom.ofHom (𝟙 G)) m) (x : Mod p hμ) :
    m x = x := by
  induction x using Submodule.Quotient.induction_on with | _ f => ?_
  obtain ⟨g, hg, hmg⟩ := hm (fun j => X j) (fun n j => by
    rw [SemiHom.ofHom_app, id_app]
    exact GlobalTheory.Katz.evA_X k (Fin d) (G.A n) (c.x n) (c.nil n) j) f
  rw [hmg]
  refine mk_eq_mk_of_sub g f ?_
  rw [hg, frMap_id, MvPowerSeries.map_id, RingHom.id_apply,
    (GlobalTheory.Katz.PullQuasiLog.main p k d d μ hμ f.1 f.2).1, sub_self]
  exact zero_mem _

theorem chartPull_add {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G H : PDivGroup p k} {d e : ℕ}
    (cG : Chart G d) (cH : Chart H e) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k}
    {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k} (hμ : IsLaw μ) (hν : IsLaw ν) (hcH : cH.IsLawOf ν)
    (f g : G ⟶ H) (mf mg mfg : Mod p hν → Mod p hμ)
    (hf : IsChartPull cH cG hν hμ (SemiHom.ofHom f) mf) (hg : IsChartPull cH cG hν hμ (SemiHom.ofHom g) mg)
    (hfg : IsChartPull cH cG hν hμ (SemiHom.ofHom (f + g)) mfg) (x : Mod p hν) :
    mfg x = mf x + mg x := by
  induction x using Submodule.Quotient.induction_on with | _ y => ?_
  obtain ⟨φf, hφf, -⟩ := GlobalTheory.T.existsUnique_powerSeries_semilinear_pDivGroupHom_chart p k k (RingHom.id k) e d H G cH cG (SemiHom.ofHom f)
  obtain ⟨φg, hφg, -⟩ := GlobalTheory.T.existsUnique_powerSeries_semilinear_pDivGroupHom_chart p k k (RingHom.id k) e d H G cH cG (SemiHom.ofHom g)
  have c1 := (GlobalTheory.T.semilinearPDivGroupHom_chart_constantCoeff_subst p k k (RingHom.id k) e d H G cH cG _ φf hφf).1
  have c2 := (GlobalTheory.T.semilinearPDivGroupHom_chart_constantCoeff_subst p k k (RingHom.id k) e d H G cH cG _ φg hφg).1
  have hsum : cG.IsMapOf cH (f + g) (op ν φf φg) :=
    GlobalTheory.T.isMapOf_add_formalGroupLawEvalPoints p k d e G H cG cH ν f g φf φg hcH (fun n j => hφf n j) (fun n j => hφg n j)
  obtain ⟨a, ha, hma⟩ := hf φf hφf y
  obtain ⟨b, hb, hmb⟩ := hg φg hφg y
  obtain ⟨s, hs, hms⟩ := hfg (op ν φf φg) (fun n j => hsum n j) y
  rw [hma, hmb, hms, ← Submodule.Quotient.mk_add]
  refine mk_eq_mk_of_sub s (a + b) ?_
  rw [Submodule.coe_add, hs, ha, hb, frMap_id, MvPowerSeries.map_id, RingHom.id_apply, ← sub_sub]
  exact (GlobalTheory.Katz.PullQuasiLog.main p k d e ν hν y.1 y.2).2.2 φf φg c1 c2

theorem chartPull_red {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] {σ : k →+* k'} {G : PDivGroup p k} {G' : PDivGroup p k'} {d e : ℕ}
    (c : Chart G d) (c' : Chart G' e) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k}
    {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k'} (hμ : IsLaw μ) (hν : IsLaw ν) (hc : c.IsLawOf μ)
    (hc' : c'.IsLawOf ν) (s : SemiHom σ G' G) (m : Mod p hμ → Mod p hν) (hm : IsChartPull c c' hμ hν s m)
    (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] G.RigExt)
    (ρ' : MvPowerSeries (Fin e ⊕ Fin e) k' × (Fin e → k') →ₗ[k'] G'.RigExt)
    (hρ : ∀ t w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n t) →
      (∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i)) → ρ (t, w) = G.rigMk (z, u))
    (hρ' : ∀ t w (z : G'.cocycles) (u : G'.omega), (∀ n, z.1 n = c'.ev₂ n t) →
      (∀ n, u.1 n = ∑ i, w i • dUnit k' (c'.x n i)) → ρ' (t, w) = G'.rigMk (z, u))
    (r : Mod p hμ →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] G.RigExt)
    (r' : Mod p hν →ₛₗ[(WittVector.constantCoeff : WittVector p k' →+* k')] G'.RigExt)
    (hr : ∀ (f : quasiLog p hμ) t w, Red p (cob1 (fun i => Katz.lift p (μ i)) f.1) t → RedV p (lin f.1) w →
      r (Submodule.Quotient.mk f) = ρ (t, w))
    (hr' : ∀ (f : quasiLog p hν) t w, Red p (cob1 (fun i => Katz.lift p (ν i)) f.1) t → RedV p (lin f.1) w →
      r' (Submodule.Quotient.mk f) = ρ' (t, w)) (x : Mod p hμ) :
    r' (m x) = s.rig (r x) := by
  induction x using Submodule.Quotient.induction_on with | _ f => ?_
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.T.existsUnique_powerSeries_semilinear_pDivGroupHom_chart p k k' σ d e G G' c c' s
  have hhom := GlobalTheory.T.connectedPDivGroupChart_semilinearHom_isFormalGroupHom p k k' σ d e G G' c c' s μ ν φ hc hc' hφ
  obtain ⟨g, hg, hmg⟩ := hm φ hφ f
  have hD := GlobalTheory.T.quasiLog_reduces_to_cocycle p k d μ hμ
  obtain ⟨t, w, ht, hw⟩ := hD.1 f.1 f.2
  have hcoc := hD.2 f.1 f.2 t ht
  have hσμ := GlobalTheory.T.isCommFormalGroupLaw_map k k' σ d μ hμ
  have hB := GlobalTheory.T.map_formalGroupLawQuasiLogarithms p k k' σ d μ hμ hσμ f.1 f.2
  have hP := GlobalTheory.KatzPull.quasiLog_pull p k' e d ν _ hν hσμ φ hhom _ hB.1
  rw [hmg, hr f t w ht hw, hr' g (pull2 φ (MvPowerSeries.map σ t)) (pullLin φ (fun i => σ (w i)))
    (by rw [hg]; exact hP.2.1 _ (hB.2.2.1 t ht)) (by rw [hg]; exact hP.2.2 _ (hB.2.2.2 w hw))]
  exact GlobalTheory.T.rigidifiedExtension_presentation_natural_semilinear p k k' σ d e G G' c c' s μ φ ρ ρ' hc hφ hρ hρ' t w hcoc

theorem chartPull_frob {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G : PDivGroup p k} {d : ℕ}
    (c : Chart G d) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (hμ : IsLaw μ)
    (m : Mod p hμ → Mod p hμ) (hm : IsChartPull c c hμ hμ (absFrob (Dieu.p_eq_zero p k) G) m) :
    KatzF.IsF p hμ m := by
  intro f
  obtain ⟨g, hg, hmg⟩ := hm (fun j => X j ^ p) (fun n j => by
    rw [absFrob_app, map_pow]
    congr 1
    exact GlobalTheory.Katz.evA_X k (Fin d) (G.A n) (c.x n) (c.nil n) j) f
  exact ⟨g, hg.trans (subst_lift_X_pow_frob p _ f.1), hmg⟩

theorem chartPull_isPull {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G H : PDivGroup p k} {d e : ℕ}
    (c : Chart G d) (c' : Chart H e) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k}
    {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k} (hμ : IsLaw μ) (hν : IsLaw ν) (f : G ⟶ H)
    (φ : Fin e → MvPowerSeries (Fin d) k) (hφ : c.IsMapOf c' f φ) (m : Mod p hν → Mod p hμ)
    (hm : IsChartPull c' c hν hμ (SemiHom.ofHom f) m) : KatzF.IsPull p hμ hν φ m := by
  intro x
  obtain ⟨g, hg, hmg⟩ := hm φ (fun n j => hφ n j) x
  refine ⟨g, ?_, hmg⟩
  rw [hg, frMap_id, MvPowerSeries.map_id, RingHom.id_apply]

end ChartRules

section Main

variable {p : ℕ} [Fact p.Prime]

theorem isChartPull_comp {k k' k'' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] [Field k''] [CharP k'' p] [PerfectRing k'' p] {σ : k →+* k'} {τ : k' →+* k''}
    {υ : k →+* k''} {G : PDivGroup p k} {G' : PDivGroup p k'} {G'' : PDivGroup p k''} {d e e' : ℕ}
    (c : Chart G d) (c' : Chart G' e) (c'' : Chart G'' e')
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k'}
    {κ : Fin e' → MvPowerSeries (Fin e' ⊕ Fin e') k''} (hμ : IsLaw μ) (hν : IsLaw ν) (hκ : IsLaw κ)
    (hc : c.IsLawOf μ) (hc'' : c''.IsLawOf κ)
    (s : SemiHom σ G' G) (t : SemiHom τ G'' G') (u : SemiHom υ G'' G)
    (hu : ∀ n a, u.app n a = t.app n (s.app n a))
    (ms : Mod p hμ → Mod p hν) (mt : Mod p hν → Mod p hκ)
    (hs : IsChartPull c c' hμ hν s ms) (ht : IsChartPull c' c'' hν hκ t mt) :
    IsChartPull c c'' hμ hκ u (fun x => mt (ms x)) := by
  obtain ⟨mu, hmu⟩ := chartPull_exists c c'' hμ hκ hc hc'' u
  have e : (mu : Mod p hμ → Mod p hκ) = fun x => mt (ms x) :=
    funext (chartPull_comp c c' c'' hμ hν hκ s t u hu ms mt mu hs ht hmu)
  rw [← e]
  exact hmu

theorem exists_base_isConn_katz : ∀ (p : ℕ) [Fact p.Prime],
    ∃ B : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn), B.Katz := by
  intro p _
  have hch : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsConn →
      ∃ (d : ℕ) (c : Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ := by
    intro k _ _ _ G hG
    obtain ⟨d, ⟨c⟩⟩ := GlobalTheory.T.exists_connectedPDivGroupChart_of_isConn p k (CharP.cast_eq_zero k p) G hG
    obtain ⟨μ, hμ⟩ := (GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).1
    exact ⟨d, c, μ, hμ⟩
  choose d c μ hc using hch
  have hlaw : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (hG : G.IsConn),
      IsLaw (μ k G hG) := fun k _ _ _ G hG => GlobalTheory.T.isCommFormalGroupLaw_of_isLawOf p k _ G _ _ (hc k G hG)
  choose ρ hρ using fun (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k)
    (hG : G.IsConn) => GlobalTheory.T.exists_rigidifiedExtension_of_series_pair p k (d k G hG) G (c k G hG)
  choose r hr hsurj hker using fun (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k)
    (hG : G.IsConn) => GlobalTheory.Katz.reductionMap p k (d k G hG) (μ k G hG) (hlaw k G hG) G.RigExt (ρ k G hG)
      (GlobalTheory.T.rigidifiedExtension_presentation_of_series_pairs p k _ G _ _ _ (hc k G hG) (hρ k G hG))
  choose P hP using fun (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] (σ : k →+* k') (G : PDivGroup p k) (G' : PDivGroup p k') (d e : ℕ) (cc : Chart G d)
    (cc' : Chart G' e) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k)
    (ν' : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k') (hμ' : IsLaw μ') (hν' : IsLaw ν')
    (hc1 : cc.IsLawOf μ') (hc2 : cc'.IsLawOf ν') (s : SemiHom σ G' G) =>
    chartPull_exists cc cc' hμ' hν' hc1 hc2 s
  have hff : ∀ (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (hG : G.IsConn),
      Module.Free (WittVector p k) (Mod p (hlaw k G hG)) ∧ Module.Finite (WittVector p k) (Mod p (hlaw k G hG)) := by
    intro k _ _ _ G hG
    haveI : Module.Finite k G.RigExt :=
      (GlobalTheory.PDivGroup.finrank_rigExt_omega p k (CharP.cast_eq_zero k p) G).2.1
    exact GlobalTheory.wittModule_free_finite_of_reduction p k _ G.RigExt (r k G hG)
      (GlobalTheory.Katz.WittHaus.haus p k _ _ (hlaw k G hG))
      (GlobalTheory.Katz.mod_noPTorsion p k _ _ (hlaw k G hG)
        (GlobalTheory.T.eq_zero_of_formalGroupLawCoboundaryOne_eq_zero p k (CharP.cast_eq_zero k p) _ G _ _ (hc k G hG)))
      (hsurj k G hG) (fun x => (hker k G hG x).1)
  let B : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn) :=
    { M := @fun k _ _ _ G hG => ModuleCat.of (WittVector p k) (Mod p (hlaw k G hG))
      smap := @fun k k' _ _ _ _ _ _ σ G' G h' h s =>
        (P k k' σ G G' _ _ (c k G h) (c k' G' h') _ _ (hlaw k G h) (hlaw k' G' h') (hc k G h) (hc k' G' h')
          s).toAddMonoidHom
      red := @fun k _ _ _ G hG => r k G hG
      free := @fun k _ _ _ G hG => (hff k G hG).1
      finite := @fun k _ _ _ G hG => (hff k G hG).2
      red_surjective := @fun k _ _ _ G hG => hsurj k G hG
      red_eq_zero := @fun k _ _ _ G hG => hker k G hG
      smap_smul := @fun k k' _ _ _ _ _ _ σ G' G h' h s a m =>
        (P k k' σ G G' _ _ (c k G h) (c k' G' h') _ _ (hlaw k G h) (hlaw k' G' h') (hc k G h) (hc k' G' h')
          s).map_smulₛₗ a m
      smap_id := @fun k _ _ _ G h m =>
        chartPull_id (c k G h) (hlaw k G h) _ (hP k k (RingHom.id k) G G _ _ (c k G h) (c k G h) _ _ (hlaw k G h)
          (hlaw k G h) (hc k G h) (hc k G h) (SemiHom.ofHom (𝟙 G))) m
      smap_add := @fun k _ _ _ G H hG hH f g m =>
        chartPull_add (c k G hG) (c k H hH) (hlaw k G hG) (hlaw k H hH) (hc k H hH) f g _ _ _
          (hP k k (RingHom.id k) H G _ _ (c k H hH) (c k G hG) _ _ (hlaw k H hH) (hlaw k G hG) (hc k H hH)
            (hc k G hG) (SemiHom.ofHom f))
          (hP k k (RingHom.id k) H G _ _ (c k H hH) (c k G hG) _ _ (hlaw k H hH) (hlaw k G hG) (hc k H hH)
            (hc k G hG) (SemiHom.ofHom g))
          (hP k k (RingHom.id k) H G _ _ (c k H hH) (c k G hG) _ _ (hlaw k H hH) (hlaw k G hG) (hc k H hH)
            (hc k G hG) (SemiHom.ofHom (f + g))) m
      smap_comp := @fun k k' k'' _ _ _ _ _ _ _ _ _ σ τ υ G'' G' G h'' h' h s t u hu m =>
        chartPull_comp (c k G h) (c k' G' h') (c k'' G'' h'') (hlaw k G h) (hlaw k' G' h') (hlaw k'' G'' h'')
          s t u hu _ _ _
          (hP k k' σ G G' _ _ (c k G h) (c k' G' h') _ _ (hlaw k G h) (hlaw k' G' h') (hc k G h) (hc k' G' h') s)
          (hP k' k'' τ G' G'' _ _ (c k' G' h') (c k'' G'' h'') _ _ (hlaw k' G' h') (hlaw k'' G'' h'')
            (hc k' G' h') (hc k'' G'' h'') t)
          (hP k k'' υ G G'' _ _ (c k G h) (c k'' G'' h'') _ _ (hlaw k G h) (hlaw k'' G'' h'') (hc k G h)
            (hc k'' G'' h'') u) m
      red_smap := @fun k k' _ _ _ _ _ _ σ G' G h' h s m =>
        chartPull_red (c k G h) (c k' G' h') (hlaw k G h) (hlaw k' G' h') (hc k G h) (hc k' G' h') s _
          (hP k k' σ G G' _ _ (c k G h) (c k' G' h') _ _ (hlaw k G h) (hlaw k' G' h') (hc k G h) (hc k' G' h') s)
          (ρ k G h) (ρ k' G' h') (hρ k G h) (hρ k' G' h') (r k G h) (r k' G' h') (hr k G h) (hr k' G' h') m }
  have hid : ∀ {k : Type} [Field k] (G : PDivGroup p k) (n : ℕ) (a : G.A n),
      (SemiHom.ofHom (𝟙 G)).app n a = a := fun G n a => rfl
  refine ⟨B, @fun k _ _ _ G h d' cc μ' hμ' hcc =>
    { toFun := P k k (RingHom.id k) G G _ _ (c k G h) cc _ _ (hlaw k G h) hμ' (hc k G h) hcc
        (SemiHom.ofHom (𝟙 G))
      invFun := P k k (RingHom.id k) G G _ _ cc (c k G h) _ _ hμ' (hlaw k G h) hcc (hc k G h)
        (SemiHom.ofHom (𝟙 G))
      map_add' := map_add _
      map_smul' := fun a x => by
        refine (LinearMap.map_smulₛₗ _ a x).trans ?_
        congr 1
      left_inv := fun x =>
        (chartPull_comp (c k G h) cc (c k G h) (hlaw k G h) hμ' (hlaw k G h) (SemiHom.ofHom (𝟙 G))
          (SemiHom.ofHom (𝟙 G)) (SemiHom.ofHom (𝟙 G)) (fun n a => rfl) _ _ _
          (hP k k (RingHom.id k) G G _ _ (c k G h) cc _ _ (hlaw k G h) hμ' (hc k G h) hcc _)
          (hP k k (RingHom.id k) G G _ _ cc (c k G h) _ _ hμ' (hlaw k G h) hcc (hc k G h) _)
          (hP k k (RingHom.id k) G G _ _ (c k G h) (c k G h) _ _ (hlaw k G h) (hlaw k G h) (hc k G h)
            (hc k G h) _) x).symm.trans
          (chartPull_id (c k G h) (hlaw k G h) _
            (hP k k (RingHom.id k) G G _ _ (c k G h) (c k G h) _ _ (hlaw k G h) (hlaw k G h) (hc k G h)
              (hc k G h) _) x)
      right_inv := fun x =>
        (chartPull_comp cc (c k G h) cc hμ' (hlaw k G h) hμ' (SemiHom.ofHom (𝟙 G))
          (SemiHom.ofHom (𝟙 G)) (SemiHom.ofHom (𝟙 G)) (fun n a => rfl) _ _ _
          (hP k k (RingHom.id k) G G _ _ cc (c k G h) _ _ hμ' (hlaw k G h) hcc (hc k G h) _)
          (hP k k (RingHom.id k) G G _ _ (c k G h) cc _ _ (hlaw k G h) hμ' (hc k G h) hcc _)
          (hP k k (RingHom.id k) G G _ _ cc cc _ _ hμ' hμ' hcc hcc _) x).symm.trans
          (chartPull_id cc hμ' _ (hP k k (RingHom.id k) G G _ _ cc cc _ _ hμ' hμ' hcc hcc _) x) }, ?_⟩
  intro k _ _ _ G h d' cc μ' hμ' hcc
  refine ⟨chartPull_frob cc hμ' _ ?_, ?_⟩
  · have hin := isChartPull_comp cc (c k G h) (c k G h) hμ' (hlaw k G h) (hlaw k G h) hcc (hc k G h)
      (SemiHom.ofHom (𝟙 G)) (absFrob (Dieu.p_eq_zero p k) G) (absFrob (Dieu.p_eq_zero p k) G)
      (fun n a => rfl) _ _
      (hP k k (RingHom.id k) G G _ _ cc (c k G h) _ _ hμ' (hlaw k G h) hcc (hc k G h) _)
      (hP k k _ G G _ _ (c k G h) (c k G h) _ _ (hlaw k G h) (hlaw k G h) (hc k G h) (hc k G h) _)
    exact isChartPull_comp cc (c k G h) cc hμ' (hlaw k G h) hμ' hcc hcc
      (absFrob (Dieu.p_eq_zero p k) G) (SemiHom.ofHom (𝟙 G)) (absFrob (Dieu.p_eq_zero p k) G)
      (fun n a => rfl) _ _ hin
      (hP k k (RingHom.id k) G G _ _ (c k G h) cc _ _ (hlaw k G h) hμ' (hc k G h) hcc _)
  · intro H h' d'' c' ν hν hc' f φ _ hφ
    refine chartPull_isPull cc c' hμ' hν f φ hφ _ ?_
    have hin := isChartPull_comp c' (c k H h') (c k G h) hν (hlaw k H h') (hlaw k G h) hc' (hc k G h)
      (SemiHom.ofHom (𝟙 H)) (SemiHom.ofHom f) (SemiHom.ofHom f)
      (fun n a => rfl) _ _
      (hP k k (RingHom.id k) H H _ _ c' (c k H h') _ _ hν (hlaw k H h') hc' (hc k H h') _)
      (hP k k _ H G _ _ (c k H h') (c k G h) _ _ (hlaw k H h') (hlaw k G h) (hc k H h') (hc k G h) _)
    exact isChartPull_comp c' (c k G h) cc hν (hlaw k G h) hμ' hc' hcc
      (SemiHom.ofHom f) (SemiHom.ofHom (𝟙 G)) (SemiHom.ofHom f)
      (fun n a => rfl) _ _ hin
      (hP k k (RingHom.id k) G G _ _ (c k G h) cc _ _ (hlaw k G h) hμ' (hc k G h) hcc _)

end Main

end GlobalTheory
end
end
