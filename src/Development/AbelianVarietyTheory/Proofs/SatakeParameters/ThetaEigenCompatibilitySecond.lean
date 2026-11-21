import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosetsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosetsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInertLocalDatumAtInertPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorEigenGoodPlaceFirstStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorEigenGoodPlaceSecondStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSatakeParameterSphericalInertPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatUOfFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorOfMemIsotypicComponent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarySatakeEqOfSameUnramifiedBaseChange

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem not_isSplitPl_of_isInertAt (D : D7) (Pp : HeightOneSpectrum (𝓞 D.host.E)) (h : Formalism.UG.IsInertAt (↥D.host.F) D.host.E (HeightOneSpectrum.under (𝓞 ↥D.host.F) Pp) Pp) : ¬ Formalism.BasicNotions.IsSplitPl D.host Pp := by
  rintro ⟨x, hx, hy⟩
  have hc : (NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)).comp
      (algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E)) = algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E) := by
    refine RingHom.ext fun a => RingOfIntegers.ext ?_
    have key : ((algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) = ((a : ↥D.host.F) : D.host.E) := rfl
    have h0 := (D.host.conjE_mem_hostF_iff _).1 (a : ↥D.host.F).2
    show (D.host.conj ((algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E)) = _
    rw [key]; exact h0
  have hmem : NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) x ∈ Pp.asIdeal := by
    unfold Formalism.UG.IsInertAt at h
    rw [← h] at hx ⊢
    have := Ideal.mem_map_of_mem (NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)) hx
    rwa [Ideal.map_map, hc] at this
  exact hy _ rfl hmem

end GlobalTheory
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_isSplitPlace_of_inert_over_realSubfield : ∀ (D : D7) (Pp : HeightOneSpectrum (𝓞 D.host.E)), Formalism.UG.IsInertAt (↥D.host.F) D.host.E (HeightOneSpectrum.under (𝓞 ↥D.host.F) Pp) Pp → ¬ Formalism.BasicNotions.IsSplitPl D.host Pp := by
  atlas_forward_decl GlobalTheory.not_isSplitPl_of_isInertAt
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertLocalDatum_at_inertPlace : ∀ (D : D7), D.host.F = maximalRealSubfield D.host.E → ∀ (Pp : HeightOneSpectrum (𝓞 D.host.E)), Formalism.UG.IsInertAt D.host.F D.host.E (Pp.under (𝓞 D.host.F)) Pp → ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (_ : InertDatum D.host.E D.R.nV v Pp), NG.OverPl Pp v := by
  first | exact @GlobalTheory.InertDatumAtInert.main | exact GlobalTheory.InertDatumAtInert.main | (intros; apply GlobalTheory.InertDatumAtInert.main <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EigIsoInert

def stabRt {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (f : GAf L n → W) : Subgroup (GAf L n) where
  carrier := {κ | NG.rt L n κ f = f}
  one_mem' := funext fun y => by
    show f (y * 1) = f y
    rw [mul_one]
  mul_mem' := by
    intro a b ha hb
    have ha' : NG.rt L n a f = f := ha
    have hb' : NG.rt L n b f = f := hb
    show NG.rt L n (a * b) f = f
    have e : NG.rt L n (a * b) f = NG.rt L n a (NG.rt L n b f) := funext fun y => by
      show f (y * (a * b)) = f (y * a * b)
      rw [mul_assoc]
    rw [e, hb', ha']
  inv_mem' := by
    intro a ha
    have ha' : NG.rt L n a f = f := ha
    show NG.rt L n a⁻¹ f = f
    calc NG.rt L n a⁻¹ f = NG.rt L n a⁻¹ (NG.rt L n a f) := by rw [ha']
      _ = f := funext fun y => by
        show f (y * a⁻¹ * a) = f y
        rw [inv_mul_cancel_right]

theorem eig_of_irr (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n)
    (S : Submodule ℂ (GAf L n → a.W)) (hS : NG.IsIrrRep a.ρ S) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (w : HeightOneSpectrum (𝓞 L)) (hw : NG.OverPl w v) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ)
    (hsat : NG.SatAt { a with S := S, irrS := hS } Dv α) (f : GAf L n → a.W) (hfS : f ∈ S)
    (hfK : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f)
    (h : Formalism.UG.GU Dv.σw n → ℂ) (hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n)) :
    heckeFunI L n (Umax L n) Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f := by
  let U : Subgroup (GAf L n) := Umax L n ⊓ stabRt f
  have hU : ∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n) :=
    fun κ hκ => ⟨fun h1 => h1.1, fun h1 => ⟨h1, hfK κ h1 hκ⟩⟩
  have e1 := GlobalTheory.InertSph.satU_of_fixed L n a S hS v w Dv α hw hsat U hU f hfS (fun κ hκ => hκ.2) h hh
  have hK : ∀ κ : GAf L n, κ ∈ Umax L n → TrivOutside {v} κ → ∃ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
      (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n :=
    fun κ hκ _ => ⟨GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal L n v w Dv κ, GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact L n v w Dv κ hκ _⟩
  rw [GlobalTheory.T.inertHeckeOperator_level_independent L n v w Dv hK (Umax L n) U (fun _ _ => Iff.rfl) hU a.W h hh.1 f hfK]
  exact e1

theorem eig_of_isoTyp_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → ∀ φ ∈ NG.isoTyp π.ρ π.S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), heckeFunI L n (Umax L n) Dv h φ = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • φ := by
  intro L _ _ _ n π v w hw Dv α hsat φ hφ hφK h hh
  have hfin : ∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) →
      ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n,
        (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0} :=
    fun U hU h hh => GlobalTheory.T.finite_inertHecke_support_cosets L n v w Dv (fun s => GlobalTheory.T.unitary_doubleCoset_finite_left_cosets Dv.ϖ Dv.σw _ n Dv.unram s)
      (GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv) U hU h hh
  set c := Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α with hc

  have hirr : ∀ S' : Submodule ℂ (GAf L n → π.W), NG.IsIrrRep π.ρ S' ∧ NG.IsoRep π.S S' → ∀ f ∈ S',
      (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) → heckeFunI L n (Umax L n) Dv h f = c • f := by
    rintro S' ⟨hS', hiso⟩ f hf hfK
    have hsat' : NG.SatAt { π.toAlgWt with S := S', irrS := hS' } Dv α :=
      GlobalTheory.SatIso.satAt_of_iso L n π { π.toAlgWt with S := S', irrS := hS' } ⟨⟨LinearEquiv.refl ℂ _, fun _ _ => rfl⟩, hiso⟩ v w Dv α hfin hsat
    exact eig_of_irr L n π.toAlgWt S' hS' v w hw Dv α hsat' f hf hfK h hh

  obtain ⟨C, cf, xs, hC⟩ := GlobalTheory.SatIso.heckeFunI_eq_sum Dv (Umax L n) h (hfin (Umax L n) (fun _ _ => Iff.rfl) h hh)
  have hadd : ∀ y z : GAf L n → π.W, heckeFunI L n (Umax L n) Dv h (y + z) =
      heckeFunI L n (Umax L n) Dv h y + heckeFunI L n (Umax L n) Dv h z := by
    intro y z
    rw [hC π.W, hC π.W, hC π.W, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_add, smul_add]
  have hzero : heckeFunI L n (Umax L n) Dv h (0 : GAf L n → π.W) = 0 := by
    rw [hC π.W]
    simp
  have key : ∀ t : Finset (Submodule ℂ (GAf L n → π.W)),
      (↑t ⊆ {S' | NG.IsIrrRep π.ρ S' ∧ NG.IsoRep π.S S'}) → ∀ f ∈ (⨆ i ∈ t, i),
      (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) → heckeFunI L n (Umax L n) Dv h f = c • f := by
    classical
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _ f hf _
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
      subst hf
      rw [hzero, smul_zero]
    | insert a t ha ih =>
      intro hsub f hf hfix
      have haF : NG.IsIrrRep π.ρ a ∧ NG.IsoRep π.S a := hsub (Finset.mem_insert_self a t)
      have hsF : (↑t : Set _) ⊆ {S' | NG.IsIrrRep π.ρ S' ∧ NG.IsoRep π.S S'} :=
        fun x hx => hsub (Finset.mem_insert_of_mem hx)
      rw [Finset.iSup_insert] at hf
      have hMst : ∀ g, ∀ y ∈ (⨆ i ∈ t, i), NG.rt L n g y ∈ (⨆ i ∈ t, i) :=
        GlobalTheory.IsoFix.iSup_finset_stable t (fun i hi => (hsF hi).1.1.stable)
      by_cases hd : a ⊓ (⨆ i ∈ t, i) = ⊥
      · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
        have hyz : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ y = y ∧ NG.rt L n κ z = z := by
          intro κ hκ hκt
          have e := hfix κ hκ hκt
          rw [map_add] at e
          have h1 : NG.rt L n κ y - y = z - NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
          have hm : NG.rt L n κ y - y ∈ a ⊓ (⨆ i ∈ t, i) :=
            ⟨a.sub_mem (haF.1.1.stable κ y hy) hy, h1 ▸ Submodule.sub_mem _ hz (hMst κ z hz)⟩
          rw [hd, Submodule.mem_bot] at hm
          refine ⟨sub_eq_zero.1 hm, ?_⟩
          rw [hm] at h1
          exact (sub_eq_zero.1 h1.symm).symm
        rw [hadd, hirr a haF y hy (fun κ hκ hκt => (hyz κ hκ hκt).1),
          ih hsF z hz (fun κ hκ hκt => (hyz κ hκ hκt).2), smul_add]
      · have hsubrep : NG.IsSubrep π.ρ (a ⊓ ⨆ i ∈ t, i) :=
          ⟨inf_le_left.trans haF.1.1.le, fun g y hy => ⟨haF.1.1.stable g y hy.1, hMst g y hy.2⟩⟩
        have heq : a ⊓ (⨆ i ∈ t, i) = a := (haF.1.2.2 _ hsubrep inf_le_left).resolve_left hd
        have hle : a ≤ ⨆ i ∈ t, i := heq ▸ inf_le_right
        exact ih hsF f ((sup_le hle le_rfl) hf) hfix
  unfold NG.isoTyp at hφ
  obtain ⟨s, hs, hfs⟩ := Submodule.mem_sSup_iff_exists_finset.1 hφ
  exact key s hs φ hfs (fun κ hκ hκt => hφK κ hκ hκt)

end GlobalTheory.EigIsoInert
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypicFixedVector_isSatakeEigen_inertPlace : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → ∀ φ ∈ NG.isoTyp π.ρ π.S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), heckeFunI L n (Umax L n) Dv h φ = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • φ := by
  atlas_forward_decl GlobalTheory.EigIsoInert.eig_of_isoTyp_fixed
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertUbcSatake

theorem satU_eq_of_ubc_eq : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ α β : Fin (n / 2) → ℂ, ubc n (Multiset.map α Finset.univ.val) = ubc n (Multiset.map β Finset.univ.val) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), Formalism.UG.SatU ϖ q h α = Formalism.UG.SatU ϖ q h β :=
  GlobalTheory.SatBcZero.satU_eq_of_ubc_eq

end GlobalTheory.InertUbcSatake
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satakeTransform_eq_of_unramifiedBaseChange_eq : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ α β : Fin (n / 2) → ℂ, ubc n (Multiset.map α Finset.univ.val) = ubc n (Multiset.map β Finset.univ.val) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), Formalism.UG.SatU ϖ q h α = Formalism.UG.SatU ϖ q h β := by
  atlas_forward_decl GlobalTheory.InertUbcSatake.satU_eq_of_ubc_eq
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.EigInert.satParam : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc) (P' : D.naut.AV i) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (w : HeightOneSpectrum (𝓞 D.host.E)), NG.OverPl w v → ¬ Formalism.BasicNotions.IsSplitPl D.host w → ∀ Dv : InertDatum D.host.E D.R.nV v w, ∃ α, NG.SatAt (P.H.av.rep i P') Dv α ∧ D.naut.satV i P' w = Multiset.map α Finset.univ.val := by
  intro hL D P i P' v w hov hns Dv
  have hsph := D.nbc.embAV_sph i P' w hns
  rw [P.H.emb i P'] at hsph
  have hS : (P.H.av.rep i P').SphAt v := (P.H.au.sph (D.nd.j i) _ _ (P.H.av.rep i P') w v hns hov).1 hsph
  obtain ⟨α, hα, hsat⟩ := P.H.au.sat (D.nd.j i) _ _ (P.H.av.rep i P') v w hov Dv (GlobalTheory.T.exists_satakeParameter_spherical_inertPlace _ _ _ v w hov Dv hS)
  refine ⟨α, hα, ?_⟩
  rw [D.nbc.embAV_sat, P.H.emb]
  exact hsat

theorem GlobalTheory.EigInert.heckeFunI_umax_sum {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)} (Dv : InertDatum L n v w)
    (h : Formalism.UG.GU Dv.σw n → ℂ) (hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n)) :
    ∃ (C : Finset (GAf L n ⧸ Umax L n)) (a : GAf L n ⧸ Umax L n → ℂ) (x : GAf L n ⧸ Umax L n → GAf L n),
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W),
        heckeFunI L n (Umax L n) Dv h φ = ∑ c ∈ C, a c • NG.rt L n (x c) φ :=
  GlobalTheory.SatIso.heckeFunI_eq_sum Dv _ h (GlobalTheory.T.finite_inertHecke_support_cosets L n v w Dv (GlobalTheory.T.unitary_doubleCoset_finite_left_cosets Dv.ϖ Dv.σw _ n Dv.unram)
    (GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv) _ (fun _ _ => Iff.rfl) h hh)

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.EigInert.eigen_at_inert : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.UG.IsInertAt D.host.F D.host.E (Pp.under (𝓞 D.host.F)) Pp → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, h Pp (Finsupp.single d 1) y = c • y := by
  intro hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 h hops Pp hG hin d hd
  classical
  have hns : ¬ Formalism.BasicNotions.IsSplitPl D.host Pp := GlobalTheory.T.not_isSplitPlace_of_inert_over_realSubfield D Pp hin
  obtain ⟨v, Dv, hov⟩ := GlobalTheory.T.exists_inertLocalDatum_at_inertPlace D hA.hF Pp hin
  have hfix := GlobalTheory.T.operator_eigen_good_place_first hAF hL D P X hA h41 h7 htl i hμ j hj h hops Pp hG hin v hov
  obtain ⟨h0, hh0, htr⟩ := GlobalTheory.T.operator_eigen_good_place_second hAF hL D P X hA h41 h7 htl i hμ j hj h hops Pp hG hin d hd v Dv hov
  obtain ⟨C, a, xs, hC⟩ := GlobalTheory.EigInert.heckeFunI_umax_sum Dv h0 hh0
  let c : ℂ := if hP : ∃ P0 : D.naut.AV i, D.naut.ptV i P0 = some x then
    Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield D.host.E) v) h0 (GlobalTheory.EigInert.satParam hL D P i hP.choose v Pp hov hns Dv).choose else 0
  refine ⟨c, htr f y c hy (hfix (hj ▸ f)) ?_⟩
  have key : ∀ g ∈ eigC D.nd D.naut i x, heckeFunI D.host.E D.R.nV (Umax D.host.E D.R.nV) Dv h0 ((P.M.loc i).real g) =
      c • (P.M.loc i).real g := by
    intro g hg
    unfold eigC at hg
    refine Submodule.iSup_induction _ (motive := fun g => heckeFunI D.host.E D.R.nV (Umax D.host.E D.R.nV) Dv h0
      ((P.M.loc i).real g) = c • (P.M.loc i).real g) hg ?_ ?_ ?_
    · intro P' g' hg'
      by_cases hP' : D.naut.ptV i P' = some x
      · rw [iSup_pos (show P' ∈ {P | D.naut.ptV i P = some x} from hP')] at hg'
        have hex : ∃ P0 : D.naut.AV i, D.naut.ptV i P0 = some x := ⟨P', hP'⟩
        have hc : c = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV _ v) h0 (GlobalTheory.EigInert.satParam hL D P i hex.choose v Pp hov hns Dv).choose := dif_pos hex
        obtain ⟨α', hα', hsv'⟩ := GlobalTheory.EigInert.satParam hL D P i P' v Pp hov hns Dv
        have hsv0 := (GlobalTheory.EigInert.satParam hL D P i hex.choose v Pp hov hns Dv).choose_spec.2
        have hub : ubc D.R.nV (D.naut.satV i P' Pp) = ubc D.R.nV (D.naut.satV i hex.choose Pp) := by
          have h41i := (show Formalism.MainNotions.SumRepresentations.At.Conclusion41 D.nd D.naut i from h41 i).2.1 P' hex.choose (by rw [hP']; simp) (by rw [hP', hex.choose_spec])
          have hS : Pp ∉ D.nd.S i := fun hm => hns (D.nd.SQ_split i Pp (Or.inl hm))
          have hQ : Pp ∉ D.nd.Q i := fun hm => hns (D.nd.SQ_split i Pp (Or.inr hm))
          exact (h41i.2 Pp hS hQ).2 hns
        rw [hsv', hsv0] at hub
        have hW := GlobalTheory.T.satakeTransform_eq_of_unramifiedBaseChange_eq _ Dv.ϖ Dv.σw _ D.R.nV Dv.unram α' _ hub h0 hh0
        rw [hc, ← hW]
        have hmem : (P.M.loc i).real g' ∈ NG.isoTyp (P.H.av.rep i P').ρ (P.H.av.rep i P').S := by
          have h2 := hg'
          rw [P.H.av.typeV] at h2
          exact h2
        exact GlobalTheory.T.isotypicFixedVector_isSatakeEigen_inertPlace _ _ (P.H.av.rep i P') v Pp hov Dv α' hα' _ hmem (hfix g') h0 hh0
      · rw [iSup_neg (show P' ∉ {P | D.naut.ptV i P = some x} from hP')] at hg'
        rw [(Submodule.mem_bot ℂ).1 hg']
        simp [hC]
    · simp [hC]
    · intro g1 g2 h1 h2
      rw [hC] at h1 h2 ⊢
      simp only [map_add, smul_add, Finset.sum_add_distrib, h1, h2]
  exact key _ hf
end
