import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsNeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerVanishesOfDualVanishes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCochainsGlueGlobal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductUnramifiedClassesVanishes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductCoboundaryModStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCocycleIntegralAfterScaling
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductDualTwistIsTwoCocycleUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TateDualCocycleCoboundaryOfVanishOnFixing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergOrdinaryOfVanishingOnCycloKernel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeightCommutatorInvariance
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCommutatorDetNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CohomologyUnramifiedLift
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EulerSystemTameClassScaleEnlargeCoefficients
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherRest
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerDualVanishesOfStrict

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

namespace GlobalTheory.Ord2

private theorem locEmb_conj {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v) :
    ∃ g : G k Ω, (∀ τ ∈ Ine (F := k) B, g⁻¹ * τ * g ∈ Ine (F := k) A) ∧
      (∀ τ ∈ Dec (F := k) B, g⁻¹ * τ * g ∈ Dec (F := k) A) ∧
      ∀ τ ∈ Dec (F := k) A, g * τ * g⁻¹ ∈ Dec (F := k) B := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := k) hA hB
  have h : IsLift (RingEquiv.refl k) g.toRingEquiv := fun x => g.commutes x
  have hm : ∀ x, g.toRingEquiv x ∈ B ↔ x ∈ A := fun x => by
    show g • x ∈ B ↔ _
    rw [← hg]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  have hm' : ∀ x, g.toRingEquiv.symm x ∈ A ↔ x ∈ B := fun x => by
    rw [← hm, RingEquiv.apply_symm_apply]
  exact ⟨g, fun τ hτ => conjGal_mem_Ine h hm hτ, fun τ hτ => conjGal_mem_Dec h hm hτ,
    fun τ hτ => conjGal_mem_Dec h.symm hm' hτ⟩

theorem bk_locEmb : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (A : ValuationSubring Ω), OverL l A → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → ∃ ι : GQ l →* G ℚ Ω, Continuous ι ∧ (∀ σ, ι σ ∈ Dec (F := ℚ) A) ∧ (∀ s ∈ Dec (F := ℚ) A, ∃ σ, ι σ = s) ∧ (∀ σ ∈ Loc.Iq l, ι σ ∈ Ine (F := ℚ) A) ∧ (∀ σ, cycZ ℚ Ω l (ι σ) = Loc.cyc l l σ) ∧ (fun σ => z (ι σ)) ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp ι) := by
  intro l _ Ω _ iA _ W A hA z hz hb
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : iA = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  obtain ⟨v, hAv, hv⟩ := hA
  obtain ⟨j, -, -, x, hx⟩ := hb.above (algebraMap ℚ (Om l))
  obtain ⟨i1, i2, -, i4, i5, i6, -⟩ := Loc.iotaFacts j
  have h0 : (fun σ => z (Loc.iota j σ)) ∈
      Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp (Loc.iota j)) :=
    ⟨⟨hz.1.comp i1.continuous, fun g h => (congrArg z (map_mul _ g h)).trans (hz.2 _ _)⟩, x,
      fun σ => hx ⟨(Loc.iota j σ, σ), fun y => (Loc.iota_spec j σ y).symm⟩⟩
  obtain ⟨g, g1, g2, g3⟩ := locEmb_conj hAv ((i6 v).2 hv)
  let ι : GQ l →* G ℚ Ω := (MulAut.conj g⁻¹).toMonoidHom.comp (Loc.iota j)
  have hι : ∀ σ, ι σ = g⁻¹ * Loc.iota j σ * g := fun σ => by simp [ι]
  have hc : Continuous ι := by
    have : (ι : GQ l → G ℚ Ω) = fun σ => g⁻¹ * Loc.iota j σ * g := funext hι
    rw [this]
    exact (continuous_const.mul i1.continuous).mul continuous_const
  refine ⟨ι, hc, fun σ => ?_, fun s hs => ?_, fun σ hσ => ?_, fun σ => ?_, ?_⟩
  · rw [hι]
    exact g2 _ (by rw [← i2]; exact ⟨σ, rfl⟩)
  · have h1 : g * s * g⁻¹ ∈ Dec (F := ℚ) (Loc.placeJ j) := g3 s hs
    rw [← i2] at h1
    obtain ⟨σ, hσ⟩ := h1
    exact ⟨σ, by rw [hι, hσ]; group⟩
  · rw [hι]
    exact g1 _ (by rw [← i4]; exact ⟨σ, hσ, rfl⟩)
  · rw [hι, map_mul, map_mul, map_inv, mul_comm _ (cycZ ℚ Ω l (Loc.iota j σ)), inv_mul_cancel_right]
    exact DFunLike.congr_fun (i5 l) σ
  · have h1 := Loc.z1fCoef (MonoidHom.id (GQ l)) ((Loc.colRep W).comp (Loc.iota j)) ((Loc.colRep W).comp ι)
      ((Loc.colRep W g⁻¹).restrictScalars ℚ_[l]) (LinearMap.continuous_on_pi (Loc.colRep W g⁻¹))
      (fun σ y => by
        show Loc.colRep W g⁻¹ (Loc.colRep W (Loc.iota j σ) y) = Loc.colRep W (ι σ) (Loc.colRep W g⁻¹ y)
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hι, mul_inv_cancel_right]) _ h0
    have hcob : ∀ σ, Loc.colRep W (ι σ) (z g⁻¹) - z g⁻¹ = z (ι σ * g⁻¹) - z (ι σ) - z g⁻¹ := fun σ => by
      rw [hz.2]; abel
    have h2 : (fun σ => Loc.colRep W (ι σ) (z g⁻¹) - z g⁻¹) ∈
        Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp ι) := by
      refine ⟨⟨?_, fun a b => ?_⟩, z g⁻¹ ⊗ₜ 1, fun σ => ?_⟩
      · rw [funext hcob]
        exact ((hz.1.comp (hc.mul continuous_const)).sub (hz.1.comp hc)).sub continuous_const
      · show Loc.colRep W (ι (a * b)) (z g⁻¹) - z g⁻¹ = Loc.colRep W (ι a) (z g⁻¹) - z g⁻¹ +
          Loc.colRep W (ι a) (Loc.colRep W (ι b) (z g⁻¹) - z g⁻¹)
        rw [map_mul, map_mul, Module.End.mul_apply, map_sub]; abel
      · simp [Loc.actC, TensorProduct.sub_tmul]
    have h3 := Submodule.sub_mem _ h1 h2
    convert h3 using 1
    funext σ
    show z (ι σ) = Loc.colRep W g⁻¹ (z (Loc.iota j σ)) - (Loc.colRep W (ι σ) (z g⁻¹) - z g⁻¹)
    have e1 := hz.2 g⁻¹ (Loc.iota j σ)
    rw [hcob, hι, mul_inv_cancel_right, e1]
    abel

end GlobalTheory.Ord2
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineClass_restrict_decompositionGroup : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (A : ValuationSubring Ω), OverL l A → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → ∃ ι : GQ l →* G ℚ Ω, Continuous ι ∧ (∀ σ, ι σ ∈ Dec (F := ℚ) A) ∧ (∀ s ∈ Dec (F := ℚ) A, ∃ σ, ι σ = s) ∧ (∀ σ ∈ Loc.Iq l, ι σ ∈ Ine (F := ℚ) A) ∧ (∀ σ, cycZ ℚ Ω l (ι σ) = Loc.cyc l l σ) ∧ (fun σ => z (ι σ)) ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp ι) := by
  atlas_forward_decl GlobalTheory.Ord2.bk_locEmb
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

namespace GlobalTheory

theorem hasWeight_neg_of_pow_cyc_inertia : ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ),
    Continuous (fun σ => (κ σ : Qbar l)) → ∀ (e m : ℕ), 1 ≤ m →
    (∀ σ ∈ Loc.Iq l, (κ σ * Loc.cycA l l (Qbar l) σ ^ (e : ℤ)) ^ m = 1) →
    Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
  intro l _ κ hκ e m hm h
  have hcyc : Continuous (Loc.cyc l l) := cyclotomicCharacter.continuous l ℚ_[l] (Om l)
  have ha : Continuous (algebraMap ℤ_[l] (Qbar l)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l)]
    exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
  have hA : Continuous (fun σ => (Loc.cycA l l (Qbar l) σ : Qbar l)) :=
    Units.continuous_val.comp
      ((Continuous.units_map (algebraMap ℤ_[l] (Qbar l) : ℤ_[l] →* Qbar l) ha).comp hcyc)
  set f : GQ l → Qbar l := fun σ => ((κ σ * Loc.cycA l l (Qbar l) σ ^ (e : ℤ) : (Qbar l)ˣ) : Qbar l) with hf_def
  have hf : Continuous f := by
    have : f = fun σ => (κ σ : Qbar l) * (Loc.cycA l l (Qbar l) σ : Qbar l) ^ e := by
      funext σ
      simp only [hf_def, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
    rw [this]
    exact hκ.mul (hA.pow e)
  have hf1 : f 1 = 1 := by simp [hf_def]
  have hm0 : 0 < m := hm
  have hfin : ({z : Qbar l | z ^ m = 1} \ {1}).Finite := by
    refine Set.Finite.subset (Multiset.finite_toSet (Polynomial.nthRoots m (1 : Qbar l))) fun z hz => ?_
    exact (Polynomial.mem_nthRoots hm0).2 hz.1
  have ho : IsOpen (f ⁻¹' ({z : Qbar l | z ^ m = 1} \ {1})ᶜ) :=
    hfin.isClosed.isOpen_compl.preimage hf
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho
    (fun hx => hx.2 hf1)
  refine ⟨U.toOpenSubgroup.toSubgroup, U.toOpenSubgroup.isOpen, fun g hg hgI => ?_⟩
  have hgI' : g ∈ Loc.Iq l := hgI
  have hpow : f g ^ m = 1 := by
    have := congrArg Units.val (h g hgI')
    simpa [hf_def, Units.val_pow_eq_pow_val] using this
  have hone : f g = 1 := by
    by_contra hne
    exact hU hg ⟨hpow, hne⟩
  have hu : κ g * Loc.cycA l l (Qbar l) g ^ (e : ℤ) = 1 := Units.ext hone
  simp only [MonoidHom.id_apply, zpow_neg]
  exact eq_inv_of_mul_eq_one_left hu

end GlobalTheory
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasWeight_neg_of_cyclotomic_pow_on_inertia : ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ), Continuous (fun σ => (κ σ : Qbar l)) → ∀ (e m : ℕ), 1 ≤ m → (∀ σ ∈ Loc.Iq l, (κ σ * Loc.cycA l l (Qbar l) σ ^ (e : ℤ)) ^ m = 1) → Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
  atlas_forward_decl GlobalTheory.hasWeight_neg_of_pow_cyc_inertia
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

noncomputable section

namespace GlobalTheory.NegVan

private theorem fd_adjoin_range (l : ℕ) [Fact l.Prime] {ι : Type} [Finite ι] (f : ι → PadicAlgCl l) :
    FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range f)) := by
  haveI : Finite (Set.range f) := (Set.finite_range _).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral

open TensorProduct in

private theorem desc {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] (φ : H →* GQ l)
    (κ : H →* (PadicAlgCl l)ˣ) (E₀ : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] E₀]
    (hκ : ∀ g, (κ g : PadicAlgCl l) ∈ E₀) (c : H → PadicAlgCl l) (hc : c ∈ Loc.finiteCocycles φ (Loc.chRep κ)) :
    ∃ (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (_ : FiniteDimensional ℚ_[l] E) (κ' : H →* Eˣ) (c' : H → E),
      (∀ g, ((κ' g : E) : PadicAlgCl l) = κ g) ∧ (∀ g, (c' g : PadicAlgCl l) = c g) ∧ c' ∈ Loc.finiteCocycles φ (Loc.chRep κ') := by
  obtain ⟨⟨hcc, hcoc⟩, x, hx⟩ := hc
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  obtain ⟨T⟩ := Loc.tiedP l
  haveI : IsDomain (Loc.Bcr l) := GlobalTheory.RegularRing.isDomain_of_tied T (Loc.botExt l)
  haveI := fd_adjoin_range l (fun p : S => p.1.1)
  let E : IntermediateField ℚ_[l] (PadicAlgCl l) := E₀ ⊔ IntermediateField.adjoin ℚ_[l] (Set.range fun p : S => p.1.1)
  have hκE : ∀ g, (κ g : PadicAlgCl l) ∈ E := fun g => (le_sup_left : E₀ ≤ E) (hκ g)
  have hS : ∀ p ∈ S, p.1 ∈ E := fun p hp =>
    (le_sup_right : _ ≤ E) (IntermediateField.subset_adjoin _ _ ⟨⟨p, hp⟩, rfl⟩)
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E (PadicAlgCl l))
    (LinearMap.ker_eq_bot.2 (algebraMap E (PadicAlgCl l)).injective)
  have hπ1 : ∀ y : E, π (y : PadicAlgCl l) = y := fun y => LinearMap.congr_fun hπ y
  let κ' : H →* Eˣ := MonoidHom.toHomUnits
    { toFun := fun g => ⟨κ g, hκE g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }
  have hκ' : ∀ g, ((κ' g : E) : PadicAlgCl l) = κ g := fun g => rfl
  have hπ2 : ∀ g y, π (κ g * y) = κ' g * π y := fun g y => map_smul π (κ' g : E) y
  let f : PadicAlgCl l →ₗ[ℚ_[l]] E := π.restrictScalars ℚ_[l]
  let i : E →ₗ[ℚ_[l]] PadicAlgCl l := E.val.toLinearMap
  have key : ∀ g (y : PadicAlgCl l ⊗[ℚ_[l]] Loc.Bcr l), LinearMap.rTensor (Loc.Bcr l) f (Loc.actC φ (Loc.chRep κ) g y) =
      Loc.actC φ (Loc.chRep κ') g (LinearMap.rTensor (Loc.Bcr l) f y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Loc.actC, Loc.chRep, f, hπ2]
    | add a b ha hb => simp only [map_add, ha, hb]
  have key' : ∀ g (y : E ⊗[ℚ_[l]] Loc.Bcr l), LinearMap.rTensor (Loc.Bcr l) i (Loc.actC φ (Loc.chRep κ') g y) =
      Loc.actC φ (Loc.chRep κ) g (LinearMap.rTensor (Loc.Bcr l) i y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Loc.actC, Loc.chRep, i, hκ']
    | add a b ha hb => simp only [map_add, ha, hb]
  set x := ∑ p ∈ S, p.1 ⊗ₜ[ℚ_[l]] p.2 with hxd
  have hix : LinearMap.rTensor (Loc.Bcr l) i (LinearMap.rTensor (Loc.Bcr l) f x) = x := by
    rw [hxd, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    congr 1
    exact congrArg Subtype.val (hπ1 ⟨p.1, hS p hp⟩)
  have hx' : ∀ g, f (c g) ⊗ₜ[ℚ_[l]] (1 : Loc.Bcr l) =
      Loc.actC φ (Loc.chRep κ') g (LinearMap.rTensor (Loc.Bcr l) f x) - LinearMap.rTensor (Loc.Bcr l) f x := fun g => by
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
  have hcE : ∀ g, ((f (c g) : E) : PadicAlgCl l) = c g := fun g => by
    have h1 := congrArg (LinearMap.rTensor (Loc.Bcr l) i) (hx' g)
    rw [map_sub, key', hix, ← hx g, LinearMap.rTensor_tmul] at h1
    exact Algebra.TensorProduct.includeLeft_injective (R := ℚ_[l]) (S := ℚ_[l]) (B := Loc.Bcr l)
      (algebraMap ℚ_[l] (Loc.Bcr l)).injective h1
  refine ⟨E, inferInstance, κ', fun g => f (c g), hκ', hcE, ⟨?_, fun g h => ?_⟩, _, hx'⟩
  · exact continuous_induced_rng.2 (hcc.congr fun g => (hcE g).symm)
  · have := hcoc g h
    simp only [Loc.chRep] at this ⊢
    simp [this, f, hπ2]

private theorem coef_finext {l : ℕ} [Fact l.Prime] (c : Coef l) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ x ∈ c.O, x ∈ K := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := ℤ_[l]) (M := c.O))
  refine ⟨_, fd_adjoin_range l (fun q : s => ((q : c.O) : PadicAlgCl l)), fun x hx => ?_⟩
  let K := IntermediateField.adjoin ℚ_[l] (Set.range fun q : s => ((q : c.O) : PadicAlgCl l))
  let M : Submodule ℤ_[l] (PadicAlgCl l) := (K.toSubalgebra.restrictScalars ℤ_[l]).toSubmodule
  have hmem : (⟨x, hx⟩ : c.O) ∈ Submodule.span ℤ_[l] (s : Set c.O) := hs ▸ Submodule.mem_top
  have hle : Submodule.span ℤ_[l] (s : Set c.O) ≤ M.comap c.O.val.toLinearMap := by
    rw [Submodule.span_le]
    intro q hq
    exact IntermediateField.subset_adjoin _ _ ⟨⟨q, hq⟩, rfl⟩
  exact hle hmem

end GlobalTheory.NegVan

open GlobalTheory.NegVan in

theorem GlobalTheory.NegVan.crys_cocycle_coboundary_of_neg_weight :
    Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ), Continuous (fun σ => (κ σ : Qbar l)) →
      ∀ c : Coef l, (∀ σ, (κ σ : Qbar l) ∈ c.O) → ∀ w : ℤ, w < 0 → Loc.HasWeight (MonoidHom.id (GQ l)) κ w →
      ∀ f ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) (Loc.chRep κ), ∃ x, ∀ σ, f σ = (κ σ : Qbar l) * x - x := by
  intro hP l _ κ hκc c hκO w hw hwt f hf
  obtain ⟨K₀, hK₀, hK⟩ := coef_finext c
  obtain ⟨E, _, κ', c', hκ, hc', hf'⟩ := desc (MonoidHom.id (GQ l)) κ K₀ (fun g => hK _ (hκO g)) f hf
  haveI : IsModuleTopology ℚ_[l] E := isModuleTopologyOfFiniteDimensional
  have hw' : Loc.HasWeight (MonoidHom.id (GQ l)) κ' w := by
    obtain ⟨U, hU, hUw⟩ := hwt
    refine ⟨U, hU, fun g hg hI => ?_⟩
    have h := hUw g hg hI
    have hcy : Units.map ((algebraMap E (PadicAlgCl l) : E →+* PadicAlgCl l) : E →* PadicAlgCl l)
        (Loc.cycA l l E g) = Loc.cycA l l (PadicAlgCl l) g := by
      refine Units.ext ?_
      simp only [Units.coe_map, MonoidHom.coe_coe, Loc.cycA, MonoidHom.comp_apply]
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
      rfl
    apply Units.map_injective (f := ((algebraMap E (PadicAlgCl l) : E →+* PadicAlgCl l) : E →* PadicAlgCl l))
      (algebraMap E (PadicAlgCl l)).injective
    rw [map_zpow, MonoidHom.id_apply, hcy, ← MonoidHom.id_apply (GQ l) g, ← h]
    exact Units.ext (hκ g)
  have hz := (Loc.z1fChar hP (MonoidHom.id (GQ l)) Topology.IsOpenEmbedding.id κ'
    (continuous_induced_rng.2 (hκc.congr fun g => (hκ g).symm)) w hw').1 hw
  rw [hz.1, mem_coboundaries1] at hf'
  obtain ⟨m, hm⟩ := hf'
  refine ⟨(m : PadicAlgCl l), fun σ => ?_⟩
  have h4 : c' σ = κ' σ * m - m := hm σ
  rw [← hc' σ, h4, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hκ]
end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineCocycle_coboundary_of_negative_weight : Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ), Continuous (fun σ => (κ σ : Qbar l)) → ∀ c : Coef l, (∀ σ, (κ σ : Qbar l) ∈ c.O) → ∀ w : ℤ, w < 0 → Loc.HasWeight (MonoidHom.id (GQ l)) κ w → ∀ f ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) (Loc.chRep κ), ∃ x, ∀ σ, f σ = (κ σ : Qbar l) * x - x := by
  atlas_forward_decl GlobalTheory.NegVan.crys_cocycle_coboundary_of_neg_weight
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

namespace GlobalTheory.Ord2

theorem bk_unr_gr : Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → Unr W z ∧ Gr W A z := by
  intro hP l _ Ω _ _ _ e S A W hN z hz hbk
  have hcol : ∀ s x, Loc.colRep W s x = mat W s *ᵥ x := fun s x => by
    simp [Loc.colRep, Matrix.toLin'_apply]
  refine ⟨fun w hw => ?_, ?_⟩
  · obtain ⟨B, hB, x, hx⟩ := hbk.away w hw
    exact ⟨B, hB, x, fun s hs => by rw [hx s hs, hcol]⟩
  obtain ⟨ι, hιc, hιD, hιS, hιI, hιcyc, hιZ⟩ := GlobalTheory.T.crystallineClass_restrict_decompositionGroup l Ω W A hN.atL z hz hbk
  have hup : ∀ σ, mat W (ι σ) 1 0 = 0 := fun σ => hN.upper _ (hιD σ)
  let k0 : GQ l →* Qbar l :=
    { toFun := fun σ => mat W (ι σ) 1 1
      map_one' := by simp [mat]
      map_mul' := fun σ τ => by
        have h := hup σ
        simp only [mat] at h
        simp only [mat, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h, zero_mul, zero_add] }
  let κ : GQ l →* (Qbar l)ˣ := k0.toHomUnits
  have hκ : ∀ σ, (κ σ : Qbar l) = mat W (ι σ) 1 1 := fun σ => rfl
  have hκc : Continuous fun σ => (κ σ : Qbar l) :=
    ((Units.continuous_val.comp (hN.cont.comp hιc)).matrix_elem 1 1)
  let f : (Fin 2 → Qbar l) →ₗ[ℚ_[l]] Qbar l := LinearMap.proj (R := ℚ_[l]) (φ := fun _ : Fin 2 => Qbar l) 1
  have hf : ∀ σ x, f (((Loc.colRep W).comp ι) σ x) = Loc.chRep κ σ (f x) := fun σ x => by
    have h := hup σ
    simp only [mat] at h
    simp [f, Loc.chRep, hcol, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hκ, mat, h]
  have hc := Loc.z1fCoef (MonoidHom.id (GQ l)) _ _ f (continuous_apply 1) hf _ hιZ
  obtain ⟨c, hcO⟩ := hN.int
  obtain ⟨m, hm1, hm⟩ := hN.wt
  have hw : Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
    refine GlobalTheory.T.hasWeight_neg_of_cyclotomic_pow_on_inertia l κ hκc e (2 * m) (by omega) fun σ hσ => ?_
    have hs := hιI σ hσ
    have h0 := hm _ hs
    have hd : (dt W (ι σ) : Qbar l) ^ 2 = 1 := by
      have := congrArg (fun u : G ℚ Ω →* (Qbar l)ˣ => ((u (ι σ) : (Qbar l)ˣ) : Qbar l)) hN.det2
      simpa using this
    have hdet : (dt W (ι σ) : Qbar l) = mat W (ι σ) 0 0 * mat W (ι σ) 1 1 := by
      have h := hup σ
      simp only [mat] at h
      simp [dt, Matrix.det_fin_two, mat, h]
    have hcy : (Loc.cycA l l (Qbar l) σ : Qbar l) = eps l (ι σ) := by
      simp only [Loc.cycA, eps, cycBar, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, hιcyc, RingHom.coe_comp, Function.comp_apply]
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
      rfl
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_zpow_eq_zpow_val, zpow_natCast, Units.val_one, hκ, hcy]
    rw [hdet] at hd
    calc (mat W (ι σ) 1 1 * eps l (ι σ) ^ e) ^ (2 * m) = (mat W (ι σ) 1 1) ^ (2 * m) * (eps l (ι σ) ^ (e * m)) ^ 2 := by ring
      _ = ((mat W (ι σ) 0 0 * mat W (ι σ) 1 1) ^ 2) ^ m := by rw [← h0]; ring
      _ = 1 := by rw [hd, one_pow]
  obtain ⟨x, hx⟩ := GlobalTheory.T.crystallineCocycle_coboundary_of_negative_weight hP l κ hκc c (fun σ => hcO _ 1 1) (-(e : ℤ)) (by have := hN.e_pos; omega) hw _ hc
  refine ⟨x, fun s hs => ?_⟩
  obtain ⟨σ, rfl⟩ := hιS s hs
  have := hx σ
  simpa [f, hκ] using this

end GlobalTheory.Ord2
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_cocycle_unramified_and_greenbergOrdinary : Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → Unr W z ∧ Gr W A z := by
  atlas_forward_decl GlobalTheory.Ord2.bk_unr_gr
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_cochains_glue_global : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (ξ : G ℚ Ω → G ℚ Ω → Qbar l), l ≠ 2 → ContainsAbove S l → Coc2 c n S ξ → (∀ v ∈ S, ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Cob2 c n (Dec (F := ℚ) B) ξ) → ∃ u : G ℚ Ω → Qbar l, Continuous u ∧ (∀ s, u s ∈ c.O) ∧ (∀ s, ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cg n (u (s * a)) (u s)) ∧ ∀ s t, Cg n (ξ s t) (eps l s * u t - u (s * t) + u s) := by
  first | exact @GlobalTheory.Ord2.TwistTriv.coboundary_of_locTriv | exact GlobalTheory.Ord2.TwistTriv.coboundary_of_locTriv | (intros; apply GlobalTheory.Ord2.TwistTriv.coboundary_of_locTriv <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.greenbergOrdinary_of_vanishing_on_cycloKernel : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ y ∈ Z1 (Loc.colRep W), (∀ g ∈ N0g W, y g = 0) → Gr W A y := by
  first | exact @GlobalTheory.Ord2.GrOfKill.gr_of_vanish_on_trivial | exact GlobalTheory.Ord2.GrOfKill.gr_of_vanish_on_trivial | (intros; apply GlobalTheory.Ord2.GrOfKill.gr_of_vanish_on_trivial <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_commutator_invariance : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (c : Coef l) (W : R2 Ω l) (y z : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → ∀ φ ∈ H0g W, ∀ g ∈ N0g W, ∀ h ∈ N0g W, Cg n (ht W y z u (φ * (g * h * g⁻¹ * h⁻¹)) - ht W y z u φ) ((mat W φ - 1).det * (om (y h) (z g) - om (y g) (z h))) := by
  first | exact @GlobalTheory.Ord2.ht_commutator | exact GlobalTheory.Ord2.ht_commutator | (intros; apply GlobalTheory.Ord2.ht_commutator <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.PairSpan

section Abstract

variable {Γ k : Type} [Group Γ] [Field k]

theorem alt_left_nondeg {v : Fin 2 → k} (hv : v ≠ 0) : ∃ a : Fin 2 → k, v 0 * a 1 - v 1 * a 0 ≠ 0 := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1; apply hv; funext i; fin_cases i <;> simp [h0, h1]
    exact ⟨![1, 0], by simp [h1]⟩
  · exact ⟨![0, 1], by simp [h0]⟩

theorem stable_cases {W : Γ →* GL (Fin 2) k} {H : Subgroup Γ} (hirr : UpperTheory.V.Af.IsIrr (W.comp H.subtype))
    (U : Submodule k (Fin 2 → k)) (hU : ∀ s ∈ H, ∀ v ∈ U, (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∈ U) :
    U = ⊥ ∨ U = ⊤ :=
  hirr.2.2 U le_top (by intro g v hv; exact hU g g.2 v hv)

theorem coc_conj {n : ℕ} (ρ : Γ →* GL (Fin n) k) (y : Γ → Fin n → k)
    (hy : ∀ g h, y (g * h) = y g + (ρ g : Matrix (Fin n) (Fin n) k) *ᵥ y h) (s g : Γ) (hg : ρ g = 1) :
    y (s * g * s⁻¹) = (ρ s : Matrix (Fin n) (Fin n) k) *ᵥ y g := by
  have h1 : y 1 = 0 := by simpa using hy 1 1
  have h2 : y s + (ρ s : Matrix (Fin n) (Fin n) k) *ᵥ y s⁻¹ = 0 := by rw [← hy, mul_inv_cancel, h1]
  rw [hy, hy, map_mul, hg, mul_one, add_right_comm, h2, zero_add]

end Abstract
end GlobalTheory.Ord2.PairSpan

namespace GlobalTheory.Ord2.PairSpan

variable {Γ k : Type} [Group Γ] [Field k]

theorem exists_pair_ne [IsAlgClosed k] [CharZero k] {W : Γ →* GL (Fin 2) k} {H : Subgroup Γ}
    (hirr : UpperTheory.V.Af.IsIrr (W.comp H.subtype)) {N : Set Γ}
    (hN : ∀ s ∈ H, ∀ g ∈ N, s * g * s⁻¹ ∈ N) {y z : Γ → Fin 2 → k}
    (hy : ∀ s ∈ H, ∀ g ∈ N, y (s * g * s⁻¹) = (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ y g)
    (hz : ∀ s ∈ H, ∀ g ∈ N, z (s * g * s⁻¹) = (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ z g)
    (hy0 : ∃ g ∈ N, y g ≠ 0) (hz0 : ∃ g ∈ N, z g ≠ 0) :
    ∃ g ∈ N, ∃ h ∈ N, y h 0 * z g 1 - y h 1 * z g 0 ≠ y g 0 * z h 1 - y g 1 * z h 0 := by
  by_contra hcon
  push_neg at hcon
  let Sig : Submodule k ((Fin 2 → k) × (Fin 2 → k)) := Submodule.span k ((fun g => (y g, z g)) '' N)
  have hgen : ∀ g ∈ N, (y g, z g) ∈ Sig := fun g hg => Submodule.subset_span ⟨g, hg, rfl⟩
  have hinv : ∀ s ∈ H, ∀ σ ∈ Sig,
      ((W s : Matrix (Fin 2) (Fin 2) k) *ᵥ σ.1, (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ σ.2) ∈ Sig := by
    intro s hs σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      rw [← hy s hs g hg, ← hz s hs g hg]
      exact hgen _ (hN s hs g hg)
    | zero =>
      simp only [Prod.fst_zero, Prod.snd_zero, Matrix.mulVec_zero, Prod.mk_zero_zero]
      exact Sig.zero_mem
    | add x x' _ _ ihx ihx' => simpa [Matrix.mulVec_add] using Sig.add_mem ihx ihx'
    | smul a x _ ihx => simpa [Matrix.mulVec_smul] using Sig.smul_mem a ihx
  have hB : ∀ g ∈ N, ∀ σ ∈ Sig, y g 0 * σ.2 1 - y g 1 * σ.2 0 = σ.1 0 * z g 1 - σ.1 1 * z g 0 := by
    intro g hg σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      exact (hcon g hg h hh).symm
    | zero => simp
    | add x x' _ _ ihx ihx' =>
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      linear_combination ihx + ihx'
    | smul a x _ ihx =>
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      linear_combination a * ihx
  let K' : Submodule k (Fin 2 → k) := Sig.comap (LinearMap.inr k (Fin 2 → k) (Fin 2 → k))
  have hK' : K' = ⊥ := by
    rcases stable_cases hirr K' (by
      intro s hs v hv
      have := hinv s hs _ hv
      simpa [K', Matrix.mulVec_zero] using this) with h | h
    · exact h
    · exfalso
      obtain ⟨g, hg, hyg⟩ := hy0
      obtain ⟨a, ha⟩ := alt_left_nondeg hyg
      have hmem : ((0 : Fin 2 → k), a) ∈ Sig := by
        have : a ∈ K' := h ▸ Submodule.mem_top
        simpa [K'] using this
      exact ha ((hB g hg _ hmem).trans (by simp))
  let P : Submodule k (Fin 2 → k) := Sig.map (LinearMap.fst k (Fin 2 → k) (Fin 2 → k))
  have hP : P = ⊤ := by
    rcases stable_cases hirr P (by
      rintro s hs v ⟨σ, hσ, rfl⟩
      exact ⟨_, hinv s hs σ hσ, rfl⟩) with h | h
    · exfalso
      obtain ⟨g, hg, hyg⟩ := hy0
      have : y g ∈ P := ⟨_, hgen g hg, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hyg this
    · exact h
  let f : Sig →ₗ[k] (Fin 2 → k) := (LinearMap.fst k (Fin 2 → k) (Fin 2 → k)).comp Sig.subtype
  have hfi : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun σ hσ => ?_
    have h1 : (σ : (Fin 2 → k) × (Fin 2 → k)).1 = 0 := hσ
    have h2 : (σ : (Fin 2 → k) × (Fin 2 → k)).2 ∈ K' := by
      show LinearMap.inr k _ _ (σ : (Fin 2 → k) × (Fin 2 → k)).2 ∈ Sig
      have : LinearMap.inr k (Fin 2 → k) (Fin 2 → k) (σ : (Fin 2 → k) × (Fin 2 → k)).2 = σ := by
        ext1 <;> simp [h1]
      rw [this]; exact σ.2
    rw [hK', Submodule.mem_bot] at h2
    exact Subtype.ext (Prod.ext h1 h2)
  have hfs : Function.Surjective f := by
    intro a
    have : a ∈ P := hP ▸ Submodule.mem_top
    obtain ⟨σ, hσ, rfl⟩ := this
    exact ⟨⟨σ, hσ⟩, rfl⟩
  let e := LinearEquiv.ofBijective f ⟨hfi, hfs⟩
  let φ : Module.End k (Fin 2 → k) :=
    (LinearMap.snd k (Fin 2 → k) (Fin 2 → k)).comp (Sig.subtype.comp e.symm.toLinearMap)
  have hφmem : ∀ a, (a, φ a) ∈ Sig := by
    intro a
    have h1 : ((e.symm a : Sig) : (Fin 2 → k) × (Fin 2 → k)).1 = a := e.apply_symm_apply a
    have : (a, φ a) = ((e.symm a : Sig) : (Fin 2 → k) × (Fin 2 → k)) := Prod.ext h1.symm rfl
    rw [this]; exact (e.symm a).2
  have hφ : ∀ σ ∈ Sig, φ σ.1 = σ.2 := by
    intro σ hσ
    have : e.symm σ.1 = ⟨σ, hσ⟩ := e.symm_apply_eq.2 rfl
    show ((e.symm σ.1 : Sig) : (Fin 2 → k) × (Fin 2 → k)).2 = σ.2
    rw [this]
  have hφW : ∀ s ∈ H, ∀ a, φ ((W s : Matrix (Fin 2) (Fin 2) k) *ᵥ a) = (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ φ a :=
    fun s hs a => hφ _ (hinv s hs _ (hφmem a))
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue φ
  have hE : Module.End.eigenspace φ c = ⊤ := by
    rcases stable_cases hirr (Module.End.eigenspace φ c) (by
      intro s hs v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [hφW s hs, hv, Matrix.mulVec_smul]) with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
    · exact h
  have hφc : ∀ a, φ a = c • a := fun a => Module.End.mem_eigenspace_iff.1 (hE ▸ Submodule.mem_top)
  have hzy : ∀ g ∈ N, z g = c • y g := fun g hg => by rw [← hφc]; exact (hφ _ (hgen g hg)).symm
  obtain ⟨g1, hg1, hzg1⟩ := hz0
  have hc0 : c ≠ 0 := by rintro rfl; apply hzg1; rw [hzy g1 hg1, zero_smul]
  obtain ⟨g0, hg0, hyg0⟩ := hy0
  have horth : ∀ h ∈ N, y g0 0 * y h 1 - y g0 1 * y h 0 = 0 := by
    intro h hh
    have := hcon h hh g0 hg0
    rw [hzy h hh, hzy g0 hg0] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have h2 : (2 * c) * (y g0 0 * y h 1 - y g0 1 * y h 0) = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exfalso; exact hc0 (by simpa using h3)
    · exact h3
  have hall : ∀ σ ∈ Sig, y g0 0 * σ.1 1 - y g0 1 * σ.1 0 = 0 := by
    intro σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      exact horth h hh
    | zero => simp
    | add x x' _ _ ihx ihx' =>
      simp only [Prod.fst_add, Pi.add_apply]
      linear_combination ihx + ihx'
    | smul a x _ ihx =>
      simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      linear_combination a * ihx
  obtain ⟨a, ha⟩ := alt_left_nondeg hyg0
  exact ha (hall _ (hφmem a))

end GlobalTheory.Ord2.PairSpan

namespace GlobalTheory.Ord2

open PairSpan in

theorem exists_om_ne_swap_on_N0g : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ y ∈ Z1 (Loc.colRep W),
    ∀ z ∈ Z1 (Loc.colRep (dual1 W)), (∃ g ∈ N0g W, y g ≠ 0) → (∃ g ∈ N0g W, z g ≠ 0) →
    ∃ g ∈ N0g W, ∃ h ∈ N0g W, om (y h) (z g) ≠ om (y g) (z h) := by
  intro l _ Ω _ _ _ e S A W hW y hyZ z hzZ hy0 hz0
  have hy' : ∀ g h, y (g * h) = y g + (W g : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ y h := fun g h => by
    rw [hyZ.2 g h]; rfl
  have hz' : ∀ g h, z (g * h) = z g + (dual1 W g : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ z h := fun g h => by
    rw [hzZ.2 g h]; rfl
  have hnorm : (N0g W).Normal := by unfold N0g; infer_instance
  have hdual : ∀ s, cycBar ℚ Ω l s = 1 → dt W s = 1 → dual1 W s = W s := by
    intro s h1 h2
    apply Units.ext
    rw [dual1, tw_val]
    simp [h1, h2]
  have hN1 : ∀ g ∈ N0g W, W g = 1 := fun g hg => (Subgroup.mem_inf.1 hg).2
  have hNd : ∀ g ∈ N0g W, dual1 W g = 1 := by
    intro g hg
    have h1 : cycBar ℚ Ω l g = 1 := (Subgroup.mem_inf.1 hg).1
    have h2 : dt W g = 1 := by
      show Matrix.GeneralLinearGroup.det (W g) = 1
      rw [hN1 g hg, map_one]
    rw [hdual g h1 h2, hN1 g hg]
  have hH : ∀ s ∈ H0g W, dual1 W s = W s := fun s hs =>
    hdual s (Subgroup.mem_inf.1 hs).1 (Subgroup.mem_inf.1 hs).2
  obtain ⟨g, hg, h, hh, hne⟩ := exists_pair_ne (k := Qbar l) (W := W) (H := H0g W) (N := (N0g W : Set (G ℚ Ω)))
    hW.irr (fun s _ g hg => hnorm.conj_mem g hg s)
    (y := y) (z := z)
    (fun s _ g hg => coc_conj W y hy' s g (hN1 g hg))
    (fun s hs g hg => by rw [coc_conj (dual1 W) z hz' s g (hNd g hg), hH s hs])
    hy0 hz0
  exact ⟨g, hg, h, hh, hne⟩

end GlobalTheory.Ord2

end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_pair_alternating_ne_on_cycloKernel : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ y ∈ Z1 (Loc.colRep W), ∀ z ∈ Z1 (Loc.colRep (dual1 W)), (∃ g ∈ N0g W, y g ≠ 0) → (∃ g ∈ N0g W, z g ≠ 0) → ∃ g ∈ N0g W, ∃ h ∈ N0g W, om (y h) (z g) ≠ om (y g) (z h) := by
  atlas_forward_decl GlobalTheory.Ord2.exists_om_ne_swap_on_N0g
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerSystemTameClass_scale_enlarge_coefficients : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c c' : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (n : ℕ) (w : Pl) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (a : Qbar l), c.O ≤ c'.O → a ∈ c'.O → Tame c W y n w ψ → Tame c' W (fun s => a • y s) n w ψ := by
  first | exact @GlobalTheory.Ord2.tame_scale | exact GlobalTheory.Ord2.tame_scale | (intros; apply GlobalTheory.Ord2.tame_scale <;> assumption)
end

section
namespace GlobalTheory.IdealComapPreimage

open IsDedekindDomain

theorem ideal_eq_comap {p : ℕ} (hp : Nat.Prime p)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hv : (p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal) :
    v.asIdeal = Ideal.comap (Rat.ringOfIntegersEquiv : NumberField.RingOfIntegers ℚ →+* ℤ)
      (Ideal.span {(p : ℤ)}) := by
  set e := Rat.ringOfIntegersEquiv
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  haveI : (Ideal.comap (e : NumberField.RingOfIntegers ℚ →+* ℤ) (Ideal.span {(p : ℤ)})).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ e.surjective
  symm
  refine Ideal.IsMaximal.eq_of_le this v.isPrime.ne_top ?_
  intro x hx
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hx
  obtain ⟨k, hk⟩ := hx
  have : x = (p : NumberField.RingOfIntegers ℚ) * e.symm k := by
    apply e.injective
    simpa using hk
  rw [this]
  exact v.asIdeal.mul_mem_right _ hv

theorem main : ∀ {p : ℕ}, Nat.Prime p → ∀ {v v' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)}, (↑p : NumberField.RingOfIntegers ℚ) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → (↑p : NumberField.RingOfIntegers ℚ) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v' → v = v' := by
  intro p hp v v' hv hv'
  apply HeightOneSpectrum.ext
  rw [ideal_eq_comap hp v hv, ideal_eq_comap hp v' hv']

end GlobalTheory.IdealComapPreimage
end

section
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.StrictKill

section Basic

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.Rb6.norm_le_one_of_mem c hx

theorem place_eq {p : ℕ} (hp : p.Prime) {v v' : HeightOneSpectrum (𝓞 ℚ)} (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (hv' : ((p : ℕ) : 𝓞 ℚ) ∈ v'.asIdeal) : v = v' :=
  _root_.GlobalTheory.IdealComapPreimage.main hp hv hv'

theorem cg_self (n : ℕ) (a : Qbar l) : Cg n a a := by
  unfold Cg; rw [sub_self, norm_zero]; exact norm_nonneg _

theorem cv_of_eq (n : ℕ) {a b : Fin 2 → Qbar l} (h : a = b) : Cv n a b := by
  subst h; intro i; exact cg_self n _

theorem norm_l_lt_one : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem sub_one_mem (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : ∀ i j, M i j ∈ c.O) (i j : Fin 2) :
    (M - 1) i j ∈ c.O := by
  rw [Matrix.sub_apply, Matrix.one_apply]
  split_ifs
  · exact sub_mem (hM i j) (one_mem _)
  · exact sub_mem (hM i j) (zero_mem _)

theorem det_mem (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : ∀ i j, M i j ∈ c.O) : M.det ∈ c.O := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hM 0 0) (hM 1 1)) (mul_mem (hM 0 1) (hM 1 0))

end Basic

section Twist

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem colRep_apply (W : R2 Ω l) (s : G ℚ Ω) (v : Fin 2 → Qbar l) : Loc.colRep W s v = mat W s *ᵥ v := by
  simp [Loc.colRep, mat, Matrix.toLin'_apply]

theorem mat_dual1 (W : R2 Ω l) (s : G ℚ Ω) :
    mat (dual1 W) s = (eps l s * (((dt W s)⁻¹ : (Qbar l)ˣ) : Qbar l)) • mat W s := by
  simp only [mat, dual1, tw_val, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, eps]

theorem dt_inv (W : R2 Ω l) (h2 : dt W ^ 2 = 1) (s : G ℚ Ω) : (dt W s)⁻¹ = dt W s := by
  have h := DFunLike.congr_fun h2 s
  simp only [pow_two, MonoidHom.mul_apply, MonoidHom.one_apply] at h
  exact inv_eq_of_mul_eq_one_right h

theorem val_dt (W : R2 Ω l) (s : G ℚ Ω) : ((dt W s : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
  simp [dt, mat]

theorem eps_eq (s : G ℚ Ω) :
    eps l s = algebraMap ℤ_[l] (PadicAlgCl l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  rfl

theorem eps_mem (c : Coef l) (s : G ℚ Ω) : eps l s ∈ c.O := by
  rw [eps_eq]; exact c.O.algebraMap_mem _

theorem dual_representation_integral_entries (c : Coef l) (W : R2 Ω l) (hW : ∀ s i j, mat W s i j ∈ c.O) (h2 : dt W ^ 2 = 1) :
    ∀ s i j, mat (dual1 W) s i j ∈ c.O := by
  intro s i j
  rw [mat_dual1, dt_inv W h2, Matrix.smul_apply, smul_eq_mul, val_dt]
  exact mul_mem (mul_mem (eps_mem c s) (det_mem c (hW s))) (hW s i j)

theorem cont_dual1 (W : R2 Ω l) (hW : Continuous W) (h2 : dt W ^ 2 = 1) : Continuous (dual1 W) := by
  have he : Continuous (fun s : G ℚ Ω => eps l s) := by
    have hz : Continuous (fun s : G ℚ Ω => ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])) :=
      Units.continuous_val.comp (continuous_cycZ ℚ Ω l)
    exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp (continuous_subtype_val.comp hz)
  have hdv : Continuous (fun s => ((dt W s : (Qbar l)ˣ) : Qbar l)) := by
    simp only [val_dt]
    exact (Units.continuous_val.comp hW).matrix_det
  have hm : Continuous (fun s => mat (dual1 W) s) := by
    have : (fun s => mat (dual1 W) s) = fun s => (eps l s * ((dt W s : (Qbar l)ˣ) : Qbar l)) • mat W s := by
      funext s; rw [mat_dual1, dt_inv W h2]
    rw [this]; exact (he.mul hdv).smul (Units.continuous_val.comp hW)
  refine Units.continuous_iff.2 ⟨hm, ?_⟩
  have : (fun s => (((dual1 W s)⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))) =
      fun s => mat (dual1 W) s⁻¹ := by
    funext s; simp [mat, map_inv]
  rw [this]; exact hm.comp continuous_inv

variable [IsAlgClosure ℚ Ω]

theorem cycZ_one {A : ValuationSubring Ω} {v : Pl} (hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) : cycZ ℚ Ω l σ = 1 :=
  Units.ext (PadicInt.ext_of_toZModPow.mp fun n => by
    rw [cycZ_toZModPow_eq hl h (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
    simp)

theorem unr_dual1 (S : Finset Pl) (W : R2 Ω l) (hS : ContainsAbove S l)
    (hunr : ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) :
    ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ (dual1 W).ker := by
  intro w hw B hB s hs
  have h1 : W s = 1 := hunr w hw B hB hs
  have hl : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => hw (hS w h)
  have h2 : cycZ ℚ Ω l s = 1 := cycZ_one hl hB hs
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [dual1, tw_val]
  simp [h1, h2, dt, cycBar]

end Twist

section Main

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem isIntegralCocycleOneModPow_of_integral_cocycle (c : Coef l) (n : ℕ) (W : R2 Ω l) (H : Subgroup (G ℚ Ω)) {a : G ℚ Ω → Fin 2 → Qbar l}
    (ha : a ∈ Z1 (Loc.colRep W)) (hint : ∀ s i, a s i ∈ c.O) : Coc1 c n W H a := by
  refine ⟨ha.1.continuousOn, hint, fun s _ t _ => cv_of_eq n ?_⟩
  rw [ha.2 s t, colRep_apply]

theorem unr_smul (W : R2 Ω l) (a : Qbar l) {y : G ℚ Ω → Fin 2 → Qbar l} (h : Unr W y) :
    Unr W (fun s => a • y s) := by
  intro w hw
  obtain ⟨B, hB, x, hx⟩ := h w hw
  exact ⟨B, hB, a • x, fun s hs => by show a • y s = _; rw [hx s hs, Matrix.mulVec_smul, smul_sub]⟩

theorem trivial_cyclotomic_le_det_one (W : R2 Ω l) : N0g W ≤ H0g W := by
  intro g hg
  rw [N0g, Subgroup.mem_inf] at hg
  rw [H0g, Subgroup.mem_inf]
  refine ⟨hg.1, ?_⟩
  have h1 : W g = 1 := hg.2
  rw [MonoidHom.mem_ker]
  simp [dt, h1]

theorem commutator_det_one_le (W : R2 Ω l) : ⁅H0g W, H0g W⁆ ≤ H0g W := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem main : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ES W A → StrZero (dual1 W) A := by
  intro hLit l _ Ω _ _ _ e S A W hN hES z hz hzU hzT
  by_contra hzB
  obtain ⟨c, y, S', hWc, hy, hyc, hyU, hyG, hT⟩ := hES

  obtain ⟨c1, k1, hcc1, hy1int, hy1loc, -, -⟩ := GlobalTheory.T.galois_cocycle_integral_after_scaling l Ω S W c y hN.cont hWc hN.unr hy hyU A
  have hWc1 : ∀ s i j, mat W s i j ∈ c1.O := fun s i j => hcc1 (hWc s i j)
  obtain ⟨c2, k2, hc12, hz2int, hz2loc, hz2triv, -⟩ := GlobalTheory.T.galois_cocycle_integral_after_scaling l Ω S (dual1 W) c1 z
    (cont_dual1 W hN.cont hN.det2) (dual_representation_integral_entries c1 W hWc1 hN.det2) (unr_dual1 S W hN.above hN.unr) hz hzU A
  have hWc2 : ∀ s i j, mat W s i j ∈ c2.O := fun s i j => hc12 (hWc1 s i j)
  set a1 : Qbar l := ((l : ℕ) : Qbar l) ^ k1 with ha1def
  set a2 : Qbar l := ((l : ℕ) : Qbar l) ^ k2 with ha2def
  have hl0 : ((l : ℕ) : Qbar l) ≠ 0 := by
    intro h0
    have := norm_l_lt_one (l := l)
    have h1 : ‖((l : ℕ) : Qbar l)‖ = 0 := by rw [h0, norm_zero]
    have h2 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := (map_natCast _ _).symm
    rw [h2, norm_algebraMap', Padic.norm_p] at h1
    have : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast (Fact.out : l.Prime).pos)
    linarith
  have ha1 : a1 ≠ 0 := pow_ne_zero _ hl0
  have ha2 : a2 ≠ 0 := pow_ne_zero _ hl0
  set y' : G ℚ Ω → Fin 2 → Qbar l := fun s => a1 • y s with hy'def
  set z' : G ℚ Ω → Fin 2 → Qbar l := fun s => a2 • z s with hz'def
  have hy' : y' ∈ Z1 (Loc.colRep W) := (Z1 (Loc.colRep W)).smul_mem a1 hy
  have hz' : z' ∈ Z1 (Loc.colRep (dual1 W)) := (Z1 (Loc.colRep (dual1 W))).smul_mem a2 hz
  have hy'int : ∀ s i, y' s i ∈ c2.O := fun s i => hc12 (hy1int s i)
  have hz'int : ∀ s i, z' s i ∈ c2.O := fun s i => hz2int s i
  have hy'U : Unr W y' := unr_smul W a1 hyU
  have hz'U : Unr (dual1 W) z' := unr_smul (dual1 W) a2 hzU
  have ha1O : a1 ∈ c2.O := pow_mem (natCast_mem _ _) _
  have hT' : ∀ n : ℕ, 1 ≤ n → ∀ w : Pl, w ∉ S' → l ^ n ∣ normV w - 1 → ∀ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)),
      KillsMu (normV w) ψ → Function.Surjective ψ → Tame c2 W y' n w ψ :=
    fun n hn w hw hd ψ hK hs => GlobalTheory.T.eulerSystemTameClass_scale_enlarge_coefficients l Ω W c c2 y n w ψ a1 (le_trans hcc1 hc12) ha1O (hT n hn w hw hd ψ hK hs)
  obtain ⟨xA, hxA, hxAe⟩ := hz2triv hzT

  have hloc : ∀ n : ℕ, ∀ v ∈ S, ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧
      Cob2 c2 n (Dec (F := ℚ) B) (cup W y' z') := by
    intro n v _
    by_cases hlv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
    · obtain ⟨v0, hAv0, hlv0⟩ := hN.atL
      have hv : v = v0 := place_eq (Fact.out : l.Prime) hlv hlv0
      subst hv
      refine ⟨A, hAv0, ?_⟩
      exact GlobalTheory.T.cup_product_coboundary_mod l Ω c2 n W (Dec (F := ℚ) A) y' z' hN.cont hWc2 hN.det2
        (isIntegralCocycleOneModPow_of_integral_cocycle c2 n W _ hy' hy'int) (isIntegralCocycleOneModPow_of_integral_cocycle c2 n (dual1 W) _ hz' hz'int)
        (Or.inr ⟨xA, hxA, fun s hs => cv_of_eq n (hxAe s hs)⟩)
    · obtain ⟨B, hB, -⟩ := hyU v hlv
      obtain ⟨x1, hx1, hx1e⟩ := hy1loc v hlv B hB
      obtain ⟨x2, hx2, hx2e⟩ := hz2loc v hlv B hB
      exact ⟨B, hB, GlobalTheory.T.cupProduct_unramifiedClasses_vanishes hLit l Ω c2 n W v B y' z' hN.cont hWc2 hN.det2 hB hlv
        (isIntegralCocycleOneModPow_of_integral_cocycle c2 n W _ hy' hy'int) (isIntegralCocycleOneModPow_of_integral_cocycle c2 n (dual1 W) _ hz' hz'int)
        ⟨x1, fun i => hc12 (hx1 i), fun s hs => cv_of_eq n (hx1e s hs)⟩
        ⟨x2, hx2, fun s hs => cv_of_eq n (hx2e s hs)⟩⟩

  have hyN : ∃ g ∈ N0g W, y' g ≠ 0 := by
    by_contra h
    push_neg at h
    apply hyG
    refine GlobalTheory.T.greenbergOrdinary_of_vanishing_on_cycloKernel l Ω e S A W hN y hy fun g hg => ?_
    have := h g hg
    exact (smul_eq_zero.mp this).resolve_left ha1
  have hzN : ∃ g ∈ N0g W, z' g ≠ 0 := by
    by_contra h
    push_neg at h
    apply hzB
    refine GlobalTheory.T.tateDual_cocycle_coboundary_of_vanish_on_fixing l Ω e S A W hN z hz fun g hg => ?_
    have := h g hg
    exact (smul_eq_zero.mp this).resolve_left ha2
  obtain ⟨g, hg, h, hh, hne⟩ := GlobalTheory.T.cocycle_pair_alternating_ne_on_cycloKernel l Ω e S A W hN y' hy' z' hz' hyN hzN
  obtain ⟨φ, hφ, hde⟩ := GlobalTheory.T.exists_commutator_det_nonzero l Ω e S A W hN
  have hφH : φ ∈ H0g W := commutator_det_one_le W hφ
  have hgW : W g = 1 := (Subgroup.mem_inf.mp hg).2
  have hhW : W h = 1 := (Subgroup.mem_inf.mp hh).2
  have hcomm : g * h * g⁻¹ * h⁻¹ ∈ ⁅H0g W, H0g W⁆ := by
    have := Subgroup.commutator_mem_commutator (trivial_cyclotomic_le_det_one W hg) (trivial_cyclotomic_le_det_one W hh)
    rwa [commutatorElement_def] at this
  have hφ1 : φ * (g * h * g⁻¹ * h⁻¹) ∈ ⁅H0g W, H0g W⁆ := mul_mem hφ hcomm
  have hmat : mat W (φ * (g * h * g⁻¹ * h⁻¹)) = mat W φ := by
    simp [mat, map_mul, map_inv, hgW, hhW]
  set de : Qbar l := (mat W φ - 1).det with hdedef
  set de' : Qbar l := om (y' h) (z' g) - om (y' g) (z' h) with hde'def
  have hde' : de' ≠ 0 := sub_ne_zero.mpr hne
  have hdeO : ‖de‖ ≤ 1 := norm_le_one_of_mem c2 (det_mem c2 (sub_one_mem c2 (hWc2 φ)))

  have key : ∀ n : ℕ, 1 ≤ n → ‖de ^ 2 * de'‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
    intro n hn
    obtain ⟨u, hu, huint, huS, hucup⟩ := GlobalTheory.T.local_cochains_glue_global hLit l Ω c2 n S (cup W y' z') hN.l_odd hN.above
      (GlobalTheory.T.cupProductDualTwist_isTwoCocycle_unramified l Ω c2 n S W y' z' hN.cont hWc2 hN.det2 hN.above hN.unr hy' hz' hy'int hz'int hy'U hz'U)
      (hloc n)
    have hr := GlobalTheory.T.cohomology_unramified_lift hLit l Ω e S A W hN c2 y' z' u S' n hn hWc2 hy' hz' hy'int hz'int hy'U hz2loc
      ⟨xA, hxA, hxAe⟩ (hT' n hn) hu huint huS hucup
    have hc := GlobalTheory.T.height_commutator_invariance l Ω n c2 W y' z' u hWc2 hy' hz' hucup φ hφH g hg h hh
    have h0 := hr φ hφ
    have h1 := hr _ hφ1
    rw [hmat] at h1
    unfold Cg at h0 h1 hc
    rw [sub_zero] at h0 h1
    set L := ‖((l : ℕ) : Qbar l) ^ n‖
    set t1 := ht W y' z' u (φ * (g * h * g⁻¹ * h⁻¹))
    set t0 := ht W y' z' u φ
    have e1 : de ^ 2 * de' = de * (de * de' - (t1 - t0)) + de * t1 - de * t0 := by ring
    have b1 : ‖de * (de * de' - (t1 - t0))‖ ≤ L := by
      rw [norm_mul, norm_sub_rev]
      calc ‖de‖ * ‖t1 - t0 - de * de'‖ ≤ 1 * L := by
            gcongr
        _ = L := one_mul L
    rw [e1]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rw [norm_neg]; exact h0))
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le b1 h1)
  have hx0 : de ^ 2 * de' ≠ 0 := mul_ne_zero (pow_ne_zero 2 hde) hde'
  have hpos : 0 < ‖de ^ 2 * de'‖ := norm_pos_iff.mpr hx0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (norm_l_lt_one (l := l))
  have hk := key (n + 1) (by omega)
  rw [norm_pow] at hk
  have hmono : ‖((l : ℕ) : Qbar l)‖ ^ (n + 1) ≤ ‖((l : ℕ) : Qbar l)‖ ^ n :=
    pow_le_pow_of_le_one (norm_nonneg _) (norm_l_lt_one (l := l)).le (by omega)
  linarith

end Main

end GlobalTheory.Ord2.StrictKill
end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strict_vanishing_dual_of_literature : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ES W A → StrZero (dual1 W) A := by
  atlas_forward_decl GlobalTheory.Ord2.StrictKill.main
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem localGaloisCohomology_of_galoisCohomology (h : GlobalTheory.Mem.LiteralAutomorphy.LitCoh) : Loc.LocalPublishedTheorems :=
  ⟨h.lfK, h.ltK, h.leK, h.lf, h.lt, h.le, h.bk⟩

theorem es_vanish : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ES W A → BlochKatoSelmerVanishes l (Loc.colRep W) := by
  intro hLit l _ Ω _ _ _ e S A W hNf hES c hc hBK
  have hStr : StrZero (dual1 W) A := GlobalTheory.T.strict_vanishing_dual_of_literature hLit l Ω e S A W hNf hES
  have hGrD : GrZero (dual1 W) A := GlobalTheory.T.ordinarySelmer_dual_vanishes_of_strict hLit l Ω e S A W hNf hES hStr
  have hGr : GrZero W A := GlobalTheory.T.ordinarySelmer_vanishes_of_dual_vanishes hLit l Ω e S A W hNf hGrD
  obtain ⟨hU, hG⟩ := GlobalTheory.T.blochKato_cocycle_unramified_and_greenbergOrdinary (localGaloisCohomology_of_galoisCohomology hLit) l Ω e S A W hNf c hc hBK
  exact hGr c hc hU hG

end GlobalTheory.Ord2
end
