import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CardKPNeZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldOfRay

section
open NumberField IsDedekindDomain GlobalTheory.Mem

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RayOnto

theorem containsRayField_comp {K L L' : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field L'] [NumberField L']
    (φ : K →+* L) (τ : L →+* L') (n : ℕ) (h : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (τ.comp φ) n := by
  intro P hP
  letI : Algebra L L' := τ.toAlgebra
  let Q : HeightOneSpectrum (𝓞 L) := P.under (𝓞 L)
  have hQ : Q.asIdeal = P.asIdeal.comap (RingOfIntegers.mapRingHom τ) := rfl
  haveI hPo : P.asIdeal.LiesOver Q.asIdeal := ⟨rfl⟩
  have hn : ((n : ℕ) : 𝓞 L) ∉ Q.asIdeal := fun h' => hP (by
    rw [hQ, Ideal.mem_comap, map_natCast] at h'
    exact h')
  obtain ⟨f, α, h1, h2, h3⟩ := h Q hn
  have hf := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal Q.asIdeal Q.isPrime Q.ne_bot
  have hcm : P.asIdeal.comap (RingOfIntegers.mapRingHom (τ.comp φ)) =
      Q.asIdeal.comap (RingOfIntegers.mapRingHom φ) := by
    ext x
    rfl
  rw [hcm]
  refine ⟨f * Q.asIdeal.inertiaDeg' P.asIdeal, α ^ Q.asIdeal.inertiaDeg' P.asIdeal, ?_, ?_, ?_⟩
  · rw [hf, h1, ← pow_mul]
  · rw [pow_mul, h2, Ideal.span_singleton_pow]
  · have := sub_dvd_pow_sub_pow α 1 (Q.asIdeal.inertiaDeg' P.asIdeal)
    rw [one_pow] at this
    exact dvd_trans h3 this

theorem exists_finset_containsRayField : GlobalTheory.NT.RayField → ∀ (P : Pre) (M : ℕ), M ≠ 0 → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ (L : Type) [Field L] [NumberField L] (σ : L →+* ℂ) (φ : P.host.K →+* L), σ.comp φ = P.host.φ₀.comp (algebraMap P.host.K P.host.E) → (∀ z ∈ S, ∃ x, σ x = z) → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ M := by
  intro hR P M hM
  let φK : P.host.K →+* ℂ := P.host.φ₀.comp (algebraMap P.host.K P.host.E)
  obtain ⟨Rf, hRf⟩ := GlobalTheory.Mem.Fld.exists_isRayFieldIn φK hR (GlobalTheory.Mem.Fld.natIdeal_ne_bot (E := P.host.K) hM)
  haveI : NumberField Rf := hRf.numberField
  let b := Module.finBasis ℚ Rf
  refine ⟨Finset.univ.image (fun i => (b i : ℂ)), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    have h : IsAlgebraic ℚ (b i) := Algebra.IsAlgebraic.isAlgebraic _
    exact h.algHom Rf.val
  · intro L _ _ σ φ hσφ hS
    obtain ⟨hm, hNF, hray⟩ := hRf
    letI := GlobalTheory.Mem.Fld.algOf φK Rf hm
    obtain ⟨hab, hun, -, hart⟩ := hray
    haveI : IsGalois P.host.K Rf := hab.toIsGalois
    have hc : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap P.host.K Rf) M :=
      GlobalTheory.FieldSize.RayNorm.containsRayField_of_ray (K := P.host.K) (L := Rf) M hun
        (fun I hI hc hχ => (hart I hI hc).1 hχ)
    have hle : Rf ≤ σ.toRatAlgHom.fieldRange := by
      intro z hz
      have hsum := congrArg Subtype.val (b.sum_repr ⟨z, hz⟩)
      rw [IntermediateField.coe_sum] at hsum
      simp only [IntermediateField.coe_smul] at hsum
      rw [← hsum]
      refine sum_mem fun i _ => IntermediateField.smul_mem _ ?_
      obtain ⟨y, hy⟩ := hS (b i) (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
      exact ⟨y, hy⟩
    let e : L ≃ₐ[ℚ] σ.toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField σ.toRatAlgHom
    let τ : Rf →+* L := (e.symm : σ.toRatAlgHom.fieldRange →+* L).comp
      (IntermediateField.inclusion hle : Rf →+* σ.toRatAlgHom.fieldRange)
    have key : ∀ w, σ (e.symm w) = (w : ℂ) := fun w => by
      conv_rhs => rw [← e.apply_symm_apply w]
      rfl
    have hτ : τ.comp (algebraMap P.host.K Rf) = φ := by
      ext x
      apply σ.injective
      have h1 : σ (φ x) = φK x := RingHom.congr_fun hσφ x
      rw [h1]
      exact key _
    rw [← hτ]
    exact containsRayField_comp _ τ M hc

end GlobalTheory.RayOnto
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Plug.RayLarge

open Formalism.L2.Host

def raySet (hR : GlobalTheory.NT.RayField) (P : Pre) (M : ℕ) : Finset ℂ :=
  if h : M ≠ 0 then Classical.choose (GlobalTheory.RayOnto.exists_finset_containsRayField hR P M h) else ∅

theorem raySet_alg (hR : GlobalTheory.NT.RayField) (P : Pre) (M : ℕ) : ∀ z ∈ raySet hR P M, IsAlgebraic ℚ z := by
  unfold raySet
  split_ifs with h
  · exact (Classical.choose_spec (GlobalTheory.RayOnto.exists_finset_containsRayField hR P M h)).1
  · simp

def levels (P : Pre) (f : Fr P) (Ξ : Set (HChar P.host.E)) : Finset ℕ :=
  Classical.choose (GlobalTheory.Plug.TwistLevels.levels_bounded P f Ξ)

def raySets (hR : GlobalTheory.NT.RayField) (P : Pre) (f : Fr P) (Ξ : Set (HChar P.host.E)) : Finset ℂ :=
  (levels P f Ξ).biUnion (raySet hR P)

theorem raySets_alg (hR : GlobalTheory.NT.RayField) (P : Pre) (f : Fr P) (Ξ : Set (HChar P.host.E)) :
    ∀ z ∈ raySets hR P f Ξ, IsAlgebraic ℚ z := by
  intro z hz
  obtain ⟨M, -, hz⟩ := Finset.mem_biUnion.1 hz
  exact raySet_alg hR P M z hz

theorem rayRec_of_has (hR : GlobalTheory.NT.RayField) {K : Ctx} (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T)
    (hH : ∀ z ∈ raySets hR X.B.toPre f (T.set f), ∃ x : X.B.LL, X.B.embLL x = z) : RayRec X.toD7 c.O.nch := by
  intro w Sp hSp
  have hspec := Classical.choose_spec (GlobalTheory.Plug.TwistLevels.levels_bounded X.B.toPre f (T.set f))
  have hM : X.B.host.g 0 * X.B.host.g 1 * ∏ q ∈ Sp.image (fun Q => Nat.card (kP Q)), q ∈ levels X.B.toPre f (T.set f) := by
    refine hspec.2 X.B rfl T HEq.rfl w Sp ?_
    intro P hP
    rcases hSp P hP with ⟨h1, -⟩ | ⟨hmu, hmem⟩
    · exact Or.inl h1
    · right
      have hw : w ∈ c.Wt := by_contra fun h => hmu (c.mu.off w h)
      rw [← (c.nch_Q w hw).1]
      exact hmem
  have hM0 := hspec.1 _ hM
  have hrs := (Classical.choose_spec (GlobalTheory.RayOnto.exists_finset_containsRayField hR X.B.toPre _ hM0)).2
  refine hrs X.B.LL X.B.embLL (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK X.toD7) ?_ ?_
  · ext x
    exact DFunLike.congr_fun X.B.embE_φ₀ _
  · intro z hz
    refine hH z (Finset.mem_biUnion.2 ⟨_, hM, ?_⟩)
    rw [raySet, dif_pos hM0]
    exact hz

end GlobalTheory.Plug.RayLarge

open GlobalTheory.Plug.RayLarge in

theorem GlobalTheory.Plug.largeBaseProperty_rayProperty : GlobalTheory.NT.RayField → ∀ (KP : ∀ B : Base, Fr B.toPre → Prop) (Q : V4.Slot), LargeBaseCondition KP Q RayPosition := by
  intro hR KP Q
  exact ⟨1, one_pos, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ =>
    ⟨0, fun K _ _ _ _ _ => ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun B f _ _ Ξ => raySets hR B f Ξ, by simp,
      fun B f _ _ Ξ => raySets_alg hR B f Ξ,
      fun B f T _ hH _ _ _ C W V S N G c _ => rayRec_of_has hR ⟨B, C, W, V, S, N, G⟩ f T c fun z hz => hH.2 z hz⟩⟩⟩⟩⟩⟩

end
end
