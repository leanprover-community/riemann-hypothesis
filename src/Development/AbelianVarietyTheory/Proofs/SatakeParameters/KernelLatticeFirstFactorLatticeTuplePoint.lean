import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocSpCompanEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLatDlOfIsOrthCo
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatSLatAdIff

section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

theorem smul_dualSet_latAd_mem {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E)
    (hco : ∃ co, IsOrthCo (sp.cm.sig : E →+* E) J co) (T : ℕ) (Lb : Submodule (𝓞 E) (Fin N → E)) (hT : 0 < T)
    (hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat Lb)
    (hdual : ∀ z ∈ dualSet (sp.cm.sig : E →+* E) J Lb, (T : E) • z ∈ Lb)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hy : y ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F))
    (z : Fin N → E) (hz : z ∈ dualSet (sp.cm.sig : E →+* E) J (latAd y Lb)) :
    (T : E) • z ∈ latAd y Lb := by
  have hlat : latAd y Lb = Formalism.UG.CS.globLat y Lb := Submodule.span_eq (Formalism.UG.CS.globLat y Lb)
  set a : 𝓞 E := (T : 𝓞 E) with ha
  have ha0 : a ≠ 0 := by
    rw [ha]; exact_mod_cast hT.ne'
  have hsm : ∀ w : Fin N → E, a • w = (T : E) • w := by
    intro w
    rw [← algebraMap_smul E a w, ha, map_natCast]

  have hdl : ∀ w ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb, a • w ∈ Lb := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => rw [hsm]; exact hdual w hw
    | zero => rw [smul_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [smul_add]; exact add_mem hu hv
    | smul c w _ hw => rw [smul_comm]; exact Lb.smul_mem c hw
  have hle : Ideal.span {a} • Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb ≤ Lb := by
    refine Submodule.smul_le.2 fun r hr w hw => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    exact Lb.smul_mem c (hdl w hw)

  have hz' : z ∈ Formalism.UG.CS.globLat y (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb) := by
    rw [Formalism.L2.GlobalTheoryTheory.Comp.glob_dl sp.cm.sig J (GlobalTheory.isLat_dl_of_isOrthCo sp J hco) hLb y hy]
    rw [hlat] at hz
    exact Submodule.subset_span hz
  have h1 : a • z ∈ Ideal.span {a} • Formalism.UG.CS.globLat y (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb) :=
    Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hz'
  have h2 := Formalism.L2.GlobalTheoryTheory.Comp.glob_mono y hle
    (Formalism.L2.GlobalTheoryTheory.Comp.smul_glob_le _ a y h1)
  rw [hlat, ← hsm]
  exact h2

end GlobalTheory
end
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem ph_tensInt_onto : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G), SplAlg A → ∀ v, (∀ s ∈ intV E (A.pl v).1, A.ph v s ∈ (A.pl v).1.adicCompletionIntegers F) ∧ ∀ x ∈ (A.pl v).1.adicCompletionIntegers F, ∃ s ∈ intV E (A.pl v).1, A.ph v s = x := by
  intro F E _ _ _ _ _ n p G A hA v
  have h1 : ∀ y : (A.pl v).1.adicCompletion F, A.ph v ((1 : E) ⊗ₜ[F] y) = y := by
    intro y
    show ((A.spl v) ((1 : E) ⊗ₜ[F] y)).1 = y
    rw [hA v y]
  refine ⟨?_, ?_⟩
  · intro s hs
    have hle : intV E (A.pl v).1 ≤ ((A.pl v).1.adicCompletionIntegers F).toSubring.comap (A.ph v) := by
      refine (Subring.closure_le).2 ?_
      rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
      · obtain ⟨r, rfl⟩ := hx
        show A.ph v ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F)) ∈ (A.pl v).1.adicCompletionIntegers F
        have h0 : IsIntegral ℤ (algebraMap (𝓞 E) E r) := (RingOfIntegers.isIntegral r).map (IsScalarTower.toAlgHom ℤ (𝓞 E) E)
        obtain ⟨q, hq, hev⟩ := h0
        let f : E →+* (A.pl v).1.adicCompletion F := (A.ph v).comp (Algebra.TensorProduct.includeLeftRingHom)
        have hf : f (algebraMap (𝓞 E) E r) = A.ph v ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F)) := rfl
        have hint' : IsIntegral ((A.pl v).1.adicCompletionIntegers F) (A.ph v ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F))) := by
          refine ⟨q.map (Int.castRingHom _), hq.map _, ?_⟩
          rw [Polynomial.eval₂_map, ← hf]
          have := congrArg f hev
          rw [map_zero, Polynomial.hom_eval₂] at this
          have e : (algebraMap ((A.pl v).1.adicCompletionIntegers F) ((A.pl v).1.adicCompletion F)).comp
              (Int.castRingHom ((A.pl v).1.adicCompletionIntegers F)) = f.comp (algebraMap ℤ E) := RingHom.ext_int _ _
          rw [e]
          exact this
        obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
        rw [← hz]
        exact z.2
      · show A.ph v ((1 : E) ⊗ₜ[F] y) ∈ (A.pl v).1.adicCompletionIntegers F
        rw [h1]
        exact hy
    exact hle hs
  · intro x hx
    refine ⟨(1 : E) ⊗ₜ[F] x, ?_, h1 x⟩
    exact Subring.subset_closure (Or.inr ⟨⟨x, hx⟩, rfl⟩)

end GlobalTheory.TwV
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_first_factor_integers_onto_local_integers : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G), SplAlg A → ∀ v, (∀ s ∈ intV E (A.pl v).1, A.ph v s ∈ (A.pl v).1.adicCompletionIntegers F) ∧ ∀ x ∈ (A.pl v).1.adicCompletionIntegers F, ∃ s ∈ intV E (A.pl v).1, A.ph v s = x := by
  atlas_forward_decl GlobalTheory.TwV.ph_tensInt_onto
end

section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem locSp_eq_image : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G), SplAlg A → LocInt A → ∀ v (Λ : Submodule (𝓞 E) (Fin n → E)) (z' : Fin n → G.P.Qq v), z' ∈ locSp (G.P.W v) (A.iw v) Λ ↔ ∃ z ∈ latS (F := F) ((A.pl v).1.adicCompletion F) (intV E (A.pl v).1) Λ, ∀ k, (A.eQ v).symm (A.ph v (z k)) = z' k := by
  intro F E _ _ _ _ _ n p G A hS hI v Λ z'
  have hph := GlobalTheory.T.tensor_first_factor_integers_onto_local_integers A hS v
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨fun k => inclE (F := F) _ (x k), Submodule.subset_span ⟨x, hx, rfl⟩, fun k => ?_⟩
      rfl
    | zero => exact ⟨0, Submodule.zero_mem _, fun k => by simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨z₁, hz₁, e₁⟩ := h₁
      obtain ⟨z₂, hz₂, e₂⟩ := h₂
      refine ⟨z₁ + z₂, Submodule.add_mem _ hz₁ hz₂, fun k => ?_⟩
      simp [e₁ k, e₂ k]
    | smul w y _ h =>
      obtain ⟨z, hz, e⟩ := h
      have hw : A.eQ v (algebraMap (G.P.W v) (G.P.Qq v) w) ∈ (A.pl v).1.adicCompletionIntegers F :=
        (hI v _).1 ⟨w, rfl⟩
      obtain ⟨s, hs, hse⟩ := hph.2 _ hw
      refine ⟨(⟨s, hs⟩ : intV E (A.pl v).1) • z, Submodule.smul_mem _ _ hz, fun k => ?_⟩
      show (A.eQ v).symm (A.ph v (s * z k)) = (w • y) k
      rw [map_mul, hse, map_mul, e k, RingEquiv.symm_apply_apply, Pi.smul_apply, Algebra.smul_def]
  · rintro ⟨z, hz, hzz⟩
    have key : ∀ z ∈ latS (F := F) ((A.pl v).1.adicCompletion F) (intV E (A.pl v).1) Λ,
        (fun k => (A.eQ v).symm (A.ph v (z k))) ∈ locSp (G.P.W v) (A.iw v) Λ := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero =>
        have h0 := Submodule.zero_mem (locSp (G.P.W v) (A.iw v) Λ)
        convert h0 using 1
        funext k
        simp
      | add y₁ y₂ _ _ h₁ h₂ =>
        have := Submodule.add_mem _ h₁ h₂
        simpa [Pi.add_def] using this
      | smul s y _ h =>
        obtain ⟨w, hw⟩ := (hI v ((A.eQ v).symm (A.ph v s))).2 (by simpa using hph.1 s.1 s.2)
        have := Submodule.smul_mem _ w h
        convert this using 1
        funext k
        show (A.eQ v).symm (A.ph v (s.1 * y k)) = _
        rw [Pi.smul_apply, Algebra.smul_def, hw, map_mul, map_mul]
    have := key z hz
    convert this using 1
    funext k
    exact (hzz k).symm

end GlobalTheory.TwV
end

section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem latAdLoc_of : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G) (Lb : Submodule (𝓞 E) (Fin n → E)), SplAlg A → LocInt A → Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin n → E)) = ⊤ → LatAdLoc A Lb := by
  intro F E _ _ _ _ _ n p G A Lb hS hI hfin hspan y v
  letI : StarRing E := starRingOfComm
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F) :=
    Units.val (bc (prV (E := E) (A.pl v).1) y : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) with hY
  set f : E ⊗[F] (A.pl v).1.adicCompletion F →+* G.P.Qq v :=
    ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v).comp (A.ph v) with hf
  have hfac : ((facQ A v y : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) = Y.map f := by
    rw [hY]; ext i j; rfl
  have hmv : ∀ u : Fin n → E ⊗[F] (A.pl v).1.adicCompletion F,
      (fun k => (A.eQ v).symm (A.ph v ((Y *ᵥ u) k))) =
        ((facQ A v y : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) *ᵥ
          (fun k => (A.eQ v).symm (A.ph v (u k))) := by
    intro u
    rw [hfac]
    funext k
    exact RingHom.map_mulVec f Y u k
  ext z'
  rw [locSp_eq_image A hS hI v, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzz⟩
    rw [GlobalTheory.LocCarry.mem_latS_latAd_iff y Lb hfin hspan] at hz
    set u := Units.val ((bc (prV (E := E) (A.pl v).1) y)⁻¹ : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) *ᵥ z with hu
    refine ⟨fun k => (A.eQ v).symm (A.ph v (u k)), (locSp_eq_image A hS hI v Lb _).2 ⟨u, hz, fun k => rfl⟩, ?_⟩
    have hzu : z = Y *ᵥ u := by
      rw [hu, hY, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    show (facQ A v y : Matrix (Fin n) (Fin n) (G.P.Qq v)) *ᵥ _ = z'
    rw [← hmv, ← hzu]
    funext k
    exact hzz k
  · rintro ⟨w, hw, hwz⟩
    obtain ⟨u, hu, huw⟩ := (locSp_eq_image A hS hI v Lb w).1 hw
    refine ⟨Y *ᵥ u, ?_, ?_⟩
    · have hback : Units.val ((bc (prV (E := E) (A.pl v).1) y)⁻¹ : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) *ᵥ
          (Y *ᵥ u) = u := by
        rw [hY, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [GlobalTheory.LocCarry.mem_latS_latAd_iff y Lb hfin hspan]
      rw [hback]
      exact hu
    · intro k
      have hw' : w = fun k => (A.eQ v).symm (A.ph v (u k)) := funext fun k => (huw k).symm
      subst hwz
      subst hw'
      exact congrFun (hmv u) k

end GlobalTheory.TwV
end

section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.FacQPt

set_option maxHeartbeats 400000 in

theorem facQ_isPt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G) (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (y : GL (Fin n) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))) : A.IsPt i g y → ∀ v, facQ A v y = bc (A.iw v) A.B * castGL A.rk (G.P.Qq v) (g v) * (bc (A.iw v) A.B)⁻¹ := by
  intro h v

  have hv := h.2 v
  have hB : bc ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v) (bc (A.phE v) A.B) = bc (A.iw v) A.B := by
    ext a b
    rfl
  have hg : bc ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v)
      (bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) (g v))) =
      castGL A.rk (G.P.Qq v) (g v) := by
    apply Units.ext
    ext a b
    simp [Formalism.UG.bc]
  unfold facQ
  rw [hv, map_mul, map_mul, map_inv, hB, hg]

end GlobalTheory.TwV.FacQPt

end
end

section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.SpanPt

theorem colSpan_map {R K : Type*} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (M X : Matrix (Fin k) (Fin k) K) :
    (colSpan R X).map ((M.mulVecLin).restrictScalars R) = colSpan R (M * X) := by
  unfold colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1

set_option maxHeartbeats 400000 in

theorem locSp_latAd_isPt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G) (Lb : Submodule (𝓞 E) (Fin n → E)), LatAdLoc A Lb → LbAtB A Lb → ∀ (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (y : GL (Fin n) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))), A.IsPt i g y → ∀ v, locSp (G.P.W v) (A.iw v) (latAd y Lb) = colSpan (G.P.W v) (((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) * (castGL A.rk (G.P.Qq v) (g v) : Matrix (Fin n) (Fin n) (G.P.Qq v))) := by
  intro F E _ _ _ _ _ n p G A Lb hA hB i g y hy v
  rw [hA y v, hB v, colSpan_map, GlobalTheory.TwV.FacQPt.facQ_isPt A i g y hy v]
  simp only [Units.val_mul, Matrix.mul_assoc]
  rw [← Units.val_mul (bc (A.iw v) A.B)⁻¹, inv_mul_cancel, Units.val_one, Matrix.mul_one]

end GlobalTheory.TwV.SpanPt

end
end

section
namespace GlobalTheory.TwV

open NumberField
open scoped Matrix

theorem map_apply_eq_mulVec {E K : Type} [Field E] [Field K] (ρ : E →+* K) {N n : ℕ}
    (f : (Fin N → E) →ₗ[E] (Fin n → E)) (x : Fin N → E) :
    (fun k => ρ (f x k)) = ((LinearMap.toMatrix' f).map ρ) *ᵥ (fun k => ρ (x k)) := by
  funext k
  rw [← LinearMap.toMatrix'_mulVec f x]
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem locSp_map {E : Type} [Field E] [NumberField E] (W K : Type) [CommRing W] [Field K] [Algebra W K]
    (ρ : E →+* K) {N n : ℕ} (f : (Fin N → E) →ₗ[E] (Fin n → E)) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    locSp W ρ (Λ.map (f.restrictScalars (𝓞 E))) =
      (locSp W ρ Λ).map ((((LinearMap.toMatrix' f).map ρ).mulVecLin).restrictScalars W) := by
  unfold locSp
  rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  exact map_apply_eq_mulVec ρ f x

end GlobalTheory.TwV
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TwV.KerSp

theorem locSp_latK_isPt : ∀ {D : D7} {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {p : ℕ} {G : GAtP p} (A : LocAt D.host.F D.host.E (D.R.N i) G) (a : 𝓞 D.host.E), (∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) co) → SplAlg A → LocInt A → LbAtB A lev.Lb → 0 < T → ∀ (c : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), A.IsPt c g x.1 → ∀ v, IsUnit (T : G.P.W v) → locSp (G.P.W v) (A.iw v) (latK D.sp (gramN D i hi) a x.1 lev.Lb) = colSpan (G.P.W v) ((LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi)).toLinearMap * A.B.1).map (A.iw v) * (castGL A.rk (G.P.Qq v) (g v) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (G.P.Qq v))) := by
  intro D i hi T bad lev p G A a hco hS hI hB hT c g x hx v hTv
  have hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat lev.Lb := ⟨lev.Lb_fin, lev.Lb_span⟩
  have hdual := GlobalTheory.smul_dualSet_latAd_mem D.sp (gramN D i hi) hco T lev.Lb hT hLb lev.Lb_dual x.1 x.2
  have hLA : LatAdLoc A lev.Lb := GlobalTheory.TwV.latAdLoc_of A lev.Lb hS hI lev.Lb_fin lev.Lb_span
  unfold Formalism.MainNotions.G.KAat.latK Formalism.L2.PairingIndexBounds.F.toStd
  rw [GlobalTheory.TwV.locSp_map, GlobalTheory.TwV.CompSp.locSp_compan_eq D.sp (G.P.W v) (G.P.Qq v) (A.iw v) (gramN D i hi) a T _ hTv hdual,
    GlobalTheory.TwV.SpanPt.locSp_latAd_isPt A lev.Lb hLA hB c g x.1 hx v, GlobalTheory.TwV.SpanPt.colSpan_map]
  rw [Matrix.map_mul, Matrix.mul_assoc]
  rfl

end GlobalTheory.TwV.KerSp
end
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelLatticeFirstFactor_latticeTuplePoint : ∀ {D : D7} {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {p : ℕ} {G : GAtP p} (A : LocAt D.host.F D.host.E (D.R.N i) G) (a : 𝓞 D.host.E), (∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) co) → SplAlg A → LocInt A → LbAtB A lev.Lb → 0 < T → ∀ (c : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), A.IsPt c g x.1 → ∀ v, IsUnit (T : G.P.W v) → locSp (G.P.W v) (A.iw v) (latK D.sp (gramN D i hi) a x.1 lev.Lb) = colSpan (G.P.W v) ((LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi)).toLinearMap * A.B.1).map (A.iw v) * (castGL A.rk (G.P.Qq v) (g v) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (G.P.Qq v))) := by
  atlas_forward_decl GlobalTheory.TwV.KerSp.locSp_latK_isPt
end
