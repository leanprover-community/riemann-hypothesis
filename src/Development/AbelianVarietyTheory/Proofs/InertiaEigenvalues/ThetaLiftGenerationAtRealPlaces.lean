import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaIntegralSobolevContinuous
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealDerivativeFockVectorsAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorFockVacuum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFiniteHeisenbergFockVacuumThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumHeisOPureTensorO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SobolevBoundedThetaFormMatrixCoeffSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DRhoSumAndSobOLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVanishesSingleCoefficientOfKernelKills
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnDownwardThetaLiftIntegrandStatement
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RightInv
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodGA
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOfHeisDer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnDownwardThetaLiftIntegrand
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FisSelfReNonneg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SqEqOneOfFixDat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactHoweDualityIsotypicMemOfStableSubspace

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downward_theta_integral_sobolev_continuous : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) (ε : ℝ), 0 < ε → ∃ (d : ℕ) (δ : ENNReal), 0 < δ ∧ ∀ P, GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P) < δ → ‖downInt R i t y f l g - downInt R i t y (R.ptP i t P) l g‖ < ε := by
  first | exact @GlobalTheory.DownLift.Sobolev₂.downInt_sobolev_cont | exact GlobalTheory.DownLift.Sobolev₂.downInt_sobolev_cont | (intros; apply GlobalTheory.DownLift.Sobolev₂.downInt_sobolev_cont <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.VacDensity

theorem burn_span : ∀ {X ι : Type} [AddCommGroup X] [Module ℂ X] (M : Submodule ℂ X), FiniteDimensional ℂ M →
    ∀ (ρ : ι → X →ₗ[ℂ] X), (∀ i, ∀ x ∈ M, ρ i x ∈ M) → (∃ i, ∀ x ∈ M, ρ i x = x) →
    (∀ i j, ∃ (a : ℂ) (k : ι), ∀ x ∈ M, ρ i (ρ j x) = a • ρ k x) →
    (∀ W : Submodule ℂ X, W ≤ M → (∀ i, ∀ x ∈ W, ρ i x ∈ W) → W = ⊥ ∨ W = M) →
    ∀ P : X →ₗ[ℂ] X, (∀ x ∈ M, P x ∈ M) → ∃ c : ι →₀ ℂ, ∀ x ∈ M, (c.sum fun i z => z • ρ i x) = P x := by
  intro X ι _ _ M hfd ρ hst hid hmul hirr P hP
  classical
  by_cases hM : M = ⊥
  · refine ⟨0, fun x hx => ?_⟩
    rw [hM, Submodule.mem_bot] at hx
    subst hx
    simp
  let r : ι → Module.End ℂ M := fun i => (ρ i).restrict (hst i)
  have hr : ∀ i (x : M), (r i x : X) = ρ i x := fun _ _ => rfl
  let p : Submodule ℂ (Module.End ℂ M) := Submodule.span ℂ (Set.range r)
  have h1 : (1 : Module.End ℂ M) ∈ p := by
    obtain ⟨i, hi⟩ := hid
    have : r i = 1 := LinearMap.ext fun x => Subtype.ext (hi x x.2)
    rw [← this]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hm : ∀ x y, x ∈ p → y ∈ p → x * y ∈ p := by
    intro x y hx hy
    have hle : p * p ≤ p := by
      rw [Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
      obtain ⟨a, k, hk⟩ := hmul i j
      have : r i * r j = a • r k := LinearMap.ext fun x => Subtype.ext (hk x x.2)
      show r i * r j ∈ p
      rw [this]
      exact p.smul_mem a (Submodule.subset_span ⟨k, rfl⟩)
    exact hle (Submodule.mul_mem_mul hx hy)
  let A : Subalgebra ℂ (Module.End ℂ M) := p.toSubalgebra h1 hm
  have hntM : Nontrivial M := Submodule.nontrivial_iff_ne_bot.2 hM
  haveI : IsSimpleModule A M := by
    refine { toNontrivial := ?_, eq_bot_or_eq_top := fun N => ?_ }
    · obtain ⟨x, hx⟩ := exists_ne (0 : M)
      refine ⟨⟨⊥, ⊤, fun h => hx ?_⟩⟩
      have : x ∈ (⊤ : Submodule A M) := Submodule.mem_top
      rw [← h] at this
      exact (Submodule.mem_bot A).1 this
    · let W : Submodule ℂ X := (N.restrictScalars ℂ).map M.subtype
      have hWM : W ≤ M := by
        rintro _ ⟨m, -, rfl⟩
        exact m.2
      have hWst : ∀ i, ∀ x ∈ W, ρ i x ∈ W := by
        rintro i _ ⟨m, hm, rfl⟩
        refine ⟨r i m, ?_, rfl⟩
        have hri : r i ∈ A := Submodule.subset_span ⟨i, rfl⟩
        exact N.smul_mem (⟨r i, hri⟩ : A) hm
      rcases hirr W hWM hWst with h | h
      · left
        refine eq_bot_iff.2 fun m hm => (Submodule.mem_bot A).2 ?_
        have : (m : X) ∈ W := ⟨m, hm, rfl⟩
        rw [h, Submodule.mem_bot] at this
        exact Subtype.ext this
      · right
        refine eq_top_iff.2 fun m _ => ?_
        have : (m : X) ∈ W := by rw [h]; exact m.2
        obtain ⟨m', hm', e⟩ := this
        rwa [Subtype.ext e] at hm'
  have hscal : ∀ φ : Module.End A M, ∃ c : ℂ, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := M) ℂ).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  let F : Module.End (Module.End A M) M :=
    { toFun := fun m => ⟨P m, hP m m.2⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun φ m => by
        obtain ⟨c, hc⟩ := hscal φ
        apply Subtype.ext
        simp only [Module.End.smul_def, RingHom.id_apply, hc, Submodule.coe_smul, map_smul] }
  let b := Module.finBasis ℂ M
  obtain ⟨a, ha⟩ := jacobson_density F (Finset.univ.image b)
  have hPa : (a : Module.End ℂ M) = P.restrict hP := by
    refine b.ext fun i => ?_
    have := ha (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    exact this.symm
  have hap : (a : Module.End ℂ M) ∈ p := a.2
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hap
  refine ⟨c, fun x hx => ?_⟩
  have e := congrArg (fun e : Module.End ℂ M => (e ⟨x, hx⟩ : X)) (hc.trans hPa)
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul] at e
  simp only [Finsupp.sum]
  exact e

theorem eq_of_orth : ∀ {X : Type} [AddCommGroup X] [Module ℂ X] (M W : Submodule ℂ X), FiniteDimensional ℂ M → W ≤ M →
    ∀ B : X → X → ℂ, (∀ (a : ℂ) (f f' g : X), f ∈ M → f' ∈ M → g ∈ M → B (a • f + f') g = star a * B f g + B f' g) →
    (∀ (a : ℂ) (f g g' : X), f ∈ M → g ∈ M → g' ∈ M → B f (a • g + g') = a * B f g + B f g') →
    (∀ f ∈ M, (∀ g ∈ W, B f g = 0) → f = 0) → W = M := by
  intro X _ _ M W hfd hWM B hl hr horth
  classical
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWM
  have hl0 : ∀ g ∈ M, B 0 g = 0 := fun g hg => by
    have := hl 1 0 0 g M.zero_mem M.zero_mem hg
    simp only [smul_zero, add_zero, star_one, one_mul] at this
    linear_combination -this
  have hr0 : ∀ f ∈ M, B f 0 = 0 := fun f hf => by
    have := hr 1 f 0 0 hf M.zero_mem M.zero_mem
    simp only [smul_zero, add_zero, one_mul] at this
    linear_combination -this
  let b := Module.finBasis ℂ W
  let L : M →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    { toFun := fun f i => star (B f (b i))
      map_add' := fun f f' => funext fun i => by
        have := hl 1 f f' (b i) f.2 f'.2 (hWM (b i).2)
        simp only [one_smul, star_one, one_mul] at this
        simp [this]
      map_smul' := fun a f => funext fun i => by
        have := hl a f 0 (b i) f.2 M.zero_mem (hWM (b i).2)
        rw [add_zero, hl0 _ (hWM (b i).2), add_zero] at this
        simp [this] }
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun f hf => Subtype.ext (horth f f.2 fun g hg => ?_)
    have hbi : ∀ i, B f (b i) = 0 := fun i => by
      have := congrFun hf i
      simpa [L] using this
    let K : Submodule ℂ X :=
      { carrier := {g | g ∈ M ∧ B f g = 0}
        add_mem' := fun {g g'} hg hg' => ⟨M.add_mem hg.1 hg'.1, by
          have := hr 1 f g g' f.2 hg.1 hg'.1
          simp only [one_smul, one_mul] at this
          rw [this, hg.2, hg'.2, add_zero]⟩
        zero_mem' := ⟨M.zero_mem, hr0 f f.2⟩
        smul_mem' := fun a g hg => ⟨M.smul_mem a hg.1, by
          have := hr a f g 0 f.2 hg.1 M.zero_mem
          rw [add_zero, hr0 f f.2, add_zero] at this
          rw [this, hg.2, mul_zero]⟩ }
    have hsum := b.sum_repr ⟨g, hg⟩
    have hgK : (⟨g, hg⟩ : W) = ∑ i, (b.repr ⟨g, hg⟩ i) • b i := hsum.symm
    have : g ∈ K := by
      have e := congrArg Subtype.val hgK
      simp only [Submodule.coe_sum, Submodule.coe_smul] at e
      rw [e]
      exact K.sum_mem fun i _ => K.smul_mem _ ⟨hWM (b i).2, hbi i⟩
    exact this.2
  have hle : Module.finrank ℂ M ≤ Module.finrank ℂ W := by
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this
  exact Submodule.eq_of_le_of_finrank_le hWM hle

end GlobalTheory.VacDensity

theorem GlobalTheory.VacDensity.proj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ v : WO S T → ℂ, IsThetaFunO ψ S T v → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) v) → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ c : WO S T →₀ ℂ, (∀ u ∈ c.support, u.map (infPart D) = 0) ∧ (c.sum fun u z => z • heisO ψ S T u v) = v ∧ ∀ x, x ∈ GlobalTheory.Size.thetaLevel ψ S T U → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) x) → ∃ a : ℂ, (c.sum fun u z => z • heisO ψ S T u x) = a • v := by
  intro D ψ θ S T hψ hθ sS sT hcS hcT v hv hvac U hU
  classical
  by_cases hv0 : v = 0
  · refine ⟨0, by simp, by simp [hv0], fun x _ _ => ⟨0, by simp⟩⟩
  obtain ⟨U₀, o₀, l₀⟩ := hv.level
  set U' : AddSubgroup (WO S T) := U ⊓ U₀ with hU'def
  have hU' : IsOpen (U' : Set (WO S T)) := by rw [hU'def, AddSubgroup.coe_inf]; exact hU.inter o₀
  set M := GlobalTheory.VacSchurFin.vacSub hψ hθ sS sT U' with hMdef
  have hfd := GlobalTheory.VacSchurFin.fd_vacSub hψ hθ sS sT hcS hcT U' hU'
  have hvM : v ∈ M := GlobalTheory.VacSchurFin.mem_vacSub.2
    ⟨hv, fun u hu h => l₀ u (AddSubgroup.mem_inf.1 hu).2 h, hvac⟩
  have hxM : ∀ x, x ∈ GlobalTheory.Size.thetaLevel ψ S T U → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) x) →
      x ∈ M := fun x hx hxv => GlobalTheory.VacSchurFin.mem_vacSub.2
    ⟨hx.1, fun u hu h => hx.2 u (AddSubgroup.mem_inf.1 hu).1 h, hxv⟩
  let N : Set (WO S T) := {w | w.map (infPart D) = 0 ∧ ∀ u ∈ U', u.map (infPart D) = 0 → ψ (symplO S T u w) = 1}
  let ρ : N → (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := fun i => GlobalTheory.SplitScalar.heisL ψ S T i.1
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hst : ∀ w ∈ N, ∀ f ∈ M, heisO ψ S T w f ∈ M := by
    rintro w ⟨hw, hA⟩ f hf
    obtain ⟨hfT, hfL, hfV⟩ := GlobalTheory.VacSchurFin.mem_vacSub.1 hf
    exact GlobalTheory.VacSchurFin.mem_vacSub.2 ⟨laws.1 w f hfT, fun u hu h0 => by
      rw [GlobalTheory.SplitScalar.heisO_comm, hA u hu h0, one_smul, hfL u hu h0], GlobalTheory.VacSchurFin.vac_heisO_fin hθ hw hfV⟩
  have h0N : (0 : WO S T) ∈ N := ⟨by ext i j; show infPart D (0 : AE D) = 0; exact RingHom.map_zero _, fun u _ _ => by
    rw [GlobalTheory.SplitScalar.symplO_zero_right, AddChar.map_zero_eq_one]⟩
  have haddN : ∀ w ∈ N, ∀ w' ∈ N, w + w' ∈ N := by
    rintro w ⟨hw, hA⟩ w' ⟨hw', hA'⟩
    refine ⟨?_, fun u hu h0 => ?_⟩
    · ext i j
      have h1 : infPart D (w i j) = 0 := congrFun (congrFun hw i) j
      have h2 : infPart D (w' i j) = 0 := congrFun (congrFun hw' i) j
      show infPart D (w i j + w' i j) = 0
      rw [RingHom.map_add, h1, h2, add_zero]
    · rw [GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul, hA u hu h0, hA' u hu h0, one_mul]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual ℂ (WO S T → ℂ), ℓ v = 1 := by
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (WO S T → ℂ), f v ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv0 ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
    exact ⟨(f v)⁻¹ • f, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]⟩
  let P : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := ℓ.smulRight v
  have hirr : ∀ W : Submodule ℂ (WO S T → ℂ), W ≤ M → (∀ i, ∀ x ∈ W, ρ i x ∈ W) → W = ⊥ ∨ W = M := by
    intro W hWM hWst
    by_cases hW : W = ⊥
    · exact Or.inl hW
    right
    obtain ⟨g, hgW, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    obtain ⟨vol⟩ := GlobalTheory.Unf.Inhab.nonempty_volM D T.rank S.rank
    have hcv : IsCovolOne (ratL T S) vol.μ vol.𝓕 := vol.covol
    refine GlobalTheory.VacDensity.eq_of_orth M W hfd hWM (GlobalTheory.RawLift.thetaIP vol.μ vol.𝓕)
      (fun a f f' g hf hf' hg => GlobalTheory.VacSchurFin.thetaInner_left hψ hcv a (GlobalTheory.VacSchurFin.mem_vacSub.1 hf).1
        (GlobalTheory.VacSchurFin.mem_vacSub.1 hf').1 (GlobalTheory.VacSchurFin.mem_vacSub.1 hg).1)
      (fun a f g g' hf hg hg' => GlobalTheory.VacSchurFin.thetaInner_right hψ hcv a (GlobalTheory.VacSchurFin.mem_vacSub.1 hf).1
        (GlobalTheory.VacSchurFin.mem_vacSub.1 hg).1 (GlobalTheory.VacSchurFin.mem_vacSub.1 hg').1) ?_
    intro f hf hfo
    obtain ⟨hfT, hfL, hfV⟩ := GlobalTheory.VacSchurFin.mem_vacSub.1 hf
    obtain ⟨hgT, hgL, hgV⟩ := GlobalTheory.VacSchurFin.mem_vacSub.1 (hWM hgW)
    refine (GlobalTheory.VacSchurFin.irr_vac D ψ θ S T hψ hθ sS sT hcS hcT vol.μ vol.𝓕 hcv f g hfT hgT hfV hgV
      fun w hw => ?_).resolve_right hg0
    by_cases hA : ∀ u ∈ U', u.map (infPart D) = 0 → ψ (symplO S T u w) = 1
    · exact hfo _ (hWst ⟨w, hw, hA⟩ g hgW)
    · push_neg at hA
      obtain ⟨u, hu, h0, hne1⟩ := hA
      have hwg : IsThetaFunO ψ S T (heisO ψ S T w g) := laws.1 w g hgT
      have e1 : GlobalTheory.RawLift.thetaIP vol.μ vol.𝓕 f (heisO ψ S T w g) =
          GlobalTheory.RawLift.thetaIP vol.μ vol.𝓕 (heisO ψ S T u f) (heisO ψ S T u (heisO ψ S T w g)) :=
        (GlobalTheory.VacSchurFin.thetaInner_heisenberg hψ hcv hfT hwg u).symm
      rw [hfL u hu h0, GlobalTheory.SplitScalar.heisO_comm, hgL u hu h0, GlobalTheory.VacSchurFin.thetaInner_smul_right] at e1
      have : (1 - ψ (symplO S T u w)) * GlobalTheory.RawLift.thetaIP vol.μ vol.𝓕 f (heisO ψ S T w g) = 0 := by
        linear_combination e1
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne1))
  obtain ⟨c, hc⟩ := GlobalTheory.VacDensity.burn_span M hfd ρ (fun i x hx => hst i.1 i.2 x hx)
    ⟨⟨0, h0N⟩, fun x _ => GlobalTheory.SplitScalar.heisO_zero ψ S T x⟩
    (fun i j => ⟨ψ (symplOH S T i.1 j.1), ⟨i.1 + j.1, haddN i.1 i.2 j.1 j.2⟩, fun x _ =>
      GlobalTheory.SplitScalar.heisO_heisO ψ S T i.1 j.1 x⟩) hirr P (fun x _ => M.smul_mem _ hvM)
  have hsum : ∀ x, ((c.mapDomain Subtype.val).sum fun u z => z • heisO ψ S T u x) = c.sum fun i z => z • ρ i x :=
    fun x => Finsupp.sum_mapDomain_index (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)
  refine ⟨c.mapDomain Subtype.val, fun u hu => ?_, ?_, fun x hx hxv => ⟨ℓ x, ?_⟩⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hu)
    exact i.2.1
  · rw [hsum, hc v hvM]
    simp [P, hℓ]
  · rw [hsum, hc x (hxM x hx hxv)]
    simp [P]
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenbergCombination_projects_onto_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ v : WO S T → ℂ, IsThetaFunO ψ S T v → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) v) → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ c : WO S T →₀ ℂ, (∀ u ∈ c.support, u.map (infPart D) = 0) ∧ (c.sum fun u z => z • heisO ψ S T u v) = v ∧ ∀ x, x ∈ GlobalTheory.Size.thetaLevel ψ S T U → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) x) → ∃ a : ℂ, (c.sum fun u z => z • heisO ψ S T u x) = a • v := by
  atlas_forward_decl GlobalTheory.VacDensity.proj
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.HeisTranslateBound

open GlobalTheory.Size GlobalTheory.OrientedHeis

theorem l2O_heisO_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) (u : WO S T) :
    l2O μ 𝓕 (heisO ψ S T u g) = l2O μ 𝓕 g := by
  have hg' := GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hg u
  have e := ipO_heisO hψ hμ.1 hμ.2.1 hg hg u
  rw [ipO_self, ipO_self, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hg'.cont, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hg.cont, Complex.ofReal_inj,
    pow_left_inj₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg two_ne_zero] at e
  exact (ENNReal.toReal_eq_toReal_iff' (l2NormOnFundamentalDomain_thetaFunction_ne_top hψ hμ.1 hμ.2.1 hg') (l2NormOnFundamentalDomain_thetaFunction_ne_top hψ hμ.1 hμ.2.1 hg)).1 e

theorem sobO_heisO_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) {h : WO S T → ℂ} (hh : IsThetaFunO ψ S T h) {u : WO S T}
    (hu : u.map (infPart D) = 0) (d : ℕ) :
    sobO ψ θ μ 𝓕 d (heisO ψ S T u h) = sobO ψ θ μ 𝓕 d h := by
  have := wordSum_eq_mul (A := heisDer ψ θ) (p := l2O μ 𝓕) (d := d) (x := h) (y := heisO ψ S T u h) (c := 1)
    fun l => by
      have e : wordAct (heisDer ψ θ) l (heisO ψ S T u h) = heisO ψ S T u (wordAct (heisDer ψ θ) l h) :=
        wordAct_rel (R := fun g g' => g = heisO ψ S T u g') l
          (fun a _ _ _ e => e ▸ GlobalTheory.FinTranslate.dRho_heisO hθ hu a.1 _ _) rfl
      rw [e, one_mul, l2O_heisO_eq hψ hθ hμ (theta_word hψ hθ l hh) u]
  rw [one_mul] at this
  exact this

end GlobalTheory.HeisTranslateBound

open GlobalTheory.Size GlobalTheory.HeisTranslateBound GlobalTheory.OrientedHeis in

theorem GlobalTheory.HeisTranslateBound.sobO_finsupp_sum_le : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ c : WO S T →₀ ℂ, (∀ u ∈ c.support, u.map (infPart D) = 0) → ∀ h : WO S T → ℂ, IsThetaFunO ψ S T h → ∀ d : ℕ, GlobalTheory.Size.sobO ψ θ μ 𝓕 d (c.sum fun u z => z • heisO ψ S T u h) ≤ (∑ u ∈ c.support, ‖c u‖ₑ) * GlobalTheory.Size.sobO ψ θ μ 𝓕 d h := by
  intro D ψ θ S T hψ hθ μ 𝓕 hμ c hc h hh d
  have ht : ∀ u, IsThetaFunO ψ S T (c u • heisO ψ S T u h) := fun u =>
    theta_smul (c u) (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hh u)
  refine (sobO_sum_le hψ hθ c.support (g := fun u => c u • heisO ψ S T u h) (fun u _ => ht u) d).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun u hu => ?_
  rw [sobO_smul, sobO_heisO_eq hψ hθ hμ hh (hc u hu)]
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.FinLikeClosure

open GlobalTheory.ChainFr GlobalTheory.Size

theorem fix_of_finLike {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T}
    {f : WO (Vc D i) (Wc D i) → ℂ} (hf : FinLike R i t f) (c : WO (Vc D i) (Wc D i) →₀ ℂ)
    (hc : ∀ u ∈ c.support, u.map (infPart D) = 0)
    (hv : (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u (R.vP i t)) = R.vP i t) :
    (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u f) = f := by
  have key : ∀ g : WO (Vc D i) (Wc D i) → ℂ, ((c - Finsupp.single 0 1).sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u g) =
      (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u g) - g := fun g => by
    rw [Finsupp.sum_sub_index (fun _ _ _ => sub_smul _ _ _), Finsupp.sum_single_index (by rw [zero_smul]), one_smul,
      GlobalTheory.OrientedHeis.heisO_zero]
  classical
  have hs : ∀ u ∈ (c - Finsupp.single 0 1).support, u.map (infPart D) = 0 := fun u hu => by
    rcases Finset.mem_union.1 (Finsupp.support_sub hu) with h | h
    · exact hc u h
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)]
      exact Matrix.map_zero _ (map_zero _)
  have := hf.2 _ hs (by rw [key, hv, sub_self])
  rwa [key, sub_eq_zero] at this

theorem closure : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ f, FinLike R i t f → ∀ (d : ℕ) (δ : ENNReal), 0 < δ → ∃ P, GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P) < δ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t μ 𝓕 hμ f hf d δ hδ
  have hC := hG.core
  have hθ : IsInfFam R.θ := hC.models.inf
  have hψ : IsStdChar D R.ψ (-1) := (hC.thP.ωP i t).std
  let AV := GlobalTheory.WeilReal.frOf (Vc D i) (fun _ => 1) (R.BV i) (fun _ => (Vc D i).rank) (hC.models.BV i)
  let BW := Fr.ofModel (R.MW i (sg0 D A))
  have cAV : AV.cart = fun _ => 1 := GlobalTheory.WeilReal.frOf_cart (hC.models.BV i)
  have oAV : AV.onb = R.BV i := GlobalTheory.WeilReal.frOf_onb (hC.models.BV i)
  have hpt : ∀ x, ptF R.ψ R.θ AV BW x =
      pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) x :=
    fun x => by rw [ptF, cAV, oAV]; rfl
  have hvθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hC.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  have hvv : ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) (R.vP i t) :=
    GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hC.thP.vP i t) hvθ
  have cS : ∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1 := fun τ => by
    have := Model.isCartanInv_cart AV τ
    rwa [cAV] at this
  have cT : ∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) := fun τ => Model.isCartanInv_cart BW τ
  obtain ⟨U, hU, hfU, hdense⟩ := GlobalTheory.FockDensity.fockDense D _ _ AV BW R.θ R.ψ hψ hθ μ 𝓕 hμ f hf.1
  obtain ⟨c, hc0, hcv, hcx⟩ := GlobalTheory.T.exists_heisenbergCombination_projects_onto_vacuum D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ (fun _ => 1) (cart (R.MW i (sg0 D A))) cS cT
    (R.vP i t) hvθ hvv U hU
  let Pf : Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ) :=
    c.sum fun u z => z • GlobalTheory.Hk3.FiniteHeis.heisLin R.ψ (Vc D i) (Wc D i) u
  have hPf : ∀ h, Pf h = c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u h := fun h =>
    LinearMap.finsupp_sum_apply _ _ _
  have hfix : Pf f = f := (hPf f).trans (fix_of_finLike hf c hc0 hcv)
  let Lp := pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
    (onb (R.MW i (sg0 D A))) (R.vP i t)
  have hLp : ∀ P, R.ptP i t P = Lp P := fun _ => rfl

  have himg : ∀ g ∈ fockSpan R.ψ R.θ AV BW U, Pf g ∈ LinearMap.range Lp := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨f₀, P, h1, h2, rfl⟩ := hg
      have hv0 : ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) f₀ :=
        fun τ => by
          have := h1.2 τ
          rwa [cAV] at this
      obtain ⟨a, ha⟩ := hcx f₀ h2 hv0
      refine ⟨a • P, ?_⟩
      rw [hPf, hpt, GlobalTheory.FiniteHeisComb.sum_heisO_pureTensorO D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ _ _ _ _ c hc0 f₀ h1.1 P, ha,
        GlobalTheory.FiniteFock.pureTensorO_smul, map_smul]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  set C : ENNReal := ∑ u ∈ c.support, ‖c u‖ₑ with hCdef
  have hCt : C ≠ ⊤ := ENNReal.sum_ne_top.2 fun _ _ => enorm_ne_top
  rcases eq_or_ne C 0 with hC0 | hC0
  · obtain ⟨g, hg, hgU, -⟩ := hdense d 1 one_pos
    obtain ⟨P, hP⟩ := himg g hg
    refine ⟨P, lt_of_le_of_lt ?_ hδ⟩
    have hb := GlobalTheory.HeisTranslateBound.sobO_finsupp_sum_le D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ μ 𝓕 hμ c hc0 (f - g) (sub_mem hfU hgU).1 d
    rw [← hCdef, hC0, zero_mul, ← hPf, map_sub, hfix, ← hP, ← hLp] at hb
    exact hb
  · obtain ⟨g, hg, hgU, hgd⟩ := hdense d (δ / C) (ENNReal.div_pos hδ.ne' hCt)
    obtain ⟨P, hP⟩ := himg g hg
    refine ⟨P, ?_⟩
    have hb := GlobalTheory.HeisTranslateBound.sobO_finsupp_sum_le D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ μ 𝓕 hμ c hc0 (f - g) (sub_mem hfU hgU).1 d
    rw [← hCdef, ← hPf, map_sub, hfix, ← hP, ← hLp] at hb
    refine lt_of_le_of_lt hb ?_
    calc C * sobO R.ψ R.θ μ 𝓕 d (f - g) < C * (δ / C) := by simpa only [mul_comm C] using ENNReal.mul_lt_mul_left hC0 hCt hgd
      _ = δ := ENNReal.mul_div_cancel hC0 hCt

end GlobalTheory.FinLikeClosure
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_fixedFinitePart_sobolevLimit_fockVectors : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ f, FinLike R i t f → ∀ (d : ℕ) (δ : ENNReal), 0 < δ → ∃ P, GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P) < δ := by
  atlas_forward_decl GlobalTheory.FinLikeClosure.closure
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_vanishes_single_coefficient_of_kernel_kills : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), R.thF i t y = 0 → ∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ptP i t (R.ioP i x w)) l g = 0 := by
  first | exact @GlobalTheory.GenRealSchur.lift_vanish_single | exact GlobalTheory.GenRealSchur.lift_vanish_single | (intros; apply GlobalTheory.GenRealSchur.lift_vanish_single <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.DownLift.GenInfEquiv

theorem representation_inv_mul_left_translate {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (γ h : H) (w : W) :
    ρ (γ * h)⁻¹ (ρ γ w) = ρ h⁻¹ w := by
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

theorem representation_right_translate_inv_mul {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (u h : H) (w : W) :
    ρ u (ρ (h * u)⁻¹ w) = ρ h⁻¹ w := by
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem ext_apply' {V : HSp D} (c : CoefA V) (φ : Formalism.IndefR.Bridge.Gf V → c.W) (h : GA D V) :
    c.ext φ h = c.ρ h⁻¹ (φ ((finHom V).rangeRestrict h)) := rfl

theorem ext_left' {V : HSp D} (c : CoefA V) (J : Subgroup (Formalism.IndefR.Bridge.Gf V)) (χ : J →* ℂˣ)
    (φ : Formalism.IndefR.Bridge.Gf V → c.W)
    (hφ : φ ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ J χ) (γ : GA D V) (hγ : γ ∈ GQ V)
    (h : GA D V) : c.ext φ (γ * h) = c.ext φ h := by
  have h1 := hφ ⟨γ, hγ⟩ ((finHom V).rangeRestrict h) 1
  simp only [map_one, Units.val_one, one_smul, OneMemClass.coe_one, mul_one] at h1
  have h2 : φ ((finHom V).rangeRestrict γ * (finHom V).rangeRestrict h) = c.ρ γ (φ ((finHom V).rangeRestrict h)) := h1
  rw [ext_apply', ext_apply', map_mul (finHom V).rangeRestrict, h2]
  exact representation_inv_mul_left_translate c.ρ γ h _

theorem ext_inf' {V : HSp D} (c : CoefA V) (φ : Formalism.IndefR.Bridge.Gf V → c.W) (u : GA D V) (hu : u ∈ GinfC V)
    (h : GA D V) : c.ρ u (c.ext φ (h * u)) = c.ext φ h := by
  have e1 : (finHom V).rangeRestrict (h * u) = (finHom V).rangeRestrict h := by
    apply Subtype.ext
    have h1 : finHom V u = 1 := hu
    show finHom V (h * u) = finHom V h
    rw [map_mul, h1, mul_one]
  rw [ext_apply', ext_apply', e1]
  exact representation_right_translate_inv_mul c.ρ u h _

theorem om_left' {ψ : AddChar (AF D.host.F) ℂ} {S T' : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)} (H : IsWeilDatumO ψ S T' χS χT om) (γ : GA D S)
    (hγ : γ ∈ GQ S) (h : GA D S) (g : GA D T') (f : WO S T' → ℂ) (hf : IsThetaFunO ψ S T' f) :
    thetaKO om (γ * h) g f = thetaKO om h g f := by
  unfold thetaKO
  have e : ((γ * h, g) : GA D S × GA D T') = (γ, (1 : GA D T')) * (h, g) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact H.om_aut _ hγ _ (Subgroup.one_mem _) _ (H.om_pres _ _ hf)

theorem om_right' {S T' : HSp D} (om : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)) (u h : GA D S)
    (g : GA D T') (f : WO S T' → ℂ) : thetaKO om (h * u) g f = thetaKO om h g (om (u, 1) f) := by
  unfold thetaKO
  have e : ((h * u, g) : GA D S × GA D T') = (h, g) * (u, (1 : GA D T')) := by simp
  rw [e, map_mul, Module.End.mul_apply]

theorem mem_of_hmodIs {X : Type} [AddCommGroup X] [Module ℂ X] (M : HMod X) (V : Submodule ℂ X) (ip : X → X → ℂ)
    (h : M.Is V ip) (x : M.H) : M.e x ∈ V := h.2.1 ▸ ⟨x, rfl⟩

end GlobalTheory.DownLift.GenInfEquiv

open GlobalTheory.DownLift.GenInfEquiv in

theorem GlobalTheory.DownLift.downInt_realEquiv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ωP i t (u, 1) f) l g = downInt R i t y f (l ∘ₗ (R.cV i).ρ u) g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y u hu f hf l g
  have hM : R.IsModels := hG.core.models
  have hν := hM.νV i t
  haveI := Formalism.IndefR.Eqv.measurableMul_GA D (Vc D i)
  haveI := Formalism.IndefR.Eqv.gQ_countable D (Vc D i)
  haveI : (R.νV i t).IsHaarMeasure := hν.1.1
  haveI : (R.νV i t).IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds (Vc D i) _ hν.1.1
  have hx := mem_of_hmodIs _ _ _ (hM.HV i t) y
  have hW := (hP i t).datum
  let Ψ : GA D (Vc D i) → ℂ := fun h =>
    thetaKO (R.ωP i t) h g f * (l ∘ₗ (R.cV i).ρ u) ((R.cV i).ext ((R.HV i t).e y) h)
  have hL : ∀ γ ∈ GQ (Vc D i), ∀ h, Ψ (γ * h) = Ψ h := by
    intro γ hγ h
    exact congrArg₂ (fun a b => a * (l ∘ₗ (R.cV i).ρ u) b) (om_left' hW γ hγ h g f hf)
      (ext_left' (R.cV i) _ _ _ hx γ hγ h)
  have hR : ∀ h, thetaKO (R.ωP i t) h g (R.ωP i t (u, 1) f) * l (R.extV i t y h) = Ψ (h * u) := by
    intro h
    exact congrArg₂ (fun a b => a * l b) (om_right' (R.ωP i t) u h g f).symm
      (ext_inf' (R.cV i) ((R.HV i t).e y) u hu h).symm
  have key := (Formalism.IndefR.Eqv.rightInv_holds _ (GQ (Vc D i)) (R.νV i t) _ hν.2 Ψ hL u).2
  have e1 : downInt R i t y (R.ωP i t (u, 1) f) l g = ∫ h in R.fdV i t, Ψ (h * u) ∂(R.νV i t) := by
    unfold downInt
    exact integral_congr_ae (Filter.Eventually.of_forall hR)
  have e2 : downInt R i t y f (l ∘ₗ (R.cV i).ρ u) g = ∫ h in R.fdV i t, Ψ h ∂(R.νV i t) := rfl
  rw [e1, e2, key]

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downwardThetaLift_real_points_equivariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ωP i t (u, 1) f) l g = downInt R i t y f (l ∘ₗ (R.cV i).ρ u) g := by
  atlas_forward_decl GlobalTheory.DownLift.downInt_realEquiv
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.DownLift.GenReal

set_option maxHeartbeats 2000000 in

theorem downInt_lie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (τ : D.what₂.Tau)
    (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ →
    ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank),
    (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) →
    ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ), (∀ g, downInt R i t y (R.ptP i t P) l g = 0) →
    ∀ g, downInt R i t y (R.ptP i t P') l g = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y τ Y hY P P' hder l hvan g
  have hm := hG.core.models
  have hθ : IsInfFam R.θ := hm.inf
  have hom := (hP i t).datum
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.ptP i t P) := hG.core.thP.pt_theta i t P
  obtain ⟨ht, hd⟩ := GlobalTheory.Chain.LiftReg.tame_dOmT hθ hom hY
  have hf' := ht.theta hf

  have hid : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT R.θ (R.ωP i t) τ Y (R.ptP i t P) = R.ptP i t P' := by
    funext z
    have h1 := hd _ hf 1 z
    simp only [one_mul, map_one, Module.End.one_apply] at h1
    exact h1.unique (hder z)
  rw [← hid]
  set f := R.ptP i t P with hfdef
  set f' := GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT R.θ (R.ωP i t) τ Y f with hf'def

  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [hm.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have hcont : Continuous fun h => l (R.extV i t y h) :=
    (LinearMap.continuous_of_finiteDimensional l).comp
      (GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx)
  have hinv : ∀ γ ∈ GQ (Vc D i), ∀ h, l (R.extV i t y (γ * h)) = l (R.extV i t y h) := fun γ hγ h =>
    congrArg l (GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx γ hγ h)
  have hrat : ∀ γ ∈ GQ (Vc D i), ∀ (c : GA D (Vc D i)) (g' : GA D (Wc D i)),
      thetaKO (R.ωP i t) (γ * c) g' f' = thetaKO (R.ωP i t) c g' f' := by
    intro γ hγ c g'
    unfold thetaKO
    have e : ((γ * c, g') : GA D (Vc D i) × GA D (Wc D i)) = ((γ, 1) : GA D (Vc D i) × GA D (Wc D i)) * (c, g') := by
      rw [Prod.mk_mul_mk, one_mul]
    rw [e, map_mul, Module.End.mul_apply]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hf')
  haveI : BorelSpace (GA D (Vc D i)) := ⟨rfl⟩

  obtain ⟨C, hC, hcov⟩ := GlobalTheory.DefiniteQuotient.exists_compact (Vc D i) hpos
  have hΨ : Continuous fun p : GA D (Vc D i) × ℝ =>
      thetaKO (R.ωP i t) p.1 (g * oneP R.θ (Wc D i) τ Y p.2) f' * l (R.extV i t y p.1) := by
    refine Continuous.mul ?_ (hcont.comp continuous_fst)
    exact (hom.om_cont f' hf' 0).comp (continuous_fst.prodMk
      (continuous_const.mul ((GlobalTheory.Mem.Lift.continuous_oneP hθ hY).comp continuous_snd)))
  obtain ⟨B, hB⟩ := (hC.prod (isCompact_closedBall (0 : ℝ) 1)).exists_bound_of_continuousOn hΨ.continuousOn
  have hbd : ∀ (h : GA D (Vc D i)) (x : ℝ), x ∈ Metric.ball (0 : ℝ) 1 →
      ‖thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) f' * l (R.extV i t y h)‖ ≤ B := by
    intro h x hxb
    obtain ⟨γ, hγ, c, hc, e⟩ := hcov h
    subst e
    rw [hrat γ hγ c, hinv γ hγ c]
    exact hB (c, x) (Set.mk_mem_prod hc (Metric.ball_subset_closedBall hxb))

  have hfin : R.νV i t (R.fdV i t) < ⊤ := by
    haveI : Countable (GQ (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
    haveI : IsTopologicalGroup (GA D (Vc D i)) :=
      inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Vc D i).gram))
    have h1 := GlobalTheory.integrableOn_fundamentalDomain_of_cocompact (GA D (Vc D i)) (GQ (Vc D i)) C hC
      (fun h => by
        obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
        exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩)
      (R.νV i t) (hm.νV i t).1.1 (R.fdV i t) (hm.νV i t).2 (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl)
    rcases (integrableOn_const_iff (C := (1 : ℂ))).1 h1 with h2 | h2
    · simp at h2
    · exact h2

  have hmeas : ∀ (φ : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) φ → ∀ x : ℝ,
      AEStronglyMeasurable (fun h => thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) φ * l (R.extV i t y h))
        ((R.νV i t).restrict (R.fdV i t)) := fun φ hφ x =>
    (((hom.om_cont φ hφ 0).comp (continuous_id.prodMk continuous_const)).mul hcont).measurable.aestronglyMeasurable
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (R.νV i t).restrict (R.fdV i t))
    (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1)
    (F := fun x h => thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) f * l (R.extV i t y h))
    (F' := fun x h => thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) f' * l (R.extV i t y h))
    (bound := fun _ => B) (Metric.ball_mem_nhds 0 one_pos) (.of_forall fun x => hmeas f hf x)
    (GlobalTheory.DownLift.GenFinite.integrableOn_downIntegrand D G Pl0 T A Ks R F hG hP i t y f l _ hf)
    (hmeas f' hf' 0) (.of_forall fun h x hxb => hbd h x hxb) (integrableOn_const hfin.ne)
    (.of_forall fun h x _ => ?_)).2
  · have e : (fun x : ℝ => ∫ h in R.fdV i t, thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) f *
        l (R.extV i t y h) ∂(R.νV i t)) = fun _ => 0 := funext fun x => hvan _
    rw [e] at key
    have h0 := key.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at h0
    exact h0
  · refine (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hY (φ := fun g' => thetaKO (R.ωP i t) h g' f)
      (φ' := fun g' => thetaKO (R.ωP i t) h g' f') (fun g' => ?_) g x).mul_const _
    simpa only [thetaKO, Prod.mk_mul_mk, mul_one] using hd f hf (h, g') 0

end GlobalTheory.DownLift.GenReal
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_vanishing_preserved_by_realLieDerivative : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ), (∀ g, downInt R i t y (R.ptP i t P) l g = 0) → ∀ g, downInt R i t y (R.ptP i t P') l g = 0 := by
  atlas_forward_decl GlobalTheory.DownLift.GenReal.downInt_lie
end

section
section
namespace GlobalTheory

open Submodule

section SchurIsotypic
variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma schur_act_inv (act : G →* Module.End ℂ H) (g : G) (y : H) : act g (act g⁻¹ y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

lemma schur_orth_stable (act : G →* Module.End ℂ H)
    (hact : ∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0)
    (P : Submodule ℂ H) (hP : ∀ g, ∀ p ∈ P, act g p ∈ P) :
    ∀ g, ∀ e ∈ Pᗮ, act g e ∈ Pᗮ := by
  intro g e he
  rw [Submodule.mem_orthogonal] at he ⊢
  intro u hu
  have := hact g _ _ (he _ (hP g⁻¹ u hu))
  rwa [schur_act_inv] at this

lemma schur_decomp [FiniteDimensional ℂ H] (P : Submodule ℂ H) (x : H) :
    ∃ p ∈ P, x - p ∈ Pᗮ := by
  exact ⟨P.starProjection x, P.starProjection_apply_mem x, P.sub_starProjection_mem_orthogonal x⟩

lemma schur_vanish {W : Type} [AddCommGroup W] [Module ℂ W] [Nontrivial W] [FiniteDimensional ℂ H]
    (act : G →* Module.End ℂ H)
    (hact : ∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0)
    (ρ : G →* Module.End ℂ W)
    (hirr : ∀ U : Submodule ℂ W, (∀ g, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤)
    (E : Submodule ℂ H) (hE : ∀ g, ∀ e ∈ E, act g e ∈ E)
    (hEorth : ∀ χ : W →ₗ[ℂ] H, (∀ g w, χ (ρ g w) = act g (χ w)) →
      ∀ w, ∀ e ∈ E, inner ℂ (χ w) e = 0)
    (φ : H →ₗ[ℂ] W) (hφ : ∀ g, ∀ e ∈ E, φ (act g e) = ρ g (φ e)) : ∀ e ∈ E, φ e = 0 := by
  by_contra hne
  push_neg at hne
  obtain ⟨e₀, he₀E, he₀⟩ := hne
  let K : Submodule ℂ H := LinearMap.ker φ ⊓ E
  have hK : ∀ g, ∀ k ∈ K, act g k ∈ K := by
    intro g k hk
    obtain ⟨hk1, hk2⟩ := Submodule.mem_inf.1 hk
    refine Submodule.mem_inf.2 ⟨?_, hE g k hk2⟩
    rw [LinearMap.mem_ker] at hk1 ⊢
    rw [hφ g k hk2, hk1, map_zero]
  let C : Submodule ℂ H := Kᗮ ⊓ E
  have hC : ∀ g, ∀ c ∈ C, act g c ∈ C := fun g c hc =>
    Submodule.mem_inf.2 ⟨schur_orth_stable act hact K hK g c (Submodule.mem_inf.1 hc).1,
      hE g c (Submodule.mem_inf.1 hc).2⟩
  have hCE : ∀ c ∈ C, c ∈ E := fun c hc => (Submodule.mem_inf.1 hc).2
  have hinj : ∀ c ∈ C, φ c = 0 → c = 0 := by
    intro c hc h0
    have hcK : c ∈ K := Submodule.mem_inf.2 ⟨h0, hCE c hc⟩
    have := (Submodule.mem_orthogonal _ _).1 (Submodule.mem_inf.1 hc).1 c hcK
    exact inner_self_eq_zero.1 this
  have hU : C.map φ = ⊤ := by
    rcases hirr (C.map φ) (by
      intro g
      rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨act g c, hC g c hc, hφ g c (hCE c hc)⟩) with h | h
    · exfalso
      obtain ⟨p, hp, hr⟩ := schur_decomp K e₀
      have hrE : e₀ - p ∈ E := E.sub_mem he₀E (Submodule.mem_inf.1 hp).2
      have hrC : e₀ - p ∈ C := Submodule.mem_inf.2 ⟨hr, hrE⟩
      have hm : φ (e₀ - p) ∈ C.map φ := Submodule.mem_map_of_mem hrC
      rw [h, Submodule.mem_bot, map_sub, LinearMap.mem_ker.1 (Submodule.mem_inf.1 hp).1,
        sub_zero] at hm
      exact he₀ hm
    · exact h
  let ψ : C →ₗ[ℂ] W := φ.comp C.subtype
  have hψi : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    exact Subtype.ext (hinj c c.2 (LinearMap.mem_ker.1 hc))
  have hψs : Function.Surjective ψ := by
    intro w
    have hw : w ∈ C.map φ := hU ▸ Submodule.mem_top
    obtain ⟨c, hc, hcw⟩ := hw
    exact ⟨⟨c, hc⟩, hcw⟩
  let e := LinearEquiv.ofBijective ψ ⟨hψi, hψs⟩
  let χ : W →ₗ[ℂ] H := C.subtype.comp e.symm.toLinearMap
  have hχC : ∀ w, χ w ∈ C := fun w => (e.symm w).2
  have hφχ : ∀ w, φ (χ w) = w := fun w => by
    show ψ (e.symm w) = w
    exact e.apply_symm_apply w
  have hχ : ∀ g w, χ (ρ g w) = act g (χ w) := by
    intro g w
    have hd : χ (ρ g w) - act g (χ w) ∈ C := C.sub_mem (hχC _) (hC g _ (hχC w))
    have := hinj _ hd (by rw [map_sub, hφχ, hφ g _ (hCE _ (hχC w)), hφχ, sub_self])
    exact sub_eq_zero.1 this
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have h0 : χ w = 0 := inner_self_eq_zero.1 (hEorth χ hχ w (χ w) (hCE _ (hχC w)))
  exact hw (by rw [← hφχ w, h0, map_zero])

end SchurIsotypic

theorem schur_isotypic_splitting : ∀ {G W H : Type} [Group G] [AddCommGroup W] [Module ℂ W] [Nontrivial W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (act : G →* Module.End ℂ H), (∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0) → ∀ (ρ : G →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ g, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ x : H, ∃ q ∈ Submodule.span ℂ {q | ∃ (φ : W →ₗ[ℂ] H) (w : W), (∀ g w', φ (ρ g w') = act g (φ w')) ∧ q = φ w}, ∃ E : Submodule ℂ H, (∀ g, ∀ e ∈ E, act g e ∈ E) ∧ (∀ φ : H →ₗ[ℂ] W, (∀ g, ∀ e ∈ E, φ (act g e) = ρ g (φ e)) → ∀ e ∈ E, φ e = 0) ∧ x - q ∈ E := by
  intro G W H _ _ _ _ _ _ _ act hact ρ hirr x
  let S : Set H := {q | ∃ (φ : W →ₗ[ℂ] H) (w : W), (∀ g w', φ (ρ g w') = act g (φ w')) ∧ q = φ w}
  let I : Submodule ℂ H := Submodule.span ℂ S
  have hI : ∀ g, ∀ y ∈ I, act g y ∈ I := by
    intro g y hy
    have hle : I.map (act g) ≤ I := by
      rw [Submodule.map_span]
      apply Submodule.span_le.2
      rintro _ ⟨_, ⟨φ, w, hφ, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨φ, ρ g w, hφ, (hφ g w).symm⟩
    exact hle (Submodule.mem_map_of_mem hy)
  obtain ⟨q, hq, hxq⟩ := schur_decomp I x
  refine ⟨q, hq, Iᗮ, schur_orth_stable act hact I hI, ?_, hxq⟩
  intro φ hφ
  refine schur_vanish act hact ρ hirr Iᗮ (schur_orth_stable act hact I hI) ?_ φ hφ
  intro χ hχ w e he
  exact (Submodule.mem_orthogonal _ _).1 he _ (Submodule.subset_span ⟨χ, w, hχ, rfl⟩)

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_isotypic_splitting_inner_product : ∀ {G W H : Type} [Group G] [AddCommGroup W] [Module ℂ W] [Nontrivial W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (act : G →* Module.End ℂ H), (∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0) → ∀ (ρ : G →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ g, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ x : H, ∃ q ∈ Submodule.span ℂ {q | ∃ (φ : W →ₗ[ℂ] H) (w : W), (∀ g w', φ (ρ g w') = act g (φ w')) ∧ q = φ w}, ∃ E : Submodule ℂ H, (∀ g, ∀ e ∈ E, act g e ∈ E) ∧ (∀ φ : H →ₗ[ℂ] W, (∀ g, ∀ e ∈ E, φ (act g e) = ρ g (φ e)) → ∀ e ∈ E, φ e = 0) ∧ x - q ∈ E := by
  atlas_forward_decl GlobalTheory.schur_isotypic_splitting
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Datum Formalism.IndefR.Links MvPolynomial Matrix
open scoped Classical

namespace GlobalTheory.FockIsotypic

variable {D : D7} {m n : ℕ}

def fvarRegroup (D : D7) (m n : ℕ) : FVar D m n ≃ Fin n × (D.what₂.Tau × Fin m) where
  toFun v := (v.2.2, (v.1, v.2.1))
  invFun w := (w.2.1, w.2.2, w.1)
  left_inv _ := rfl
  right_inv _ := rfl

def flatRegroup (D : D7) (m n : ℕ) : Fin (Fintype.card (FVar D m n)) ≃ Fin n × (D.what₂.Tau × Fin m) :=
  (Equiv.prodPUnit _).symm.trans ((flat (FVar D m n)).symm.trans (fvarRegroup D m n))

def fockBlock (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n) (k : D.what₂.Tau × Fin m) : Matrix (Fin n) (Fin n) ℂ :=
  if k.2.val < p k.1 then ((((U k.1)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᵀ else ((U k.1 : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)

def fockMat (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n) :
    Matrix (Fin (Fintype.card (FVar D m n))) (Fin (Fintype.card (FVar D m n))) ℂ :=
  (blockDiagonal (fockBlock (m := m) p U)).submatrix (flatRegroup D m n) (flatRegroup D m n)

theorem rename_fockSubst (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n) (P : PolF D m n) :
    rename (flat (FVar D m n)) (GlobalTheory.ExportSeries.fockSubst p U P) =
      ReciprocityTheory.PGsh.rowSubst (fockMat p U) (rename (flat (FVar D m n)) P) := by
  have key : (rename (flat (FVar D m n))).comp (GlobalTheory.ExportSeries.fockSubst p U) =
      (ReciprocityTheory.PGsh.rowSubst (fockMat p U)).comp (rename (flat (FVar D m n))) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, GlobalTheory.ExportSeries.fockSubst, aeval_X, rename_X, ReciprocityTheory.PGsh.rowSubst_X,
      ← (flatRegroup D m n).symm.sum_comp, Fintype.sum_prod_type_right,
      Finset.sum_eq_single (v.1, v.2.1)]
    · have hv : flatRegroup D m n (flat (FVar D m n) v).1 = (v.2.2, (v.1, v.2.1)) := by
        change fvarRegroup D m n ((flat (FVar D m n)).symm ((flat (FVar D m n) v).1, PUnit.unit)) = _
        rw [show ((flat (FVar D m n) v).1, PUnit.unit) = flat (FVar D m n) v from rfl, Equiv.symm_apply_apply]
        rfl
      have hx : ∀ b : Fin n, ((flatRegroup D m n).symm (b, (v.1, v.2.1)), (flat (FVar D m n) v).2) =
          flat (FVar D m n) (v.1, v.2.1, b) := fun b => by
        simp [flatRegroup, fvarRegroup]
      simp only [fockMat, submatrix_apply, Equiv.apply_symm_apply, hv, blockDiagonal_apply_eq, hx]
      split_ifs with h <;> simp [fockBlock, h, map_sum, rename_X]
    · intro k _ hk
      refine Finset.sum_eq_zero fun b _ => ?_
      have hv : flatRegroup D m n (flat (FVar D m n) v).1 = (v.2.2, (v.1, v.2.1)) := by
        change fvarRegroup D m n ((flat (FVar D m n)).symm ((flat (FVar D m n) v).1, PUnit.unit)) = _
        rw [show ((flat (FVar D m n) v).1, PUnit.unit) = flat (FVar D m n) v from rfl, Equiv.symm_apply_apply]
        rfl
      simp [fockMat, hv, blockDiagonal_apply_ne _ _ _ hk]
    · simp
  exact congrArg (fun f => f P) key

theorem fockBlock_conjTranspose_mul (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n)
    (hU : ∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) (k : D.what₂.Tau × Fin m) :
    (fockBlock p U k)ᴴ * fockBlock p U k = 1 := by
  have hu := hU k.1
  rw [Matrix.mem_unitaryGroup_iff] at hu
  have hu' := hU k.1
  rw [Matrix.mem_unitaryGroup_iff'] at hu'
  unfold fockBlock
  split_ifs
  · have hinv : (((U k.1)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = star (U k.1).val :=
      Units.inv_eq_of_mul_eq_one_right hu
    rw [hinv]
    ext i j
    have := congrArg (starRingEnd ℂ) (congrFun (congrFun hu' i) j)
    simp only [Matrix.mul_apply, Matrix.star_apply, map_sum, map_mul, Complex.conj_conj, RCLike.star_def] at this
    have h1 : ((star (U k.1).val)ᵀᴴ * (star (U k.1).val)ᵀ) i j =
        ∑ x, (U k.1).val x i * starRingEnd ℂ ((U k.1).val x j) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.star_apply, RCLike.star_def,
        Complex.conj_conj]
    rw [h1, this, Matrix.one_apply]
    split_ifs <;> simp
  · simpa [Matrix.star_eq_conjTranspose] using hu'

theorem fockMat_conjTranspose_mul (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n)
    (hU : ∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (fockMat (m := m) p U)ᴴ * fockMat p U = 1 := by
  rw [fockMat, conjTranspose_submatrix, submatrix_mul_equiv, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
  simp only [fockBlock_conjTranspose_mul p U hU]
  rw [show (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) = (1 : D.what₂.Tau × Fin m → Matrix (Fin n) (Fin n) ℂ) from rfl,
    blockDiagonal_one, submatrix_one_equiv]

theorem fis_fockSubst_of_unitary (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n)
    (hU : ∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) (P Q : PolF D m n) :
    fis (GlobalTheory.ExportSeries.fockSubst p U P) (GlobalTheory.ExportSeries.fockSubst p U Q) = fis P Q := by
  unfold fis
  rw [rename_fockSubst, rename_fockSubst, ReciprocityTheory.PGsh.fischer_rowSubst, ReciprocityTheory.PGsh.rowSubst_mul,
    fockMat_conjTranspose_mul p U hU, ReciprocityTheory.PGsh.rowSubst_one]

end GlobalTheory.FockIsotypic
end
end

open Formalism.BasicNotions Formalism.IndefR.Datum Formalism.IndefR.Links
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fischerInnerForm_fockSubstitution_unitary_invariant : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ P Q : PolF D m n, GlobalTheory.FockIsotypic.fis (GlobalTheory.ExportSeries.fockSubst p U P) (GlobalTheory.ExportSeries.fockSubst p U Q) = GlobalTheory.FockIsotypic.fis P Q := by
  atlas_forward_decl GlobalTheory.FockIsotypic.fis_fockSubst_of_unitary
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.RealFockActionFree

open GlobalTheory.ExportSeries
open scoped ComplexOrder

theorem om_ptP_inf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∃ (p : D.what₂.Tau → ℕ) (c : ℂ) (U : GlobalTheory.ExportSeries.GLR D (Vc D i).rank), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) ∧ ∀ P : PolF D (Wc D i).rank (Vc D i).rank, R.ωP i t (u, 1) (R.ptP i t P) = R.ptP i t (c • GlobalTheory.ExportSeries.fockSubst p U P) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC i t u hu
  obtain ⟨hf, hv, -⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  have hW := hC.thP.ωP i t
  have hθ : IsInfFam R.θ := hC.models.inf
  have hBS := fun τ => GlobalTheory.RealFockAction.onb_posDef (hC.models.BV i τ)
  have hS : ∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1 := fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBS τ)
  have hT : ∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) :=
    fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart _ τ
  have one : ∀ τ, compAt R.θ τ (Formalism.L2.Theta.mt (Wc D i) 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one (Wc D i) _
  let BU : GLR D (Vc D i).rank := fun τ => (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hC.models.BV i τ)).unit
  let U : GLR D (Vc D i).rank := inBasis BU (realGL R.θ (Vc D i) u)
  have eu : ∀ τ, (U τ).val = (R.BV i τ)⁻¹ * compAt R.θ τ (Formalism.L2.Theta.mt (Vc D i) u) * R.BV i τ := fun τ => by
    show _ = ((BU τ).val)⁻¹ * _ * (BU τ).val
    rw [← Matrix.coe_units_inv]
    rfl
  have hU : ∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ := fun τ => by
    rw [eu]; exact GlobalTheory.RealFockAction.conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ (Vc D i) u τ)
  have hle : ∀ τ, ((Wc D i).sig (tauE D τ)).1 ≤ (Wc D i).rank := fun τ => by
    have hs : (Wc D i).SigOK := D.sp.W_sig _
    obtain ⟨e, -⟩ := hs (tauE D τ)
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  have hev : Even (Vc D i).rank := (D.sp.V_rank _ (Nat.le_add_left _ _) i.2) ▸ (GlobalTheory.ConjTwist.Test.odd_r D).add_odd D.R.t_odd
  have hη := GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hC.lev.eta R.C.isEta _ _ _ hW.resS hW.resT
    (hev.add_odd ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2) ▸ GlobalTheory.ConjTwist.Test.odd_r D))
  obtain ⟨x, hx, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ (Vc D i) (fun τ => by
    have := (hS τ).2.2.det_pos.ne'
    rwa [Matrix.mul_one] at this) u hu
  have hy : IsDetRoot (Wc D i) 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  obtain ⟨c, hc⟩ : ∃ c : ℂ, R.ωP i t (u, 1) (R.vP i t) = c • R.vP i t :=
    ⟨_, GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D R.ψ hW.std (Vc D i) (Wc D i) R.θ hθ _ _ (R.ωP i t) _ hη hW (fun _ => 1)
      (cart (R.MW i (sg0 D A))) hS hT u hu 1 (one_mem _) (fun τ => by rw [one_mul, mul_one])
      (fun τ => by rw [one, one_mul, mul_one]) x 1 hx hy _ hf hv⟩
  refine ⟨fun τ => ((Wc D i).sig (tauE D τ)).1, c, U, hU, fun P => ?_⟩
  unfold RealDat.ptP
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D _ _ (Vc D i) (Wc D i) _ _ (R.ωP i t) hW hθ (fun _ => 1) (fun _ => 1) (R.BV i)
    (fun τ => R.BV i τ * (U τ).val) (cart (R.MW i (sg0 D A))) (cart (R.MW i (sg0 D A)))
    (onb (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) u 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, one_mul, mul_one])
    (fun τ => by rw [eu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hC.models.BV i τ))), Matrix.one_mul])
    (fun τ => by rw [one, one_mul]) _ hf P).2, hc, GlobalTheory.FiniteFock.pureTensorO_smul,
    GlobalTheory.RealFockAction.pureTensorO_subst (p := fun τ => ((Wc D i).sig (tauE D τ)).1) hW.std hθ hS hT
      (fun τ => (GlobalTheory.RealFockAction.onb_laws (GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hC.models.order i τ)) (hle τ)).1)
      _ _ hU hf, LinearMap.map_smul]

end GlobalTheory.RealFockActionFree
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoints_act_fock_scalar_unitary_substitution : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∃ (p : D.what₂.Tau → ℕ) (c : ℂ) (U : GlobalTheory.ExportSeries.GLR D (Vc D i).rank), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) ∧ ∀ P : PolF D (Wc D i).rank (Vc D i).rank, R.ωP i t (u, 1) (R.ptP i t P) = R.ptP i t (c • GlobalTheory.ExportSeries.fockSubst p U P) := by
  atlas_forward_decl GlobalTheory.RealFockActionFree.om_ptP_inf
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.FockIsotypic

theorem isotypic_split : ∀ {G W H : Type} [Group G] [AddCommGroup W] [Module ℂ W] [Nontrivial W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (act : G →* Module.End ℂ H), (∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0) → ∀ (ρ : G →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ g, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ x : H, ∃ q ∈ Submodule.span ℂ {q | ∃ (φ : W →ₗ[ℂ] H) (w : W), (∀ g w', φ (ρ g w') = act g (φ w')) ∧ q = φ w}, ∃ E : Submodule ℂ H, (∀ g, ∀ e ∈ E, act g e ∈ E) ∧ (∀ φ : H →ₗ[ℂ] W, (∀ g, ∀ e ∈ E, φ (act g e) = ρ g (φ e)) → ∀ e ∈ E, φ e = 0) ∧ x - q ∈ E := GlobalTheory.T.schur_isotypic_splitting_inner_product

theorem fis_fockSubst : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ P Q : PolF D m n, GlobalTheory.FockIsotypic.fis (GlobalTheory.ExportSeries.fockSubst p U P) (GlobalTheory.ExportSeries.fockSubst p U Q) = GlobalTheory.FockIsotypic.fis P Q := GlobalTheory.T.fischerInnerForm_fockSubstitution_unitary_invariant

theorem om_ptP_fock : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∃ (p : D.what₂.Tau → ℕ) (c : ℂ) (U : GlobalTheory.ExportSeries.GLR D (Vc D i).rank), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) ∧ ∀ P : PolF D (Wc D i).rank (Vc D i).rank, R.ωP i t (u, 1) (R.ptP i t P) = R.ptP i t (c • GlobalTheory.ExportSeries.fockSubst p U P) := GlobalTheory.T.realPoints_act_fock_scalar_unitary_substitution

theorem totalDegree_aeval_le {σ κ : Type} (f : σ → MvPolynomial κ ℂ) (hf : ∀ v, (f v).totalDegree ≤ 1)
    (P : MvPolynomial σ ℂ) : (MvPolynomial.aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun s hs => ?_
  rw [MvPolynomial.aeval_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h0 : (algebraMap ℂ (MvPolynomial κ ℂ) (MvPolynomial.coeff s P)).totalDegree = 0 :=
    MvPolynomial.totalDegree_C _
  rw [h0, zero_add]
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  unfold Finsupp.prod Finsupp.sum
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc s i * (f i).totalDegree ≤ s i * 1 := Nat.mul_le_mul_left _ (hf i)
    _ = s i := mul_one _

theorem totalDegree_fockSubst_le {D : D7} {m n : ℕ} (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n)
    (P : PolF D m n) : (GlobalTheory.ExportSeries.fockSubst p U P).totalDegree ≤ P.totalDegree := by
  unfold GlobalTheory.ExportSeries.fockSubst
  refine totalDegree_aeval_le _ (fun v => ?_) P
  split_ifs
  all_goals
    refine MvPolynomial.totalDegree_finsetSum_le fun b _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

theorem decomp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∀ (P : PolF D (Wc D i).rank (Vc D i).rank), ∃ Q ∈ Submodule.span ℂ {Q : PolF D (Wc D i).rank (Vc D i).rank | ∃ (φ : (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (w : (R.cV i).W), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) ∧ Q = φ w}, ∃ E : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank), FiniteDimensional ℂ E ∧ (∀ u ∈ GinfC (Vc D i), ∀ P₁ ∈ E, ∀ P₂ : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P₂ = R.ωP i t (u, 1) (R.ptP i t P₁) → P₂ ∈ E) ∧ (∀ φ : PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ, (∀ u ∈ GinfC (Vc D i), ∀ P₁ ∈ E, ∀ P₂ : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P₂ = R.ωP i t (u, 1) (R.ptP i t P₁) → ∀ l, φ P₂ l = φ P₁ (l ∘ₗ (R.cV i).ρ u)) → ∀ P₁ ∈ E, φ P₁ = 0) ∧ P - Q ∈ E := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hgiv _ i t P
  have hC := hgiv.core
  have hinj : Function.Injective (R.ptP i t) := (GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t).2.2
  have hcV : (R.cV i).Is := hC.models.cV i
  haveI : Nontrivial (R.cV i).W := hcV.2.2.2.1
  choose p c U hU hω using fun g : GinfC (Vc D i) => om_ptP_fock D G Pl0 T A Ks R F hC i t g.1 g.2
  let actL : GinfC (Vc D i) → Module.End ℂ (PolF D (Wc D i).rank (Vc D i).rank) :=
    fun g => c g • (GlobalTheory.ExportSeries.fockSubst (p g) (U g)).toLinearMap
  have hact : ∀ g Q, R.ptP i t (actL g Q) = R.ωP i t (g.1, 1) (R.ptP i t Q) := fun g Q => (hω g Q).symm
  have hmul : ∀ g h Q, actL (g * h) Q = actL g (actL h Q) := fun g h Q => hinj (by
    have e : (((g * h : GinfC (Vc D i)) : GA D (Vc D i)), (1 : GA D (Wc D i))) = ((g : GA D (Vc D i)), 1) * ((h : GA D (Vc D i)), 1) := by
      simp
    rw [hact, hact, hact, e, map_mul, Module.End.mul_apply])
  have hone : ∀ Q, actL 1 Q = Q := fun Q => hinj (by
    have e : (((1 : GinfC (Vc D i)) : GA D (Vc D i)), (1 : GA D (Wc D i))) = 1 := by simp
    rw [hact, e, map_one, Module.End.one_apply])
  let S : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank) :=
    MvPolynomial.restrictTotalDegree (FVar D (Wc D i).rank (Vc D i).rank) ℂ P.totalDegree
  have hS : ∀ g, ∀ Q ∈ S, actL g Q ∈ S := fun g Q hQ => by
    rw [MvPolynomial.mem_restrictTotalDegree] at hQ ⊢
    exact (MvPolynomial.totalDegree_smul_le _ _).trans ((totalDegree_fockSubst_le _ _ _).trans hQ)
  letI : InnerProductSpace.Core ℂ S := fisCore S
  letI : NormedAddCommGroup S := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore _
  let actS : GinfC (Vc D i) →* Module.End ℂ S :=
    { toFun := fun g => (actL g).restrict (hS g)
      map_one' := LinearMap.ext fun x => Subtype.ext (hone x.1)
      map_mul' := fun g h => LinearMap.ext fun x => Subtype.ext (hmul g h x.1) }
  have hconf : ∀ g (x y : S), inner ℂ x y = 0 → inner ℂ (actS g x) (actS g y) = 0 := by
    intro g x y h
    change fis (actL g y.1) (actL g x.1) = 0
    change fis y.1 x.1 = 0 at h
    simp only [actL, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
    rw [fis_smul_left, fis_smul_right, fis_fockSubst _ _ _ _ _ (hU g), h, mul_zero, mul_zero]
  let ρ' : GinfC (Vc D i) →* Module.End ℂ (R.cV i).W := (R.cV i).ρ.comp (GinfC (Vc D i)).subtype
  have hirr : ∀ W' : Submodule ℂ (R.cV i).W, (∀ g, W'.map (ρ' g) ≤ W') → W' = ⊥ ∨ W' = ⊤ :=
    fun W' hW => hcV.2.2.2.2 W' fun h => by
      obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
      rw [map_mul, hcV.1 k hk, mul_one]
      exact hW ⟨a, ha⟩
  obtain ⟨q, hq, E, hEst, hEs, hxE⟩ :=
    isotypic_split actS hconf ρ' hirr ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 le_rfl⟩
  refine ⟨q.1, ?_, E.map S.subtype, inferInstance, ?_, ?_, ⟨_, hxE, rfl⟩⟩
  · refine Submodule.span_mono ?_ (Submodule.apply_mem_span_image_of_mem_span S.subtype hq)
    rintro _ ⟨_, ⟨φ, w, hφ, rfl⟩, rfl⟩
    refine ⟨S.subtype ∘ₗ φ, w, fun u hu w' => ?_, rfl⟩
    have e := congrArg Subtype.val (hφ ⟨u, hu⟩ w')
    show R.ptP i t (φ (ρ' ⟨u, hu⟩ w')).1 = R.ωP i t (u, 1) (R.ptP i t (φ w').1)
    rw [e]
    exact hact ⟨u, hu⟩ _
  · rintro u hu _ ⟨e, he, rfl⟩ P₂ h
    have e2 : P₂ = actL ⟨u, hu⟩ e.1 := hinj (h.trans (hact ⟨u, hu⟩ e.1).symm)
    exact ⟨actS ⟨u, hu⟩ e, hEst _ e he, e2.symm⟩
  · intro φ' hφ'
    let ev := Module.evalEquiv ℂ (R.cV i).W
    let φ : S →ₗ[ℂ] (R.cV i).W := ev.symm.toLinearMap ∘ₗ φ' ∘ₗ S.subtype
    have hφe : ∀ x : S, ev (φ x) = φ' x.1 := fun x => ev.apply_symm_apply _
    have key : ∀ g, ∀ e ∈ E, φ (actS g e) = ρ' g (φ e) := by
      intro g e he
      apply ev.injective
      rw [hφe]
      ext l
      have h1 := hφ' g.1 g.2 e.1 ⟨e, he, rfl⟩ (actL g e.1) (hact g e.1) l
      change φ' (actL g e.1) l = _
      rw [h1, ← hφe e]
      rfl
    rintro _ ⟨e, he, rfl⟩
    rw [Submodule.subtype_apply, ← hφe e, hEs φ key e he, map_zero]

end GlobalTheory.FockIsotypic

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_mem_span_lifted_maps : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∀ (P : PolF D (Wc D i).rank (Vc D i).rank), ∃ Q ∈ Submodule.span ℂ {Q : PolF D (Wc D i).rank (Vc D i).rank | ∃ (φ : (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (w : (R.cV i).W), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) ∧ Q = φ w}, ∃ E : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank), FiniteDimensional ℂ E ∧ (∀ u ∈ GinfC (Vc D i), ∀ P₁ ∈ E, ∀ P₂ : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P₂ = R.ωP i t (u, 1) (R.ptP i t P₁) → P₂ ∈ E) ∧ (∀ φ : PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ, (∀ u ∈ GinfC (Vc D i), ∀ P₁ ∈ E, ∀ P₂ : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P₂ = R.ωP i t (u, 1) (R.ptP i t P₁) → ∀ l, φ P₂ l = φ P₁ (l ∘ₗ (R.cV i).ρ u)) → ∀ P₁ ∈ E, φ P₁ = 0) ∧ P - Q ∈ E := by
  atlas_forward_decl GlobalTheory.FockIsotypic.decomp
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.GenByIo

theorem forms_vanish_of_io : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (ι : Type) (B : ι → PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ), (∀ (j : ι) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), R.ptP i t P' = R.ωP i t (u, 1) (R.ptP i t P) → ∀ l, B j P' l = B j P (l ∘ₗ (R.cV i).ρ u)) → (∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) → (∀ j, B j P = 0) → ∀ j, B j P' = 0) → (∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W) (j : ι), B j (R.ioP i x w) = 0) → ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (j : ι), B j P = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t ι B heq hlie hio P j
  let U : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank) := ⨅ j, LinearMap.ker (B j)
  have hU : ∀ P, P ∈ U ↔ ∀ j, B j P = 0 := fun P => by simp [U, Submodule.mem_iInf]
  have hstab : ∀ u ∈ GinfC (Vc D i), ∀ P ∈ U, ∀ P' : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P' = R.ωP i t (u, 1) (R.ptP i t P) → P' ∈ U := by
    intro u hu P hP P' h
    rw [hU] at hP ⊢
    intro j
    ext l
    rw [heq j u hu P P' h l, hP j]
    rfl
  have hlie' : ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) → P ∈ U → P' ∈ U := by
    intro τ Y hY P P' hd hP
    rw [hU] at hP ⊢
    exact hlie τ Y hY P P' hd hP
  have hio' : ∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W), R.ioP i x w ∈ U := fun x w => (hU _).2 (hio x w)
  obtain ⟨Q, hQ, E, -, -, hNo, hPQ⟩ := GlobalTheory.T.polynomial_mem_span_lifted_maps D G Pl0 T A Ks R F hG hF i t P
  have hQU : Q ∈ U := by
    refine Submodule.span_le.2 ?_ hQ
    rintro _ ⟨φ, w, hφ, rfl⟩
    exact GlobalTheory.T.compactHoweDuality_isotypic_mem_of_stable_subspace D G Pl0 T A Ks R F hG hF i t U hstab hlie' hio' φ hφ w
  have hN : B j (P - Q) = 0 :=
    hNo (B j) (fun u hu P₁ _ P₂ h l => heq j u hu P₁ P₂ h l) _ hPQ
  have := (hU Q).1 hQU j
  rw [map_sub, this, sub_zero] at hN
  exact hN

end GlobalTheory.GenByIo
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_bilinearForms_vanish_of_io_generation_real : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (ι : Type) (B : ι → PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ), (∀ (j : ι) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), R.ptP i t P' = R.ωP i t (u, 1) (R.ptP i t P) → ∀ l, B j P' l = B j P (l ∘ₗ (R.cV i).ρ u)) → (∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) → (∀ j, B j P = 0) → ∀ j, B j P' = 0) → (∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W) (j : ι), B j (R.ioP i x w) = 0) → ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (j : ι), B j P = 0 := by
  atlas_forward_decl GlobalTheory.GenByIo.forms_vanish_of_io
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.GenRealFock

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem pureTensor_add (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (P Q : PolF D (Wc D i).rank (Vc D i).rank) :
    R.ptP i t (P + Q) = R.ptP i t P + R.ptP i t Q := by
  unfold RealDat.ptP; exact map_add _ _ _

theorem pureTensor_smul (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (c : ℂ) (P : PolF D (Wc D i).rank (Vc D i).rank) :
    R.ptP i t (c • P) = c • R.ptP i t P := by
  unfold RealDat.ptP; exact map_smul _ _ _

theorem downInt_add_f (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f f' : WO (Vc D i) (Wc D i) → ℂ)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i))
    (hf : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)) (R.fdV i t) (R.νV i t))
    (hf' : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f' * l (R.extV i t y h)) (R.fdV i t) (R.νV i t)) :
    downInt R i t y (f + f') l g = downInt R i t y f l g + downInt R i t y f' l g := by
  unfold downInt
  rw [← integral_add hf hf']
  congr 1
  funext h
  simp only [thetaKO, map_add, Pi.add_apply, add_mul]

theorem downInt_smul_f (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (c : ℂ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) :
    downInt R i t y (c • f) l g = c * downInt R i t y f l g := by
  unfold downInt
  rw [← integral_const_mul]
  congr 1
  funext h
  simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem downInt_add_l (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ)
    (l l' : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i))
    (hf : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)) (R.fdV i t) (R.νV i t))
    (hf' : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l' (R.extV i t y h)) (R.fdV i t) (R.νV i t)) :
    downInt R i t y f (l + l') g = downInt R i t y f l g + downInt R i t y f l' g := by
  unfold downInt
  rw [← integral_add hf hf']
  congr 1
  funext h
  simp only [LinearMap.add_apply, mul_add]

theorem downInt_smul_l (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (c : ℂ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) :
    downInt R i t y f (c • l) g = c * downInt R i t y f l g := by
  unfold downInt
  rw [← integral_const_mul]
  congr 1
  funext h
  simp only [LinearMap.smul_apply, smul_eq_mul]
  ring

theorem exists_bilin (R : RealDat D A Ks) (F : Face D A) (hG : GlobalTheory.LiftRows.Given R F) (hP : R.FullP)
    (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) :
    ∃ B : GA D (Wc D i) → PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ,
      ∀ g P l, B g P l = downInt R i t y (R.ptP i t P) l g := by
  have hth := hG.core.thP.pt_theta i t
  have hint := fun f l g hf => GlobalTheory.T.integrableOn_downwardThetaLift_integrand D G Pl0 T A Ks R F hG hP i t y f l g hf
  refine ⟨fun g => LinearMap.mk₂ ℂ (fun P l => downInt R i t y (R.ptP i t P) l g) ?_ ?_ ?_ ?_, fun g P l => rfl⟩
  · intro P Q l
    rw [pureTensor_add, downInt_add_f _ _ _ _ _ _ _ _ (hint _ l g (hth P)) (hint _ l g (hth Q))]
  · intro c P l
    rw [pureTensor_smul, downInt_smul_f, smul_eq_mul]
  · intro P l l'
    exact downInt_add_l _ _ _ _ _ _ _ _ (hint _ l g (hth P)) (hint _ l' g (hth P))
  · intro c P l
    rw [downInt_smul_l, smul_eq_mul]

theorem gen : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), (∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ptP i t (R.ioP i x w)) l g = 0) → ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ptP i t P) l g = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y hio P l g
  obtain ⟨B, hB⟩ := exists_bilin R F hG hP i t y
  have hth := hG.core.thP.pt_theta i t
  have key := (GlobalTheory.T.equivariant_bilinearForms_vanish_of_io_generation_real) D G Pl0 T A Ks R F hG hP i t (GA D (Wc D i)) B ?_ ?_ ?_ P g
  · rw [← hB, key, LinearMap.zero_apply]
  · intro j u hu P P' e l
    rw [hB, hB, e]
    exact (GlobalTheory.T.downwardThetaLift_real_points_equivariant) D G Pl0 T A Ks R F hG hP i t y u hu _ (hth P) l j
  · intro τ Y hY P P' hd h0 j
    refine LinearMap.ext fun l => ?_
    rw [LinearMap.zero_apply, hB]
    refine (GlobalTheory.T.thetaLift_vanishing_preserved_by_realLieDerivative) D G Pl0 T A Ks R F hG hP i t y τ Y hY P P' hd l (fun g' => ?_) j
    rw [← hB, h0 g', LinearMap.zero_apply]
  · intro x w j
    refine LinearMap.ext fun l => ?_
    rw [LinearMap.zero_apply, hB]
    exact hio x w l j

end GlobalTheory.GenRealFock
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realFockThetaLift_vanishing_of_generating_vectors : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), (∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ptP i t (R.ioP i x w)) l g = 0) → ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ptP i t P) l g = 0 := by
  atlas_forward_decl GlobalTheory.GenRealFock.gen
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.GenReal

theorem genInf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GenInf R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y hy f hf l g
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (D := D) (V := Vc D i) (W := Wc D i)
  have h0 : ∀ P, downInt R i t y (R.ptP i t P) l g = 0 := fun P =>
    GlobalTheory.T.realFockThetaLift_vanishing_of_generating_vectors D G Pl0 T A Ks R F hG hP i t y (GlobalTheory.T.theta_lift_vanishes_single_coefficient_of_kernel_kills D G Pl0 T A Ks R F hG hP i t y hy) P l g
  by_contra hne
  have hpos : 0 < ‖downInt R i t y f l g‖ := norm_pos_iff.2 hne
  obtain ⟨d, δ, hδ, hc⟩ := GlobalTheory.T.downward_theta_integral_sobolev_continuous D G Pl0 T A Ks R F hG hP i t y μ 𝓕 hμ f hf.1 l g _ hpos
  obtain ⟨P, hPd⟩ := GlobalTheory.T.thetaFunction_fixedFinitePart_sobolevLimit_fockVectors D G Pl0 T A Ks R F hG hP i t μ 𝓕 hμ f hf d δ hδ
  have := hc P hPd
  rw [h0 P, sub_zero] at this
  exact lt_irrefl _ this

end GlobalTheory.GenReal
end
