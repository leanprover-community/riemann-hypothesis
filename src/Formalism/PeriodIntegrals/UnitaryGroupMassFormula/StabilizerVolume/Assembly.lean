import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.VolStabFromSWS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExFDStabFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SWeqOm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibInf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnfoldMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.HformSmulRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FinTheta
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnimodStab
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoClose
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabNu
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.OrbTupFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoMuInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PullLocSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExOmTOfSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.NuNeSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.NuNeLam
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SdTestInf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SdDual
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FiniteOnCompacts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RPGlue
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RpAbsHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DetAdm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.AdmCpt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Unimod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensPos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ArchPosHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolDone
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensIdxF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensCnt

section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem volStabFromSW_of (h1 : ExChar) (h2 : ExOmT) (h3 : ExStab) (h4 : ExFDStab)
    (h5 : SWeqOm) (h6 : Unfold) (h7 : PosTest) : PI.VolStabS.VolStabFromSWS := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc hJ' a ha1 ha2 X0 hT hdet
  refine ⟨h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet, fun ψ hψ => ?_⟩
  refine ⟨ha.1, fun μ hμ => ?_⟩
  refine ⟨h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ, fun νX hν => ?_⟩
  refine ⟨h3 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν, fun μ' hμ' => ?_⟩
  obtain ⟨hμ'H, hμ'C⟩ := hμ'
  refine ⟨(ha.2 μ hμ).1, fun 𝓕 h𝓕 => ?_⟩
  refine ⟨h4 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ' hμ'H, fun 𝓕' h𝓕' => ?_⟩
  obtain ⟨φ, hφ0, hadm, hI⟩ := h7 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν μ' hμ'H hμ'C
  have e1 := h5 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν _ hadm
  unfold meanC at e1
  have hθ : ∫ h in 𝓕, thetaS F E σ M J (fun X => (φ X : ℂ))
      {X | gramE σ J X = gramE σ J X0} h ∂μ ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at e1
    exact hI e1.symm
  obtain ⟨hfin, e2⟩ :=
    h6 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν μ' hμ'H hμ'C 𝓕' h𝓕'
      φ hφ0 hadm.adm hθ
  rw [e2, smul_smul] at e1
  have hc1 : (μ 𝓕).toReal⁻¹ * (μ' 𝓕').toReal = 1 := by
    have e3 : ((((μ 𝓕).toReal⁻¹ * (μ' 𝓕').toReal : ℝ)) : ℂ) * ∫ X, (φ X : ℂ) ∂νX =
        1 * ∫ X, (φ X : ℂ) ∂νX := by
      rw [one_mul, ← Complex.real_smul]
      exact e1
    exact_mod_cast mul_right_cancel₀ hI e3
  have h0 : (μ 𝓕).toReal ≠ 0 := by
    intro h0
    rw [h0, inv_zero, zero_mul] at hc1
    exact zero_ne_one hc1
  have e4 : (μ 𝓕).toReal = (μ' 𝓕').toReal := (inv_mul_eq_one₀ h0).1 hc1
  exact (ENNReal.toReal_eq_toReal_iff' hfin ((ha.2 μ hμ).2 𝓕 h𝓕).ne).1 e4.symm

end PI.VolStabS
end
end

section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem exChar_holds : ExChar := by
  intro F E _ _ _ _ _ σ hE M J _hJ _ha hc a _ha1 ha2 _X0 _hT _hdet
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  let b := Module.finBasis F E
  have h0 : 2 * 0 < M := by omega
  have hrd : RapidDecay b (fun _ : Fin 0 → Fin M → Ainf F ⊗[F] E => (1 : ℂ)) :=
    fun N => ⟨1, fun X => by simp [sizeTup]⟩
  have hpf : IsPureFin b (fun _ : Fin 0 → Fin M → Af F ⊗[F] E => (1 : ℂ))
      (fun v (_ : Fin 0 → Fin M → Fv F v ⊗[F] E) => (1 : ℂ)) := by
    refine ⟨fun v => ⟨IsLocallyConstant.const 1, ?_⟩, Filter.Eventually.of_forall fun v => ?_,
      fun X => by simp⟩
    · exact (Set.subsingleton_of_subsingleton).isCompact
    · funext X
      simp [latV, Set.indicator]
  have hS := hc 0 h0 (0 : Matrix (Fin 0) (Fin 0) E) (fun i => Fin.elim0 i) (by simp)
    (Module.finrank F E) b (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ _ => 1)
    continuous_const hrd (Formalism.L2.SG.Pf.NcWeil.isSmoothCc_empty _) hpf (fun _ => by simp)
  obtain ⟨μ, hμ⟩ := hS.1
  obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
  exact ((hS.2 μ hμ).2 𝓕 h𝓕).1

end PI.VolStabS
end
end

section
namespace PI.VolStabS

theorem unfold_holds : Unfold :=
  unfold_of witt_holds finTheta_holds invInv_holds measOrb_holds measGrp_holds

end PI.VolStabS
end

section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem integrable_of_isOmT {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {ψ : AddChar (AF F) ℂ}
    {a : ℕ} {T : Matrix (Fin a) (Fin a) E} {hT : ∀ i j, σ (T j i) = T i j}
    {νX : Measure (Fin a → Fin M → AF F ⊗[F] E)} (hν : IsOmT F E σ M J ψ T hT νX)
    {Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ} (hΦ : IsAdm F E Φ) : Integrable Φ νX := by
  obtain ⟨d, b, Φinf, Φf, Φv, hc, hcs, hpf, hprod⟩ := hΦ
  obtain ⟨μinf, h1⟩ := hν.2.1
  have k1 := hν.2.2 μinf h1
  obtain ⟨νinf, h2⟩ := k1.1
  have k2 := k1.2 νinf h2
  obtain ⟨μv, h3⟩ := k2.1
  have k3 := k2.2 μv h3
  obtain ⟨νv, h4⟩ := k3.1
  have k4 := k3.2 νv h4
  obtain ⟨fibInf, h5⟩ := k4.1
  have k5 := k4.2 fibInf h5
  obtain ⟨fibV, h6⟩ := k5.1
  exact (k5.2 fibV h6 d b Φ Φinf Φf Φv hc hcs hpf hprod).1

theorem posTest_of (hN : TestNear) : PosTest := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ _hψ μ hμ νX hν μ' _hμ' hC
  obtain ⟨φ, hφ0, hadm, U, hUo, hUne, hUpos⟩ := hN F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  refine ⟨φ, hφ0, hadm, fun hI0 => ?_⟩
  have hint : Integrable (fun X => (φ X : ℂ)) νX := integrable_of_isOmT hν hadm.adm
  have hintR : Integrable φ νX := by simpa using hint.re
  have hI : ∫ X, φ X ∂νX = 0 := by
    rw [integral_complex_ofReal] at hI0
    exact_mod_cast hI0
  have hae : φ =ᵐ[νX] 0 := (integral_eq_zero_iff_of_nonneg (fun X => hφ0 X) hintR).1 hI
  obtain ⟨hnull, hform⟩ := hC
  classical
  let s : (Fin a → Fin M → AF F ⊗[F] E) → HA (AF F) σ J := fun y =>
    if h : ∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y then h.choose else 1
  have hs : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y) →
      s y • ratTup (AF F) X0 = y := by
    intro y h
    simp only [s, dif_pos h]
    exact h.choose_spec
  have hf : Measurable (U.indicator (1 : HA (AF F) σ J → ENNReal)) :=
    measurable_one.indicator hUo.measurableSet
  have e := hform _ hf s hs
  have hL : ∫⁻ g, U.indicator (1 : HA (AF F) σ J → ENNReal) g ∂μ = μ U :=
    lintegral_indicator_one hUo.measurableSet
  have : μ.IsHaarMeasure := hμ
  have hpos : 0 < μ U := hUo.measure_pos μ hUne
  have hR : ∫⁻ y, ∫⁻ h', U.indicator (1 : HA (AF F) σ J → ENNReal)
      (s y * (h' : HA (AF F) σ J)) ∂μ' ∂νX = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hae, ae_iff.2 hnull] with y hy0 hyo
    simp only [Pi.zero_apply] at hy0
    have hz : ∀ h' : stabT (AF F) σ J X0,
        U.indicator (1 : HA (AF F) σ J → ENNReal) (s y * (h' : HA (AF F) σ J)) = 0 := by
      intro h'
      refine Set.indicator_apply_eq_zero.2 fun hm => ?_
      exfalso
      have hh : (h' : HA (AF F) σ J) • ratTup (AF F) X0 = ratTup (AF F) X0 := h'.2
      have h0 := hUpos _ hm
      rw [mul_smul, hh, hs y hyo, hy0] at h0
      exact lt_irrefl _ h0
    simp only [hz, lintegral_zero]
  rw [hL, hR] at e
  exact hpos.ne' e

theorem posTest_holds : PosTest := posTest_of testNear_holds

end PI.VolStabS
end
end

section
noncomputable section

namespace PI.VolStabS

theorem exStab_of_orb (hO : OrbTup) (hI : NuInv) (hF : NuFin) (hN : NuNeZero) : ExStab :=
  exStab_of_U secCtblW_holds lcscPolish_holds hO hI hF hN

end PI.VolStabS
end
end

section
namespace PI.VolStabS

theorem exStab_of_nu (hI : NuInv) (hF : NuFin) (hN : NuNeZero) : ExStab :=
  exStab_of_orb orbTup_holds hI hF hN

end PI.VolStabS
end

section
noncomputable section

namespace PI.VolStabS

namespace CompGAux

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.VolStabS.FiniteThetaCoordinates
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem tmap_sigR (φ : R →ₐ[F] S) (x : R ⊗[F] E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (sigR R σ x) =
      sigR S σ (Algebra.TensorProduct.map φ (AlgHom.id F E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tmap_inclR (φ : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR, Algebra.TensorProduct.map_tmul]

theorem map_mem_HR (φ : R →ₐ[F] S) {g : GL (Fin M) (R ⊗[F] E)} (hg : g ∈ HR R σ J) :
    Formalism.UG.bc (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom g ∈ HR S σ J := by
  set ψ : R ⊗[F] E →+* S ⊗[F] E := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
  have hg' : Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := hg
  have hcT : (Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))).map ψ =
      Formalism.UG.cT (sigR S σ) ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map ψ) := by
    ext i j
    simp [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, ψ, tmap_sigR]
  have hJ : (JR R J).map ψ = JR S J := by
    ext i j
    simp [JR, Matrix.map_apply, ψ, tmap_inclR]
  show Formalism.UG.cT (sigR S σ) ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map ψ) * JR S J *
      (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map ψ = JR S J
  rw [← hcT, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg']

def haMap (φ : R →ₐ[F] S) : HA R σ J →* HA S σ J :=
  MonoidHom.codRestrict
    ((Formalism.UG.bc (n := Fin M) (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom).comp
      (HR R σ J).subtype) (HR S σ J) (fun h => map_mem_HR σ J φ h.2)

theorem mat_haMap_apply (φ : R →ₐ[F] S) (h : HA R σ J) (i j : Fin M) :
    ((HA.mat S σ J (haMap σ J φ h) : GL (Fin M) (S ⊗[F] E)) : Matrix (Fin M) (Fin M) _) i j =
      Algebra.TensorProduct.map φ (AlgHom.id F E)
        (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) i j) := rfl

theorem map_smul_tup (φ : R →ₐ[F] S) {n : ℕ} (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E) :
    (fun x i => Algebra.TensorProduct.map φ (AlgHom.id F E) ((h • X) x i)) =
      haMap σ J φ h • (fun x i => Algebra.TensorProduct.map φ (AlgHom.id F E) (X x i)) := by
  funext x i
  show Algebra.TensorProduct.map φ (AlgHom.id F E)
      ((((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec (X x)) i) =
    (((HA.mat S σ J (haMap σ J φ h) : GL (Fin M) (S ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec
      (fun j => Algebra.TensorProduct.map φ (AlgHom.id F E) (X x j))) i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, mat_haMap_apply]

theorem tmap_comp {T : Type} [CommRing T] [Algebra F T] (f : R →ₐ[F] S) (g : S →ₐ[F] T)
    (y : R ⊗[F] E) :
    Algebra.TensorProduct.map g (AlgHom.id F E) (Algebra.TensorProduct.map f (AlgHom.id F E) y) =
      Algebra.TensorProduct.map (g.comp f) (AlgHom.id F E) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Gen

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem crd_mulVec_mem (v : HeightOneSpectrum (𝓞 F)) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (m : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) (y : Fin M → Fv F v ⊗[F] E)
    (hm : ∀ i j p, crd b (Fv F v) (m i j) p ∈ v.adicCompletionIntegers F)
    (hy : ∀ j q, crd b (Fv F v) (y j) q ∈ v.adicCompletionIntegers F)
    (hc : ∀ p q k, algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F)
    (i : Fin M) (k : Fin d) : crd b (Fv F v) ((m.mulVec y) i) k ∈ v.adicCompletionIntegers F := by
  rw [crd_mulVec]
  exact sum_mem fun j _ => sum_mem fun p _ => sum_mem fun q _ =>
    mul_mem (mul_mem (hm i j p) (hy j q)) (hc p q k)

theorem smul_mem_latV (v : HeightOneSpectrum (𝓞 F)) {d a : ℕ} (b : Module.Basis (Fin d) F E)
    (h : HA (Fv F v) σ J)
    (hm : ∀ i j p, crd b (Fv F v)
      (((HA.mat (Fv F v) σ J h : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p ∈
        v.adicCompletionIntegers F)
    (hc : ∀ p q k, algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F)
    (Y : Fin a → Fin M → Fv F v ⊗[F] E) (hY : Y ∈ latV b v) : h • Y ∈ latV b v := by
  simp only [latV, Set.mem_ofPred_eq] at hY ⊢
  intro x i k
  exact crd_mulVec_mem v b _ (Y x) hm (fun j q => hY x j q) hc i k

theorem eventually_int (g : HA (AF F) σ J) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, ∀ i j p, piV F v (crd b (AF F)
      (((HA.mat (AF F) σ J g : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p) ∈
        v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  intro i j p
  exact (eventually_piV_le_one F _).mono fun v hv => (norm_le_one_iff_mem F v _).1 hv

theorem eventually_struct {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, ∀ p q k,
      algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  intro p q k
  refine (eventually_piV_le_one F (algebraMap F (AF F) (b.repr (b p * b q) k))).mono fun v hv => ?_
  rw [AlgHom.commutes] at hv
  exact (norm_le_one_iff_mem F v _).1 hv

theorem compG_gen (a : ℕ) (g : HA (AF F) σ J) :
    ∃ (hInf : HA (Ainf F) σ J) (hv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J),
    (∀ X : Fin a → Fin M → AF F ⊗[F] E, projInf (g • X) = hInf • projInf X) ∧
    (∀ (v : HeightOneSpectrum (𝓞 F)) (X : Fin a → Fin M → AF F ⊗[F] E),
      projV v (projFin (g • X)) = hv v • projV v (projFin X)) ∧
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in Filter.cofinite,
      ∀ Y : Fin a → Fin M → Fv F v ⊗[F] E, hv v • Y ∈ latV b v ↔ Y ∈ latV b v := by
  refine ⟨haMap σ J (fstA F) g, fun v => haMap σ J (piV F v) g, ?_, ?_, ?_⟩
  · intro X
    exact map_smul_tup σ J (fstA F) g X
  · intro v X
    have e : ∀ Z : Fin a → Fin M → AF F ⊗[F] E, projV v (projFin Z) =
        fun x i => Algebra.TensorProduct.map (piV F v) (AlgHom.id F E) (Z x i) := by
      intro Z
      funext x i
      exact tmap_comp (sndA F) (evalV F v) (Z x i)
    rw [e, e, map_smul_tup]
  · intro d b
    filter_upwards [eventually_int σ J g b, eventually_int σ J g⁻¹ b, eventually_struct b]
      with v h1 h2 h3
    have hm : ∀ g' : HA (AF F) σ J, (∀ i j p, piV F v (crd b (AF F)
        (((HA.mat (AF F) σ J g' : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p) ∈
          v.adicCompletionIntegers F) → ∀ i j p, crd b (Fv F v)
        (((HA.mat (Fv F v) σ J (haMap σ J (piV F v) g') : GL (Fin M) _) :
          Matrix (Fin M) (Fin M) _) i j) p ∈ v.adicCompletionIntegers F := by
      intro g' hg' i j p
      rw [mat_haMap_apply, crd_map]
      exact hg' i j p
    intro Y
    constructor
    · intro hY
      have := smul_mem_latV σ J v b (haMap σ J (piV F v) g⁻¹) (hm g⁻¹ h2) h3 _ hY
      rwa [map_inv, inv_smul_smul] at this
    · intro hY
      exact smul_mem_latV σ J v b (haMap σ J (piV F v) g) (hm g h1) h3 Y hY

end Loc

end CompGAux

theorem compG_holds : CompG := by
  intro F E _ _ _ _ _ σ _hCM M J _hJ _ha _hc a _ha1 _ha2 _X0 _hT _hdet g
  exact CompGAux.compG_gen σ J a g

end PI.VolStabS
end
end

section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise



end PI.VolStabS
end
end

section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise



end PI.VolStabS
end
end

section
namespace PI.VolStabS


end PI.VolStabS
end

section
noncomputable section

namespace PI.VolStabS

open NumberField IsDedekindDomain Filter Asymptotics
open scoped nonZeroDivisors

namespace LocalCountingSum

variable (K : Type) [Field K] [NumberField K]

def cnt (n : ℕ) : ℝ := (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ)

theorem sum_cnt (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, cnt K k =
    (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) := by
  induction n with
  | zero =>
    have hE : IsEmpty {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ 0} := by
      constructor
      rintro ⟨I, hI⟩
      have h0 : Ideal.absNorm (I : Ideal (𝓞 K)) = 0 := Nat.le_zero.1 hI
      rw [Ideal.absNorm_eq_zero_iff] at h0
      exact (mem_nonZeroDivisors_iff_ne_zero.1 I.2) (by rw [h0]; rfl)
    rw [Nat.card_of_isEmpty]
    simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    haveI : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} := (Ideal.finite_setOf_absNorm_le₀ (S := 𝓞 K) n).to_subtype
    haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n + 1} :=
      (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) (n + 1)).to_subtype
    have hnz : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n + 1 → I ∈ (Ideal (𝓞 K))⁰ := by
      intro I hI
      refine mem_nonZeroDivisors_iff_ne_zero.2 (fun h => ?_)
      rw [h] at hI
      simp at hI
    let e : {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n + 1} ≃ {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} ⊕ {I : Ideal (𝓞 K) // Ideal.absNorm I = n + 1} :=
      { toFun := fun x => if h : Ideal.absNorm (x.1 : Ideal (𝓞 K)) ≤ n then Sum.inl ⟨x.1, h⟩
          else Sum.inr ⟨x.1.1, by have := x.2; omega⟩
        invFun := fun y => match y with
          | Sum.inl z => ⟨z.1, Nat.le_succ_of_le z.2⟩
          | Sum.inr z => ⟨⟨z.1, hnz z.1 z.2⟩, z.2.le⟩
        left_inv := by
          intro x
          by_cases h : Ideal.absNorm (x.1 : Ideal (𝓞 K)) ≤ n
          · simp only [dif_pos h]
          · simp only [dif_neg h]
        right_inv := by
          intro y
          rcases y with z | z
          · simp only [dif_pos z.2]
          · have hz : ¬ Ideal.absNorm z.1 ≤ n := by have := z.2; omega
            simp only [dif_neg hz] }
    rw [Nat.card_congr e, Nat.card_sum]
    unfold cnt
    push_cast
    ring

theorem sum_cnt_bigO :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, cnt K k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  have h2 := (NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop
  have hc : ∀ n : ℕ, (Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ (n : ℝ)} : ℝ) =
      (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) := by
    intro n
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun I => Nat.cast_le))
  simp only [Real.rpow_one]
  obtain ⟨L, hL⟩ : ∃ L, Tendsto ((fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, cnt K k) / fun n : ℕ => (n : ℝ))
      atTop (nhds L) :=
    ⟨_, h2.congr (fun n => by simp only [Function.comp_apply, Pi.div_apply, hc n, sum_cnt K n])⟩
  exact Asymptotics.isBigO_of_div_tendsto_nhds
    (Filter.eventually_atTop.2 ⟨1, fun n hn h0 => absurd h0 (by positivity)⟩) L hL

theorem cnt_summable : Summable fun n : ℕ ↦ cnt K n / (n : ℝ) ^ 2 := by
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := cnt K) (r := 1) (s := 2) (sum_cnt_bigO K)
    (fun n => by unfold cnt; positivity) zero_le_one (by norm_num)
  unfold LSeriesSummable at h
  have e : LSeries.term (fun n => ((cnt K n : ℝ) : ℂ)) 2 = fun n => ((cnt K n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn.ne']
      push_cast
      congr 1
      exact_mod_cast Complex.cpow_natCast (n : ℂ) 2
  rw [e] at h
  exact Complex.summable_ofReal.1 h

end LocalCountingSum

theorem qV_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    qV v = (Ideal.absNorm v.asIdeal : ℝ) := by
  unfold qV
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem qvSum_holds : QvSum := by
  intro F _ _
  haveI hfin : ∀ n : ℕ, Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
    fun n => (Ideal.finite_setOf_absNorm_eq (S := 𝓞 F) n).to_subtype
  let f : Ideal (𝓞 F) → ℝ := fun I => ((Ideal.absNorm I : ℝ))⁻¹ ^ 2
  have hf0 : ∀ I, 0 ≤ f I := fun I => by positivity
  have hsig : Summable (fun x : Σ n : ℕ, {I : Ideal (𝓞 F) // Ideal.absNorm I = n} => f x.2.1) := by
    rw [summable_sigma_of_nonneg (fun x => hf0 _)]
    refine ⟨fun n => Summable.of_finite, ?_⟩
    have e2 : (fun n : ℕ => ∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}, f I.1) =
        fun n => LocalCountingSum.cnt F n / (n : ℝ) ^ 2 := by
      funext n
      have hc : ∀ I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}, f I.1 = ((n : ℝ))⁻¹ ^ 2 := by
        intro I
        simp only [f, I.2]
      rw [tsum_congr hc, tsum_const, nsmul_eq_mul]
      unfold LocalCountingSum.cnt
      rw [inv_pow, div_eq_mul_inv]
    rw [e2]
    exact LocalCountingSum.cnt_summable F
  have hI : Summable f := (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 F) => Ideal.absNorm I)).summable_iff.1 hsig
  have hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) :=
    fun v w h => HeightOneSpectrum.ext h
  refine (hI.comp_injective hinj).congr (fun v => ?_)
  simp only [Function.comp_apply, f, qV_eq]

end PI.VolStabS
end
end

section
namespace PI.VolStabS

theorem restrProd_holds : RestrProd :=
  restrProd_of rpAbs_holds rpFib_holds rpGlue_holds RestrProdG.rpGram_holds
    RestrProdA.rpTail_holds RestrProdA.latCofin_holds

end PI.VolStabS
end

section
noncomputable section

namespace PI.VolStabS.InvariantStabilizerAssembly

open PI.VolStabS MeasureTheory Measure Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.VolFromSW
open scoped TensorProduct



end PI.VolStabS.InvariantStabilizerAssembly
end
end

section
noncomputable section

namespace PI.VolStabS.OrbProperW

open PI.VolStabS Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
  PI.VolFromSW Set Topology
open scoped TensorProduct Pointwise

section Abstract

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SigmaCompactSpace G]
  [MulAction G X] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [ContinuousSMul G X]

theorem orbMk (x0 : X) (k : G) :
    ((k : G ⧸ MulAction.stabilizer G x0)).out • x0 = k • x0 := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (MulAction.stabilizer G x0) k
  rw [hh, mul_smul, (MulAction.mem_stabilizer_iff.1 h.2)]

theorem orbInj (x0 : X) :
    Function.Injective (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) := by
  intro q q' h
  simp only at h
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
    MulAction.mem_stabilizer_iff, mul_smul, ← h, inv_smul_smul]

theorem orbit_proper (x0 : X) (hcl : IsClosed (MulAction.orbit G x0)) (K : Set X)
    (hK : IsCompact K) :
    IsCompact ((fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) ⁻¹' K) := by
  let O := MulAction.orbit G x0
  have : LocallyCompactSpace O := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : ContinuousSMul G O := ⟨continuous_induced_rng.2
    (continuous_smul.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩
  let o0 : O := ⟨x0, MulAction.mem_orbit_self x0⟩
  have hopen : IsOpenMap (fun g : G => g • o0) := isOpenMap_smul_of_sigmaCompact o0
  let φ : G ⧸ MulAction.stabilizer G x0 → O := fun q => ⟨q.out • x0, MulAction.mem_orbit x0 q.out⟩
  have hφmk : ∀ g : G, φ (g : G ⧸ MulAction.stabilizer G x0) = g • o0 := fun g =>
    Subtype.ext (orbMk x0 g)
  have hφc : Continuous φ := by
    rw [(QuotientGroup.isQuotientMap_mk (MulAction.stabilizer G x0)).continuous_iff]
    have : φ ∘ QuotientGroup.mk = fun g : G => g • o0 := funext hφmk
    rw [this]
    exact continuous_id.smul continuous_const
  have hφo : IsOpenMap φ := by
    intro U hU
    have : φ '' U = (fun g : G => g • o0) '' (QuotientGroup.mk ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        refine ⟨q.out, ?_, ?_⟩
        · simp only [mem_preimage, QuotientGroup.out_eq']
          exact hq
        · show q.out • o0 = φ q
          rw [← hφmk q.out, QuotientGroup.out_eq']
      · rintro ⟨g, hg, rfl⟩
        exact ⟨_, hg, hφmk g⟩
    rw [this]
    exact hopen _ (hU.preimage QuotientGroup.continuous_mk)
  have hφi : Function.Injective φ := fun q q' h => orbInj (G := G) x0 (congrArg Subtype.val h)
  have hφs : Function.Surjective φ := by
    rintro ⟨y, g, rfl⟩
    exact ⟨(g : G ⧸ MulAction.stabilizer G x0), hφmk g⟩
  let e : (G ⧸ MulAction.stabilizer G x0) ≃ₜ O :=
    (Equiv.ofBijective φ ⟨hφi, hφs⟩).toHomeomorphOfContinuousOpen hφc hφo
  have hpre : (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) ⁻¹' K =
      e ⁻¹' (Subtype.val ⁻¹' K) := Set.ext fun q => Iff.rfl
  rw [hpre, e.isCompact_preimage]
  exact hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK

end Abstract

theorem orbProper_holds : OrbProper := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet K hK
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have : SigmaCompactSpace (HA (AF F) σ J) := um_sigmaCompact_HA F E σ M J ha
  have : ContinuousSMul (HA (AF F) σ J) (Fin a → Fin M → AF F ⊗[F] E) := by
    refine ⟨?_⟩
    have hmat : Continuous (fun g : HA (AF F) σ J =>
        ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) :=
      Units.continuous_val.comp continuous_subtype_val
    show Continuous (fun p : HA (AF F) σ J × (Fin a → Fin M → AF F ⊗[F] E) =>
      actTup (AF F) (HA.mat (AF F) σ J p.1) p.2)
    unfold actTup
    exact continuous_pi fun i => (hmat.comp continuous_fst).matrix_mulVec
      ((continuous_apply i).comp continuous_snd)
  have hgp := gramPres_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have hot := orbTup_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have horb : MulAction.orbit (HA (AF F) σ J) (ratTup (F := F) (AF F) X0) =
      (fun y => gramR (AF F) σ J y) ⁻¹' {(gramE σ J X0).map (inclR (AF F))} := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      simp only [mem_preimage, mem_singleton_iff]
      show gramR (AF F) σ J (g • ratTup (F := F) (AF F) X0) = _
      rw [hgp, LocPosW.gramR_ratTup]
    · intro hy
      obtain ⟨g, hg⟩ := hot y hy
      exact ⟨g, hg⟩
  have hcl : IsClosed (MulAction.orbit (HA (AF F) σ J) (ratTup (F := F) (AF F) X0)) := by
    rw [horb]
    exact isClosed_singleton.preimage (continuous_gramR (AF F) σ J)
  exact orbit_proper (G := HA (AF F) σ J) (ratTup (F := F) (AF F) X0) hcl K hK

end PI.VolStabS.OrbProperW
end
end

section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter Topology Set LocPosW
open scoped TensorProduct ENNReal

theorem locPos_holds : LocPos := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ νv hν fibV hfib
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := hμ.1
  have := hν.1
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ :=
    (tensAll_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet).2 v
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : LocallyCompactSpace (HermR (Fv F v) σ a) :=
    t4.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (HermR (Fv F v) σ a) :=
    have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
    Topology.IsInducing.subtypeVal.secondCountableTopology
  let b := Module.finBasis F E
  set X1 := ratTup (F := F) (Fv F v) X0 with hX1
  set T := hermOf (Fv F v) σ (gramE σ J X0) hT with hTdef
  have hgT : gramH (Fv F v) σ hσ J hJ.1 X1 = T := Subtype.ext (gramR_ratTup (Fv F v) σ J X0)
  have hX1U : LinearIndependent (Fv F v ⊗[F] E) X1 :=
    linIndep_of_isUnit_det (Fv F v) σ J X1
      (by rw [gramR_ratTup]; exact isUnit_det_hermOf (Fv F v) σ _ hT hdet)
  obtain ⟨N, hN, hd⟩ := gramFilt_of (dxOpen_of secGram_holds) F E σ hσ M J hJ.1 hJ.2 a ha1 (by omega) v
    _ b X1 hX1U
  obtain ⟨Λ0, hB, hΛ0o, hΛ0c, hsub⟩ := isCOBasis_latSub b v a M N hN
  obtain ⟨Λ, H, D, h0, hΛo, hΛc, hΛa, hHo, hHc, hHb, hD, hyp⟩ :=
    hd X1 (by rw [sub_self]; exact mem_of_mem_nhds hN) Λ0 hB hsub
  let Nb : Set (HermR (Fv F v) σ a) :=
    {S | IsUnit (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)).det}
  have hNb : Nb ∈ 𝓝 T :=
    (isOpen_unitHerm (Fv F v) (isOpen_units_Fv F v) σ a).mem_nhds
      (isUnit_det_hermOf (Fv F v) σ _ hT hdet)
  have hval := fibCos μv νv (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective
    (gramH (Fv F v) σ hσ J hJ.1) (continuous_gramH (Fv F v) σ hσ J hJ.1) (fun _ => rfl)
    _ Set.univ fibV hfib T Filter.univ_mem Nb hNb
    (fun X hX => linIndep_of_isUnit_det (Fv F v) σ J X hX) Λ H hΛo hΛc hΛa hHo hHc hHb D hD X1
    hyp (by rw [hgT, sub_self]; exact zero_mem _)
  have hΛ0pos : μv (Λ 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ≠ 0 :=
    ((hΛo 0).measure_pos μv ⟨0, zero_mem _⟩).ne'
  have hΛ0fin : μv (Λ 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ≠ ⊤ :=
    ((hΛc 0).measure_lt_top).ne
  have hH0pos : νv (H 0 : Set (HermR (Fv F v) σ a)) ≠ 0 :=
    ((hHo 0).measure_pos νv ⟨0, zero_mem _⟩).ne'
  have hH0fin : νv (H 0 : Set (HermR (Fv F v) σ a)) ≠ ⊤ := ((hHc 0).measure_lt_top).ne
  have hQo : IsOpen {x | x - X1 ∈ Λ 0} := (hΛo 0).preimage (continuous_id.sub continuous_const)
  have hQcl : IsClosed {x | x - X1 ∈ Λ 0} :=
    (AddSubgroup.isClosed_of_isOpen _ (hΛo 0)).preimage (continuous_id.sub continuous_const)
  have hQc : IsCompact {x | x - X1 ∈ Λ 0} := by
    have e : {x | x - X1 ∈ Λ 0} = (fun w => w + X1) '' (Λ 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) := by
      ext z
      simp only [mem_ofPred_eq, mem_image, SetLike.mem_coe]
      constructor
      · intro hz
        exact ⟨z - X1, hz, by abel⟩
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
    rw [e]
    exact (hΛc 0).image (continuous_id.add continuous_const)
  refine ⟨{x | x - X1 ∈ Λ 0}.indicator 1, ⟨(LocallyConstant.indicator
    (LocallyConstant.const _ (1 : ℂ)) ⟨hQcl, hQo⟩).isLocallyConstant,
    HasCompactSupport.intro' hQc hQcl fun Y hY => Set.indicator_of_notMem hY _⟩, ?_⟩
  rw [hval]
  have hr : 0 < (μv (Λ 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) /
      νv (H 0 : Set (HermR (Fv F v) σ a))).toReal :=
    ENNReal.toReal_pos (ENNReal.div_pos_iff.2 ⟨hΛ0pos, hH0fin⟩).ne'
      (ENNReal.div_ne_top hΛ0fin hH0pos)
  exact_mod_cast hr.ne'

end PI.VolStabS
end
end

section
namespace PI.VolStabS.Assembly

open PI.VolStabS

theorem fibPin_closed : FibPin := fibPin_holds

theorem sWeqOm_closed : SWeqOm := sWeqOm_of densFibInf_holds densFibV_holds

theorem sdUniq_closed : SdUniq :=
  sdUniq_of_inf sdTestInf_holds

theorem exOmT_holds : ExOmT :=
  exOmT_of_open (fibInfEx_of DiscreteGroups.fibOfDens_holds tensAll_holds densInf_holds)
    (fibVEx_of DiscreteGroups.fibOfDens_holds tensAll_holds densV_holds) sdUniq_closed restrProd_holds

theorem nuInv_holds : NuInv := nuInv_of_pin detAdm_holds compG_holds fibPin_closed sdUniq_closed

theorem volStabFromSW_of_nuNe (hN : NuNeZero) : PI.VolStabS.VolStabFromSWS := volStabFromSW_of exChar_holds exOmT_holds (exStab_of_nu nuInv_holds nuFin_holds hN)
    exFDStab_holds sWeqOm_closed unfold_holds posTest_holds



theorem volStabFromSW_of_open_dens (hDA : DensAA) : PI.VolStabS.VolStabFromSWS := volStabFromSW_of_nuNe (nuNeZero_of_dens archPos_holds locPos_holds hDA qvSum_holds)

theorem volStabFromSW_of_open_aa (hV : VolAA) (hH : HensAA) (hI : IdxH) (hC : CntAA) :
    PI.VolStabS.VolStabFromSWS := volStabFromSW_of_open_dens (densAA_of_open hV hH hI hC)

theorem volStabFromSW_of_open_vic (hV : VolAA) (hI : IdxH) (hC : CntAA) :
    PI.VolStabS.VolStabFromSWS := volStabFromSW_of_open_aa hV hensAA_holds hI hC

theorem volStabFromSW_of_open_ic (hI : IdxH) (hC : CntAA) : PI.VolStabS.VolStabFromSWS := volStabFromSW_of_open_vic volAA_holds hI hC

theorem volStabFromSW_of_cntAA (hC : CntAA) : PI.VolStabS.VolStabFromSWS := volStabFromSW_of_open_ic idxH_holds hC

theorem volStabFromSW_holds : PI.VolStabS.VolStabFromSWS := volStabFromSW_of_cntAA cntAA_holds

end PI.VolStabS.Assembly
end
