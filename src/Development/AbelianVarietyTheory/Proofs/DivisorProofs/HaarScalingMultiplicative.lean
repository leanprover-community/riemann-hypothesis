import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DistribHaarCharTransport

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

open scoped GroundTheory.Global.AdeleBaseChange NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.IdeleLogHom

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange

section Transfer

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def toE : (AE F E)ˣ →* IdeleGroup E :=
  Units.map (adeleTensorAlgEquivLeft F E : AE F E →ₐ[AF F] AdeleRing (𝓞 E) E).toMonoidHom

def ofE : IdeleGroup E →* (AE F E)ˣ :=
  Units.map ((adeleTensorAlgEquivLeft F E).symm : AdeleRing (𝓞 E) E →ₐ[AF F] AE F E).toMonoidHom

theorem ofE_toE (x : (AE F E)ˣ) : ofE F E (toE F E x) = x := by
  ext
  simp [ofE, toE]

theorem continuous_ofE : Continuous (ofE F E) := by
  have : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  have : IsModuleTopology (AF F) (AdeleRing (𝓞 E) E) := isModuleTopology_adeleRing
  exact Continuous.units_map _
    (IsModuleTopology.continuous_of_linearMap (adeleTensorAlgEquivLeft F E).symm.toLinearMap)

theorem toE_inclR (γ : Eˣ) :
    toE F E (Units.map (inclR (F := F) (AF F)).toMonoidHom γ) = IdeleGroup.diagonal E γ := by
  ext
  simp [toE, inclR, adeleTensorAlgEquivLeft_tmul, IdeleGroup.coe_diagonal]

theorem absE_eq_ideleModule (x : (AE F E)ˣ) :
    (absE F E x : ℝ) = (IdeleGroup.ideleModule E (toE F E x) : ℝ) := by
  rw [← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F), ← GlobalTheory.ModuAdele.modu_norm_eq_absE]
  have h2 : ∀ u : (AF F)ˣ, (((adeleClass F).modu u : ℝ≥0) : ℝ) = (IdeleGroup.ideleModule F u : ℝ) := fun u => by
    change (distribHaarChar (AdeleRing (𝓞 F) F) u : ℝ) = _
    exact GlobalTheory.ModuAdele.distribHaarChar_adeleRing F u
  have h3 : Units.map (Algebra.norm (AF F) : AE F E →* AF F) x = ideleNorm F E (toE F E x) := by
    ext
    simp [toE, ideleNorm, Algebra.norm_eq_of_algEquiv]
  rw [h2, h3]

end Transfer

section OnE

variable {E : Type} [Field E] [NumberField E]

theorem map_pow_eq (ψ : IdeleGroup E → ℂ) (hadd : ∀ s t, ψ (s * t) = ψ s + ψ t) (y : IdeleGroup E) (n : ℕ) :
    ψ (y ^ n) = n * ψ y := by
  induction n with
  | zero =>
    have h := hadd 1 1
    rw [mul_one] at h
    simpa using h
  | succ n ih => rw [pow_succ, hadd, ih]; push_cast; ring

theorem eq_zero_of_mem_normOne (ψ : IdeleGroup E → ℂ) (hψ : Continuous ψ) (hadd : ∀ s t, ψ (s * t) = ψ s + ψ t)
    (hE : ∀ γ : Eˣ, ψ (IdeleGroup.diagonal E γ) = 0) {y : IdeleGroup E} (hy : y ∈ IdeleGroup.normOneSubgroup E) :
    ψ y = 0 := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup E
  obtain ⟨M, hM⟩ := (hD.image hψ).isBounded.exists_norm_le
  have hb : ∀ z ∈ IdeleGroup.normOneSubgroup E, ‖ψ z‖ ≤ M := fun z hz => by
    obtain ⟨k, hk⟩ := hxD z hz
    have := hM _ ⟨_, hk, rfl⟩
    rwa [hadd, hE, zero_add] at this
  by_contra hne
  have hpos : 0 < ‖ψ y‖ := norm_pos_iff.2 hne
  obtain ⟨n, hn⟩ := exists_nat_gt (M / ‖ψ y‖)
  have h1 := hb _ (pow_mem hy n)
  rw [map_pow_eq ψ hadd, norm_mul, Complex.norm_natCast] at h1
  rw [div_lt_iff₀ hpos] at hn
  linarith

theorem exists_log_of_ideleGroup (ψ : IdeleGroup E → ℂ) (hψ : Continuous ψ) (hadd : ∀ s t, ψ (s * t) = ψ s + ψ t)
    (hE : ∀ γ : Eˣ, ψ (IdeleGroup.diagonal E γ) = 0) :
    ∃ A : ℂ, ∀ y, ψ y = A * (Real.log (IdeleGroup.ideleModule E y : ℝ) : ℂ) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  let s := moduleSection w
  have h1 : ψ 1 = 0 := by
    have h := hadd 1 1
    rw [mul_one] at h
    linear_combination -h
  let e : ℝ → {r : ℝ // 0 < r} := fun u => ⟨Real.exp u, Real.exp_pos u⟩
  let fA : ℝ →+ ℂ :=
    { toFun := fun u => ψ (s (e u))
      map_zero' := by
        have : e 0 = 1 := Subtype.ext Real.exp_zero
        simp only [this, map_one, h1]
      map_add' := fun u v => by
        have : e (u + v) = e u * e v := Subtype.ext (Real.exp_add u v)
        simp only [this, map_mul, hadd] }
  have hfc : Continuous fA :=
    hψ.comp ((continuous_moduleSection w).comp (Real.continuous_exp.subtype_mk _))
  let L := fA.toRealLinearMap hfc
  have hL : ∀ u : ℝ, fA u = u * fA 1 := fun u => by
    have h := L.map_smul u 1
    simp only [smul_eq_mul, mul_one, Complex.real_smul, L, AddMonoidHom.coe_toRealLinearMap] at h
    exact h
  refine ⟨fA 1, fun y => ?_⟩
  set r := IdeleGroup.ideleModule E y with hr
  have hsplit : y = (y * (s r)⁻¹) * s r := by group
  have hr' : e (Real.log r) = r := Subtype.ext (Real.exp_log r.2)
  have hz : ψ (y * (s r)⁻¹) = 0 :=
    eq_zero_of_mem_normOne ψ hψ hadd hE (by exact mul_inv_moduleSection_mem w y)
  have hs : ψ (s r) = fA (Real.log r) := by
    show ψ (s r) = ψ (s (e (Real.log r)))
    rw [hr']
  rw [hsplit, hadd, hz, zero_add, hs, hL, mul_comm]

end OnE

theorem exists_eq_mul_log_absE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (φ : (AE F E)ˣ → ℂ), Continuous φ → (∀ s t, φ (s * t) = φ s + φ t) →
    (∀ γ : Eˣ, φ (Units.map (inclR (F := F) (AF F)).toMonoidHom γ) = 0) →
    ∃ A : ℂ, ∀ t, φ t = A * ((Real.log (absE F E t : ℝ) : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ φ hφ hadd hE
  have hdiag : ∀ γ : Eˣ, ofE F E (IdeleGroup.diagonal E γ) = Units.map (inclR (F := F) (AF F)).toMonoidHom γ :=
    fun γ => by rw [← toE_inclR F E, ofE_toE]
  obtain ⟨A, hA⟩ := exists_log_of_ideleGroup (fun y => φ (ofE F E y)) (hφ.comp (continuous_ofE F E))
    (fun s t => by simp only [map_mul, hadd]) (fun γ => by simp only [hdiag, hE])
  refine ⟨A, fun t => ?_⟩
  have h := hA (toE F E t)
  rw [ofE_toE] at h
  rw [h, absE_eq_ideleModule F E]

end GlobalTheory.IdeleLogHom
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.AdeleUnitModule

open scoped Pointwise ENNReal

theorem map_smul_eq_inv_smul {G A : Type} [Group G] [AddCommGroup A] [DistribMulAction G A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A]
    [ContinuousConstSMul G A] [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] (g : G) :
    μ.map (fun x => g • x) = ((distribHaarChar A g : ℝ≥0∞))⁻¹ • μ := by
  have h1 : DomMulAct.mk g⁻¹ • μ = μ.map (fun x => g • x) := by
    ext s hs
    rw [Measure.domSMul_apply, Measure.map_apply (measurable_const_smul g) hs, Set.preimage_smul]
    simp
  have h2 := Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk g⁻¹ • μ) μ
  rw [addHaarScalarFactor_smul_eq_distribHaarChar μ g⁻¹, map_inv (distribHaarChar A)] at h2
  rw [← h1, h2, ENNReal.smul_def, ENNReal.coe_inv (distribHaarChar_pos).ne']

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange

theorem distribHaarChar_eq_absE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTopologicalRing (AE F E)] [LocallyCompactSpace (AE F E)] [SecondCountableTopology (AE F E)] [T2Space (AE F E)]
    (t : (AE F E)ˣ) : distribHaarChar (AE F E) t = absE F E t := by
  have : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  have := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  have : IsModuleTopology (AF F) (AdeleRing (𝓞 E) E) := isModuleTopology_adeleRing
  let φ : AE F E ≃ₜ+ AdeleRing (𝓞 E) E :=
    { (adeleTensorAlgEquivLeft F E).toAddEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap (adeleTensorAlgEquivLeft F E).toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap (adeleTensorAlgEquivLeft F E).symm.toLinearMap }
  haveI : SecondCountableTopology (AdeleRing (𝓞 E) E) := φ.symm.toHomeomorph.secondCountableTopology
  haveI : T2Space (AdeleRing (𝓞 E) E) := φ.symm.toHomeomorph.isEmbedding.t2Space
  have h1 : distribHaarChar (AdeleRing (𝓞 E) E) (GlobalTheory.IdeleLogHom.toE F E t) = distribHaarChar (AE F E) t :=
    GlobalTheory.JR.ModuleNorm.distribHaarChar_transport φ t (GlobalTheory.IdeleLogHom.toE F E t) (fun x => by
      change adeleTensorAlgEquivLeft F E ((t : AE F E) * x) = _
      rw [map_mul]
      rfl)
  apply NNReal.eq
  rw [← h1, GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GlobalTheory.IdeleLogHom.absE_eq_ideleModule]

theorem map_mul_eq_absE_inv_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ [MeasurableSpace (AE F E)] [BorelSpace (AE F E)] (ν : Measure (AE F E)), ν.IsAddHaarMeasure →
  ∀ t : (AE F E)ˣ, ν.map (fun x => (t : AE F E) * x) = ((absE F E t : ENNReal))⁻¹ • ν := by
  intro F E _ _ _ _ _ σ _ _ _ ν _ t
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  have h := map_smul_eq_inv_smul ν t
  rw [distribHaarChar_eq_absE] at h
  exact h

end GlobalTheory.AdeleUnitModule
end
