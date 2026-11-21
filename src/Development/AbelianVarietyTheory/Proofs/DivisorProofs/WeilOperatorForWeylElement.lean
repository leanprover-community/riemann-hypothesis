import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierSchwartzStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIndicatorFourier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFourierTransformSurjectiveIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForUnipotentMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicEqSpanPure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicPureTensorEqProductLocal

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fourier_schwartz_stable : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl F, (∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ],
    (∀ φ ∈ SB (κ → Fv F v), fourV ψ v φ ∈ SB (κ → Fv F v)) ∧
    (∀ φ ∈ SB (κ → Fv F v), ∀ χ ∈ SB (κ → Fv F v), fourV ψ v (φ + χ) = fourV ψ v φ + fourV ψ v χ) ∧
    ∀ (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v), schr (GlobalTheory.LatVac.psiAt ψ v) w φ ∈ SB (κ → Fv F v) := by
  first | exact @GlobalTheory.WeylFour.fourV_sb | exact GlobalTheory.WeylFour.fourV_sb | (intros; apply GlobalTheory.WeylFour.fourV_sb <;> assumption)
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour.LocInv

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

local instance borelFvLoc (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

open GlobalTheory.SplitWeil

theorem norm_addChar_eq_one {v : Pl F} (χ : AddChar (Fv F v) ℂ) (hχ : Continuous χ) (x : Fv F v) :
    ‖χ x‖ = 1 := by
  have hb : ∀ y : Fv F v, ‖χ y‖ ≤ 1 := by
    intro y
    obtain ⟨s, hs⟩ : ∃ s : (Fv F v)ˣ, y ∈ cball s := by
      by_cases hy : y = 0
      · exact ⟨1, by simp [hy, cball]⟩
      · exact ⟨Units.mk0 y hy, by simp [cball]⟩
    obtain ⟨M, hM⟩ := (isCompact_cball s).exists_bound_of_continuousOn hχ.continuousOn
    have hn : ∀ n : ℕ, ‖χ y‖ ^ n ≤ M := by
      intro n
      have hmem : n • y ∈ cball s := by
        induction n with
        | zero => simp [cball]
        | succ n ih => rw [succ_nsmul]; exact add_mem_cball ih hs
      rw [← norm_pow, ← AddChar.map_nsmul_eq_pow]
      exact hM _ hmem
    by_contra h
    push_neg at h
    obtain ⟨n, hn'⟩ := pow_unbounded_of_one_lt M h
    exact absurd (hn n) (not_le.mpr hn')
  have h1 := hb x
  have h2 := hb (-x)
  have h3 : χ x * χ (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h4 : ‖χ x‖ * ‖χ (-x)‖ = 1 := by rw [← norm_mul, h3, norm_one]
  refine le_antisymm h1 ?_
  nlinarith [norm_nonneg (χ x), norm_nonneg (χ (-x))]

def toCirc {v : Pl F} (χ : AddChar (Fv F v) ℂ) (h : ∀ x, ‖χ x‖ = 1) : AddChar (Fv F v) Circle where
  toFun x := ⟨χ x, by simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using h x⟩
  map_zero_eq_one' := by
    apply Circle.ext
    simp
  map_add_eq_mul' a b := by
    apply Circle.ext
    exact χ.map_add_eq_mul a b

theorem coe_toCirc {v : Pl F} (χ : AddChar (Fv F v) ℂ) (h : ∀ x, ‖χ x‖ = 1) (x : Fv F v) :
    ((toCirc χ h x : Circle) : ℂ) = χ x := rfl

theorem continuous_psiAt' (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl F) :
    Continuous (GlobalTheory.LatVac.psiAt ψ v) := by
  have hj : Continuous (GlobalTheory.LatVac.liftV (F := F) v) := by
    change Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)
    exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)
  exact hψ.comp hj

theorem measV_selfDual (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (v : Pl F) (hne : ∃ x, psiLoc ψ v x ≠ 1) :
    ∃ (h : ∀ x, ‖GlobalTheory.LatVac.psiAt ψ v x‖ = 1) (c : (Fv F v)ˣ),
      HasConductor (toCirc _ h) c ∧ IsSelfDual (toCirc _ h) (measV ψ v) := by
  have hc := continuous_psiAt' ψ hψ.1 v
  have hn : ∀ x, ‖GlobalTheory.LatVac.psiAt ψ v x‖ = 1 := norm_addChar_eq_one _ hc
  have hcc : Continuous (toCirc _ hn) := Continuous.subtype_mk hc _
  have hne1 : toCirc _ hn ≠ 1 := by
    obtain ⟨x, hx⟩ := hne
    intro h1
    apply hx
    have := congrArg (fun χ : AddChar (Fv F v) Circle => ((χ x : Circle) : ℂ)) h1
    simpa [coe_toCirc, GlobalTheory.LatVac.psiAt_apply] using this
  obtain ⟨c, hcond⟩ := exists_hasConductor_of_continuous _ hcc hne1
  obtain ⟨ν, hν⟩ := exists_isSelfDual_of_hasConductor hcond
  have hex : ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν := ⟨ν, hν.1, fun f hf => hν.2 f hf⟩
  refine ⟨hn, c, hcond, ?_⟩
  have hm : measV ψ v = hex.choose := by
    unfold measV
    rw [dif_pos hex]
  rw [hm]
  exact ⟨hex.choose_spec.1, fun f hf => hex.choose_spec.2 f hf⟩

end GlobalTheory.WeylFour.LocInv

namespace GlobalTheory.WeylFour.LocInv

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem fourV_fourV : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl F,
    (∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ], ∀ φ ∈ SB (κ → Fv F v), fourV ψ v (fourV ψ v φ) = fun x => φ (-x) := by
  intro F _ _ ψ hψ v hne κ _ φ hφ
  classical
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨hn, c, hcond, hself⟩ := measV_selfDual ψ hψ v hne
  haveI := hself.1
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)
  haveI := GlobalTheory.SplitWeil.t2Space (Fv F v)
  funext z
  have hinner : ∀ y, fourV ψ v φ y * GlobalTheory.LatVac.psiAt ψ v (y ⬝ᵥ z) =
      ∫ x, φ (x - z) * ((toCirc _ hn (x ⬝ᵥ y) : Circle) : ℂ) ∂(Measure.pi fun _ : κ => measV ψ v) := by
    intro y
    unfold fourV
    rw [← integral_mul_const]
    have h1 : ∀ x : κ → Fv F v, φ x * GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ y) * GlobalTheory.LatVac.psiAt ψ v (y ⬝ᵥ z) =
        φ x * GlobalTheory.LatVac.psiAt ψ v ((x + z) ⬝ᵥ y) := by
      intro x
      rw [add_dotProduct, AddChar.map_add_eq_mul, dotProduct_comm z y, mul_assoc]
    simp only [h1]
    rw [← integral_sub_right_eq_self (μ := Measure.pi fun _ : κ => measV ψ v)
      (fun x => φ x * GlobalTheory.LatVac.psiAt ψ v ((x + z) ⬝ᵥ y)) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [sub_add_cancel, coe_toCirc]
  have hg : (fun x : κ → Fv F v => φ (x - z)) ∈ GlobalTheory.SplitWeil.SB (κ → Fv F v) :=
    ⟨hφ.1.comp_continuous (continuous_id.sub continuous_const),
      hφ.2.comp_homeomorph (Homeomorph.subRight z)⟩
  have h2 := (GlobalTheory.SplitWeil.FourierPi.fourier_pi_of_conductor hcond hself hg).2
  show ∫ y, fourV ψ v φ y * GlobalTheory.LatVac.psiAt ψ v (y ⬝ᵥ z) ∂(Measure.pi fun _ : κ => measV ψ v) = φ (-z)
  simp only [hinner]
  rw [h2, zero_sub]

end GlobalTheory.WeylFour.LocInv
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fourier_double_reflection : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl F, (∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ], ∀ φ ∈ SB (κ → Fv F v), fourV ψ v (fourV ψ v φ) = fun x => φ (-x) := by
  atlas_forward_decl GlobalTheory.WeylFour.LocInv.fourV_fourV
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

namespace GlobalTheory.WeylFour

theorem schr_fourV_loc : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (v : Pl F) (κ : Type) [Fintype κ]
    (w : (κ → Fv F v) × (κ → Fv F v)) (φ : (κ → Fv F v) → ℂ),
    fourV ψ v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) = schr (GlobalTheory.LatVac.psiAt ψ v) (w.2, -w.1) (fourV ψ v φ) := by
  intro F _ _ ψ _ v κ _ w φ
  haveI hOc : CompactSpace (v.adicCompletionIntegers F) :=
    GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  haveI : LocallyCompactSpace (Fv F v) :=
    (isCompact_iff_compactSpace.2 hOc).locallyCompactSpace_of_mem_nhds_of_addGroup
      ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem (v.adicCompletionIntegers F)))
  haveI : SecondCountableTopology (Fv F v) := by
    have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    have : TopologicalSpace.SeparableSpace (Fv F v) :=
      ⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _,
        IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v⟩⟩
    exact UniformSpace.secondCountable_of_separable (Fv F v)
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hinv : (measV ψ v).IsAddLeftInvariant ∧ SigmaFinite (measV ψ v) := by
    unfold measV
    split_ifs with h
    · haveI := h.choose_spec.1
      exact ⟨inferInstance, inferInstance⟩
    · exact ⟨⟨fun g => by simp⟩, inferInstance⟩
  haveI := hinv.1
  haveI := hinv.2
  have h2 : (⅟2 : Fv F v) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
  funext y
  simp only [fourV, schr]
  set χ := GlobalTheory.LatVac.psiAt ψ v
  set μ := Measure.pi fun _ : κ => measV ψ v
  let g : (κ → Fv F v) → ℂ := fun x =>
    χ ((x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * φ x * χ ((x - w.1) ⬝ᵥ y)
  have hg : ∀ x, χ (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * φ (x + w.1) * χ (x ⬝ᵥ y) = g (x + w.1) := by
    intro x; simp only [g, add_sub_cancel_right]
  simp_rw [hg]
  rw [integral_add_right_eq_self g w.1, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [g]
  have key : (x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) + (x - w.1) ⬝ᵥ y =
      y ⬝ᵥ (-w.1) + ⅟(2 : Fv F v) * (w.2 ⬝ᵥ (-w.1)) + x ⬝ᵥ (y + w.2) := by
    simp only [sub_dotProduct, dotProduct_add, dotProduct_neg]
    rw [dotProduct_comm y w.1, dotProduct_comm w.2 w.1]
    linear_combination (w.1 ⬝ᵥ w.2) * h2
  calc χ ((x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * φ x * χ ((x - w.1) ⬝ᵥ y)
      = φ x * (χ ((x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * χ ((x - w.1) ⬝ᵥ y)) := by ring
    _ = φ x * χ (y ⬝ᵥ (-w.1) + ⅟(2 : Fv F v) * (w.2 ⬝ᵥ (-w.1)) + x ⬝ᵥ (y + w.2)) := by
      rw [← AddChar.map_add_eq_mul, key]
    _ = _ := by rw [AddChar.map_add_eq_mul]; ring

end GlobalTheory.WeylFour
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fourier_schrodinger_intertwine : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (v : Pl F) (κ : Type) [Fintype κ]
    (w : (κ → Fv F v) × (κ → Fv F v)) (φ : (κ → Fv F v) → ℂ),
    fourV ψ v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) = schr (GlobalTheory.LatVac.psiAt ψ v) (w.2, -w.1) (fourV ψ v φ) := by
  atlas_forward_decl GlobalTheory.WeylFour.schr_fourV_loc
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lattice_indicator_fourier : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (v : Pl F) (κ : Type) [Fintype κ],
    GlobalTheory.SympChange.indO (κ := κ) v ∈ SB (κ → Fv F v) ∧
    (PsiUnr ψ v → fourV ψ v (GlobalTheory.SympChange.indO (κ := κ) v) = GlobalTheory.SympChange.indO v) := by
  first | exact @GlobalTheory.WeylFour.IndOSelf.indO_self_fourier | exact GlobalTheory.WeylFour.IndOSelf.indO_self_fourier | (intros; apply GlobalTheory.WeylFour.IndOSelf.indO_self_fourier <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_fourier_transform_surjective_integral : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ ei : SInf F κ →L[ℂ] SInf F κ, Function.Surjective ei ∧ (∀ f y, ei f y = ∫ x, f x * eInf x y ∂(measI F κ)) ∧
      ∀ (f : SInf F κ) y, Continuous (fun x => f x * eInf x y) ∧ Integrable (fun x => f x * eInf x y) (measI F κ) := by
  first | exact @GlobalTheory.WeylFour.exists_fourier_measI | exact GlobalTheory.WeylFour.exists_fourier_measI | (intros; apply GlobalTheory.WeylFour.exists_fourier_measI <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.AdeleCharProd

variable {F : Type} [Field F] [NumberField F]

lemma isOpen_intV (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (HeightOneSpectrum.adicCompletionIntegers F v : Set (HeightOneSpectrum.adicCompletion F v)) :=
  Valued.isOpen_valuationSubring _

def ofInt (q : ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v) : Af F :=
  RestrictedProduct.structureMap _ _ _ q

lemma continuous_ofInt : Continuous (ofInt (F := F)) :=
  (RestrictedProduct.isOpenEmbedding_structureMap (fun v => isOpen_intV (F := F) v)).continuous

lemma ofInt_add (p q : ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v) :
    ofInt (p + q) = ofInt p + ofInt q := by
  apply RestrictedProduct.ext; intro w; rfl

open Classical in
lemma ofInt_single (v : HeightOneSpectrum (𝓞 F)) (t : HeightOneSpectrum.adicCompletionIntegers F v) :
    ofInt (Pi.single v t) = singleFin v (t : Fv F v) := by
  apply RestrictedProduct.ext; intro w
  by_cases h : w = v
  · subst h
    show ((Pi.single w t : ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v) w : Fv F w) = _
    rw [Pi.single_eq_same]
    exact (RestrictedProduct.single_eq_same _ w (t : Fv F w)).symm
  · show ((Pi.single v t : ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v) w : Fv F w) = _
    rw [Pi.single_eq_of_ne h]
    exact (RestrictedProduct.single_eq_of_ne _ (t : Fv F v) h).symm

end GlobalTheory.AdeleCharProd

namespace GlobalTheory.AdeleCharProd

variable {F : Type} [Field F] [NumberField F]

lemma psiLoc_int {ψ : AddChar (AF F) ℂ} {v : Pl F} (hv : PsiUnr ψ v) {t : Fv F v}
    (ht : t ∈ HeightOneSpectrum.adicCompletionIntegers F v) : psiLoc ψ v t = 1 := by
  have := ((hv 1).2 (one_mem _)) t ht
  simpa using this

open Classical in
lemma psi_ofInt_single (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (t : HeightOneSpectrum.adicCompletionIntegers F v) (h : PsiUnr ψ v ∨ t = 0) :
    ψ (LinearMap.inr F (Ainf F) (Af F) (ofInt (Pi.single v t))) = 1 := by
  classical
  rw [ofInt_single]
  rcases h with h | h
  · exact psiLoc_int h t.2
  · subst h
    have h0 : (LinearMap.inr F (Ainf F) (Af F)) ((singleFin v) ((0 : HeightOneSpectrum.adicCompletionIntegers F v) : Fv F v)) = (0 : AF F) := by
      simp; rfl
    rw [h0]; exact AddChar.map_zero_eq_one ψ

open Classical in

lemma psi_ofInt (ψ : AddChar (AF F) ℂ) (hc : Continuous ψ)
    (q : ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v)
    (hq : ∀ v, PsiUnr ψ v ∨ q v = 0) :
    ψ (LinearMap.inr F (Ainf F) (Af F) (ofInt q)) = 1 := by
  set g : (∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v) → ℂ :=
    fun p => ψ (LinearMap.inr F (Ainf F) (Af F) (ofInt p)) with hg
  have gc : Continuous g := by
    refine hc.comp ?_
    refine Continuous.comp ?_ continuous_ofInt
    exact (continuous_const.prodMk continuous_id)
  let tr : Finset (HeightOneSpectrum (𝓞 F)) → ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v :=
    fun T => ∑ v ∈ T, Pi.single v (q v)
  have htr : Tendsto tr atTop (𝓝 q) := by
    rw [tendsto_pi_nhds]; intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop {w}] with T hT
    have hw : w ∈ T := hT (Finset.mem_singleton_self w)
    simp only [tr, Finset.sum_apply]
    rw [Finset.sum_eq_single w]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne' hb]
    · intro h; exact absurd hw h
  have h1 : ∀ T, g (tr T) = 1 := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have h0 : ofInt (F := F) 0 = 0 := by apply RestrictedProduct.ext; intro w; rfl
      simp only [g, tr, Finset.sum_empty, h0, map_zero]; exact AddChar.map_zero_eq_one ψ
    | insert a T ha ih =>
      have hmul : ∀ p p', g (p + p') = g p * g p' := by
        intro p p'; simp only [g, ofInt_add, map_add]; exact AddChar.map_add_eq_mul _ _ _
      have e : tr (insert a T) = Pi.single a (q a) + tr T := by simp only [tr, Finset.sum_insert ha]
      rw [e, hmul, ih, mul_one]; exact psi_ofInt_single ψ a (q a) (hq a)
  have := gc.continuousAt.tendsto.comp htr
  have h2 : Tendsto (g ∘ tr) atTop (𝓝 1) := by
    simp only [Function.comp_def, h1]; exact tendsto_const_nhds
  exact tendsto_nhds_unique this h2

end GlobalTheory.AdeleCharProd

namespace GlobalTheory.AdeleCharProd

variable {F : Type} [Field F] [NumberField F]

open Classical in

lemma finite_decomp (ψ : AddChar (AF F) ℂ) (hunr : ∀ᶠ v in cofinite, PsiUnr ψ v) (x : Af F) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F)))
      (q : ∀ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicCompletionIntegers F v),
      (∀ v, PsiUnr ψ v ∨ q v = 0) ∧ (∀ v ∉ S, PsiUnr ψ v ∧ x v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧
      x = ofInt q + ∑ v ∈ S, singleFin v (x v) := by
  have hev : ∀ᶠ v in cofinite, PsiUnr ψ v ∧ x v ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    hunr.and x.2
  have hS := Filter.eventually_cofinite.1 hev
  refine ⟨hS.toFinset, fun v => if h : PsiUnr ψ v ∧ x v ∈ HeightOneSpectrum.adicCompletionIntegers F v
    then ⟨x v, h.2⟩ else 0, ?_, ?_, ?_⟩
  · intro v
    by_cases h : PsiUnr ψ v ∧ x v ∈ HeightOneSpectrum.adicCompletionIntegers F v
    · exact Or.inl h.1
    · exact Or.inr (dif_neg h)
  · intro v hv
    by_contra h
    exact hv (hS.mem_toFinset.2 h)
  · apply RestrictedProduct.ext; intro w
    show evalV F w x = evalV F w (_ + _)
    rw [map_add, map_sum]
    have hsame : ∀ (t : Fv F w), evalV F w (singleFin w t) = t := fun t =>
      RestrictedProduct.single_eq_same (fun v => HeightOneSpectrum.adicCompletionIntegers F v) w t
    have hne : ∀ v (t : Fv F v), v ≠ w → evalV F w (singleFin v t) = 0 := fun v t h =>
      RestrictedProduct.single_eq_of_ne (fun v => HeightOneSpectrum.adicCompletionIntegers F v) t (Ne.symm h)
    by_cases hw : PsiUnr ψ w ∧ x w ∈ HeightOneSpectrum.adicCompletionIntegers F w
    · have hwS : w ∉ hS.toFinset := fun h => (hS.mem_toFinset.1 h) hw
      rw [Finset.sum_eq_zero]
      · show x w = ((if h : PsiUnr ψ w ∧ x w ∈ HeightOneSpectrum.adicCompletionIntegers F w
          then (⟨x w, h.2⟩ : HeightOneSpectrum.adicCompletionIntegers F w) else 0 : _) : Fv F w) + 0
        rw [dif_pos hw, add_zero]
      · intro v hv
        apply hne
        rintro rfl; exact hwS hv
    · have hwS : w ∈ hS.toFinset := hS.mem_toFinset.2 hw
      rw [Finset.sum_eq_single w]
      · rw [hsame]
        show x w = ((if h : PsiUnr ψ w ∧ x w ∈ HeightOneSpectrum.adicCompletionIntegers F w
          then (⟨x w, h.2⟩ : HeightOneSpectrum.adicCompletionIntegers F w) else 0 : _) : Fv F w) + x w
        rw [dif_neg hw]; simp
      · intro v _ hv; exact hne v _ hv
      · intro h; exact absurd hwS h

end GlobalTheory.AdeleCharProd

namespace GlobalTheory.AdeleCharProd

variable {F : Type} [Field F] [NumberField F]

lemma addChar_sum {ι : Type} (ψ : AddChar (AF F) ℂ) (S : Finset ι) (f : ι → AF F) :
    ψ (∑ v ∈ S, f v) = ∏ v ∈ S, ψ (f v) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty]; exact AddChar.map_zero_eq_one ψ
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

end GlobalTheory.AdeleCharProd

namespace GlobalTheory.AdeleCharProd

theorem psi_eq_inf_mul_finprod : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    (∀ᶠ v in cofinite, PsiUnr ψ v) →
    ∀ a : AF F, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) : ℝ)) * ∏ᶠ v, psiLoc ψ v (evFin F v a) := by
  intro F _ _ ψ hstd hunr a
  classical
  obtain ⟨S, q, hq, hout, hx⟩ := finite_decomp ψ hunr a.2
  let j : Af F →+ AF F :=
    { toFun := fun y => (LinearMap.inr F (Ainf F) (Af F) y : AF F)
      map_zero' := by simp; rfl
      map_add' := fun y z => by
        show ((0 : Ainf F), y + z) = ((0 : Ainf F) + 0, y + z)
        rw [add_zero] }
  let i1 : AF F := LinearMap.inl F (Ainf F) (Af F) a.1
  have ha : a = i1 + j a.2 := by
    show a = (a.1 + 0, 0 + a.2)
    rw [add_zero, zero_add]; rfl
  have hinf : ψ i1 = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) : ℝ)) := by
    refine hstd.2.2 _ ?_
    intro u hu
    have hu1 : u.1 = 0 := by
      have : (InfiniteAdeleRing.ringEquiv_mixedSpace F) u.1 = 0 := hu
      exact (map_eq_zero_iff _ (RingEquiv.injective _)).1 this
    show (u.1 * a.1, u.2 * 0) = ((0 : AF F))
    rw [hu1, zero_mul, mul_zero]; rfl
  have hfin : ψ (j a.2) = ∏ v ∈ S, psiLoc ψ v (evFin F v a) := by
    rw [hx, map_add, map_sum, AddChar.map_add_eq_mul, addChar_sum]
    rw [show ψ (j (ofInt q)) = 1 from psi_ofInt ψ hstd.1 q hq, one_mul]
    refine Finset.prod_congr rfl fun v _ => ?_
    rfl
  have hfp : ∏ᶠ v, psiLoc ψ v (evFin F v a) = ∏ v ∈ S, psiLoc ψ v (evFin F v a) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra hvS
    obtain ⟨h1, h2⟩ := hout v hvS
    exact hv (psiLoc_int h1 h2)
  rw [hfp]
  conv_lhs => rw [ha]
  rw [AddChar.map_add_eq_mul, hinf, hfin]

end GlobalTheory.AdeleCharProd

end
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylTwist

open GlobalTheory.SympChange GlobalTheory.HeisSchA

theorem pure_mul_psi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    ∀ (κ : Type) [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (y : κ → AF F),
    (∀ v, φ v ∈ SB (κ → Fv F v)) → (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) →
    (∀ v, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) ∈ SB (κ → Fv F v)) ∧
    (∀ᶠ v in cofinite, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) = GlobalTheory.SympChange.indO v) ∧
    ∀ x, pure f φ x * ψ (x ⬝ᵥ y) = (f (fun i => evI F (x i)) * eInf (fun i => evI F (x i)) (fun i => evI F (y i))) *
      ∏ᶠ v, (φ v (fun i => evFin F v (x i)) *
        GlobalTheory.LatVac.psiAt ψ v ((fun i => evFin F v (x i)) ⬝ᵥ fun i => evFin F v (y i))) := by
  intro F _ _ ψ hψ hunr κ _ f φ y hφ hφO
  have hlc := GlobalTheory.SympUnip.psiAt_isLocallyConstant ψ hψ.1
  have hyint : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (y i) ∈ v.adicCompletionIntegers F :=
    eventually_all.2 fun i => GlobalTheory.SympUnip.eventually_evFin (y i)
  refine ⟨fun v => ⟨(hφ v).1.mul ((hlc v).comp_continuous (continuous_id.dotProduct continuous_const)),
    (hφ v).2.mul_right⟩, ?_, fun x => ?_⟩
  · filter_upwards [hunr, hφO, hyint] with v hv hφv hy
    funext z
    rw [hφv]
    by_cases hz : z ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
    · have hm : (z ⬝ᵥ fun i => evFin F v (y i)) ∈ v.adicCompletionIntegers F :=
        sum_mem fun i _ => mul_mem (hz i) (hy i)
      have h4 := (hv 1).2 (one_mem _) _ hm
      rw [one_mul] at h4
      rw [GlobalTheory.LatVac.psiAt_apply, h4, mul_one]
    · rw [indO, Set.indicator_of_notMem hz, zero_mul]
  · have hfin : (Function.mulSupport fun v : Pl F => φ v fun i => evFin F v (x i)).Finite := by
      have h3 : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
        eventually_all.2 fun i => GlobalTheory.SympUnip.eventually_evFin (x i)
      have h4 : ∀ᶠ v : Pl F in cofinite, (φ v fun i => evFin F v (x i)) = 1 := by
        filter_upwards [hφO, h3] with v hv h3
        rw [hv, indO, Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h3)]
        rfl
      exact h4
    have hq : ∀ v : Pl F, evalV F v (p2 (x ⬝ᵥ y)) =
        (fun i => evFin F v (x i)) ⬝ᵥ fun i => evFin F v (y i) := fun v =>
      RingHom.map_dotProduct (evFin F v : AF F →+* Fv F v) x y
    obtain ⟨hs, hp⟩ := GlobalTheory.SympUnip.finChar_eq_finprod ψ hψ.1 (p2 (x ⬝ᵥ y))
    simp only [hq] at hs hp
    let q : AF F →+* mixedEmbedding.mixedSpace F := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1
    have h3 : ψ (mk (p1 (x ⬝ᵥ y)) 0) = eInf (fun i => evI F (x i)) (fun i => evI F (y i)) := by
      have e1 : evI F (mk (p1 (x ⬝ᵥ y)) 0) = (fun i => evI F (x i)) ⬝ᵥ fun i => evI F (y i) :=
        RingHom.map_dotProduct q x y
      rw [hψ.2.2 _ (at_mk _), e1, eInf]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [finprod_mul_distrib hfin hs, ← hp, map_eq_mul ψ (x ⬝ᵥ y), h3]
    ring

end GlobalTheory.WeylTwist

end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_restricted_product_char : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    ∀ (κ : Type) [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (y : κ → AF F),
    (∀ v, φ v ∈ SB (κ → Fv F v)) → (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) →
    (∀ v, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) ∈ SB (κ → Fv F v)) ∧
    (∀ᶠ v in cofinite, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) = GlobalTheory.SympChange.indO v) ∧
    ∀ x, pure f φ x * ψ (x ⬝ᵥ y) = (f (fun i => evI F (x i)) * eInf (fun i => evI F (x i)) (fun i => evI F (y i))) *
      ∏ᶠ v, (φ v (fun i => evFin F v (x i)) *
        GlobalTheory.LatVac.psiAt ψ v ((fun i => evFin F v (x i)) ⬝ᵥ fun i => evFin F v (y i))) := by
  atlas_forward_decl GlobalTheory.WeylTwist.pure_mul_psi
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_adelic_eq_span_pure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    schA F κ = Submodule.span ℂ {Φ | ∃ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) ∧
      (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) ∧ Φ = pure f φ} := by
  first | exact @GlobalTheory.WeylSpan.schA_eq_span_pure | exact GlobalTheory.WeylSpan.schA_eq_span_pure | (intros; apply GlobalTheory.WeylSpan.schA_eq_span_pure <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_preserves_schwartz : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), ∀ Φ ∈ schA F κ, schr ψ w Φ ∈ schA F κ := by
  first | exact @GlobalTheory.WeylFour.SchrKeep.schr_mem_schA | exact GlobalTheory.WeylFour.SchrKeep.schr_mem_schA | (intros; apply GlobalTheory.WeylFour.SchrKeep.schr_mem_schA <;> assumption)
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
noncomputable section

namespace GlobalTheory.WeylMeas

open scoped ENNReal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_meas : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl F, ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ],
    ∃ μ : Measure (κ → AF F), μ.IsAddRightInvariant ∧
      ∀ (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), Continuous g →
        Integrable g (measI F κ) → (∀ v, φ v ∈ SB (κ → Fv F v)) → (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) →
        Integrable (fun x => g (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i))) μ ∧
        ∫ x, g (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i)) ∂μ =
          (∫ z, g z ∂(measI F κ)) * ∏ᶠ v, ∫ z, φ v z ∂(Measure.pi fun _ : κ => measV ψ v) := by
  intro F _ _ ψ hψ hunr hne κ _
  classical
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI hB : ∀ v : Pl F, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI hSC : ∀ v : Pl F, SecondCountableTopology (Fv F v) := fun v => GlobalTheory.SplitWeil.secondCountable _
  haveI hH : ∀ v : Pl F, (measV ψ v).IsAddHaarMeasure := fun v => (isSelfDualFor_measV ψ hψ.1 v (hne v)).1
  haveI : (measI F κ).IsAddHaarMeasure := measI_isAddHaar F κ
  have hOint : ∀ v : Pl F, (v.adicCompletionIntegers F : Set (Fv F v)) =
      ((ValuativeRel.valuation (Fv F v)).integer : Set (Fv F v)) := fun v => by
    ext x; exact (GlobalTheory.WeylFour.IndOSelf.mem_int_iff x).symm
  have hOc : ∀ v : Pl F, IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := fun v =>
    (hOint v) ▸ GlobalTheory.SplitWeil.isCompact_int _
  have hOo : ∀ v : Pl F, IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := fun v =>
    (hOint v) ▸ GlobalTheory.SplitWeil.isOpen_int _
  have hOpi : ∀ v : Pl F, {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} =
      Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := fun v => by
    ext x; simp
  have hOm : ∀ v : Pl F, MeasurableSet {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := fun v => by
    rw [hOpi v]; exact MeasurableSet.univ_pi fun _ => (hOo v).measurableSet
  set c : Pl F → ℝ≥0∞ := fun v =>
    (Measure.pi fun _ : κ => measV ψ v) {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} with hcdef
  have hcpi : ∀ v, c v = ∏ _i : κ, measV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) := fun v => by
    simp only [c]; rw [hOpi v, Measure.pi_pi]
  have hc0 : ∀ v, c v ≠ 0 := fun v => by
    rw [hcpi v]
    exact Finset.prod_ne_zero_iff.2 fun _ _ =>
      ((hOo v).measure_pos (measV ψ v) ⟨0, (v.adicCompletionIntegers F).zero_mem⟩).ne'
  have hct : ∀ v, c v ≠ ⊤ := fun v => by
    rw [hcpi v]
    exact ENNReal.prod_ne_top fun _ _ => (hOc v).measure_lt_top.ne
  have hc1 : ∀ v, PsiUnr ψ v → c v = 1 := fun v hv => by
    have h1 := (GlobalTheory.WeylFour.IndOSelf.isUnitVol_measV ψ v hv).2
    rw [← hOint v] at h1
    rw [hcpi v, h1, Finset.prod_const_one]
  set μv : ∀ v : Pl F, Measure (κ → Fv F v) := fun v => (c v)⁻¹ • Measure.pi fun _ : κ => measV ψ v with hμvdef
  haveI hμvH : ∀ v, (μv v).IsAddHaarMeasure := fun v =>
    Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 (hct v)) (ENNReal.inv_ne_top.2 (hc0 v))
  have hμv1 : ∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 := fun v => by
    simp only [μv]
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (hc0 v) (hct v)
  have hpi : ∀ v, (Measure.pi fun _ : κ => measV ψ v) = c v • μv v := fun v => by
    simp only [μv, smul_smul, ENNReal.mul_inv_cancel (hc0 v) (hct v), one_smul]
  obtain ⟨c₀, hc₀, hform⟩ := GlobalTheory.AdelicHaarPure.integral_pure_haar F κ (Measure.addHaar : Measure (κ → AF F))
    (measI F κ) μv hμv1

  have hind1 : ∀ v, ∫ x, GlobalTheory.RatWeilOp.ind κ v x ∂(μv v) = 1 := fun v => by
    have := integral_indicator_const (μ := μv v) (1 : ℂ) (hOm v)
    simpa [GlobalTheory.RatWeilOp.ind, Measure.real, Pi.one_def, hμv1 v] using this

  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hbcs : HasCompactSupport (fun z => b z) := b.hasCompactSupport
  have hf₀c : Continuous (fun z => ((b z : ℝ) : ℂ)) := Complex.continuous_ofReal.comp b.continuous
  have hf₀cs : HasCompactSupport (fun z => ((b z : ℝ) : ℂ)) := hbcs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hf₀i : Integrable (fun z => ((b z : ℝ) : ℂ)) (measI F κ) := hf₀c.integrable_of_hasCompactSupport hf₀cs
  have hBpos : 0 < ∫ z, b z ∂(measI F κ) :=
    b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := measI F κ) (x := 0) hbcs (fun z => b.nonneg)
      (by rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]; exact one_ne_zero)
  have hfam0 : GlobalTheory.RatWeilOp.IsFam (fun v : Pl F => GlobalTheory.RatWeilOp.ind κ v) :=
    ⟨fun v => GlobalTheory.WeylFour.IndOSelf.indO_mem_SB v κ, Filter.Eventually.of_forall fun v => rfl⟩
  obtain ⟨-, h0⟩ := hform (fun z => ((b z : ℝ) : ℂ)) _ hf₀c hf₀i hfam0
  rw [finprod_congr hind1, finprod_one, mul_one, integral_complex_ofReal] at h0
  set H : (κ → AF F) → ℂ := fun x => ((b (fun i => evI F (x i)) : ℝ) : ℂ) *
    ∏ᶠ v, GlobalTheory.RatWeilOp.ind κ v (fun i => evFin F v (x i)) with hHdef
  have key : ∀ z w : ℂ, (z.im = 0 ∧ 0 ≤ z.re) → (w.im = 0 ∧ 0 ≤ w.re) → ((z * w).im = 0 ∧ 0 ≤ (z * w).re) := by
    rintro z w ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨by rw [Complex.mul_im, h1, h3]; simp, by rw [Complex.mul_re, h1, h3]; simpa using mul_nonneg h2 h4⟩
  have hP : ∀ x, (H x).im = 0 ∧ 0 ≤ (H x).re := by
    intro x
    refine key _ _ ⟨by simp, by simpa using b.nonneg⟩ ?_
    refine finprod_induction (fun z : ℂ => z.im = 0 ∧ 0 ≤ z.re) ⟨by simp, by simp⟩ key (fun v => ?_)
    by_cases h : (fun i => evFin F v (x i)) ∈ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F}
    · simp [GlobalTheory.RatWeilOp.ind, Set.indicator_of_mem h]
    · simp [GlobalTheory.RatWeilOp.ind, Set.indicator_of_notMem h]
  have hHr : H = fun x => (((H x).re : ℝ) : ℂ) := funext fun x => Complex.ext (by simp) (by simp [(hP x).1])
  have hL : ∫ x, H x ∂(Measure.addHaar : Measure (κ → AF F)) =
      ((∫ x, (H x).re ∂(Measure.addHaar : Measure (κ → AF F)) : ℝ) : ℂ) := by
    conv_lhs => rw [hHr]
    exact integral_complex_ofReal
  have hLnn : 0 ≤ ∫ x, (H x).re ∂(Measure.addHaar : Measure (κ → AF F)) := integral_nonneg fun x => (hP x).2
  set L := ∫ x, (H x).re ∂(Measure.addHaar : Measure (κ → AF F)) with hLdef
  set B := ∫ z, b z ∂(measI F κ) with hBdef
  have hc₀eq : c₀ = ((L / B : ℝ) : ℂ) := by
    have hB0 : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hBpos.ne'
    rw [Complex.ofReal_div, eq_div_iff hB0, ← hL, ← h0]
  set t := L / B with htdef
  have ht0 : t ≠ 0 := fun h => hc₀ (by rw [hc₀eq, h, Complex.ofReal_zero])
  have htpos : 0 < t := lt_of_le_of_ne (div_nonneg hLnn hBpos.le) (Ne.symm ht0)

  obtain ⟨T, hT⟩ : ∃ T : Finset (Pl F), ∀ v ∉ T, PsiUnr ψ v :=
    ⟨(Filter.eventually_cofinite.1 hunr).toFinset, fun v hv => by simpa using hv⟩
  set Cr : ℝ := ∏ v ∈ T, (c v).toReal with hCrdef
  have hCr : 0 ≤ Cr := Finset.prod_nonneg fun v _ => ENNReal.toReal_nonneg
  refine ⟨ENNReal.ofReal (Cr / t) • Measure.addHaar, inferInstance, fun g φ hgc hgi hSB hev => ?_⟩
  have hfam : GlobalTheory.RatWeilOp.IsFam φ := ⟨hSB, hev⟩
  obtain ⟨hI, hE⟩ := hform g φ hgc hgi hfam
  refine ⟨hI.smul_measure ENNReal.ofReal_ne_top, ?_⟩
  have hloc : ∀ v, ∫ z, φ v z ∂(Measure.pi fun _ : κ => measV ψ v) = ((c v).toReal : ℂ) * ∫ z, φ v z ∂(μv v) :=
    fun v => by rw [hpi v, integral_smul_measure, Complex.real_smul]
  have hsub : Function.mulSupport (fun v => ((c v).toReal : ℂ)) ⊆ (T : Set (Pl F)) := fun v hv => by
    by_contra h
    exact hv (by show ((c v).toReal : ℂ) = 1; rw [hc1 v (hT v h)]; simp)
  have hs2 : (Function.mulSupport fun v => ∫ z, φ v z ∂(μv v)).Finite :=
    (Filter.eventually_cofinite.1 hev).subset fun v hv h => hv (by
      show ∫ z, φ v z ∂(μv v) = 1
      rw [h]; exact hind1 v)
  have hCprod : ∏ᶠ v, ((c v).toReal : ℂ) = (Cr : ℂ) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub, hCrdef, Complex.ofReal_prod]
  rw [integral_smul_measure, hE, ENNReal.toReal_ofReal (div_nonneg hCr htpos.le), hc₀eq, finprod_congr hloc,
    finprod_mul_distrib (T.finite_toSet.subset hsub) hs2, hCprod, Complex.real_smul]
  have ht0' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht0
  rw [Complex.ofReal_div]
  field_simp

end GlobalTheory.WeylMeas

end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_adelic_integral_formula : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl F, ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ],
    ∃ μ : Measure (κ → AF F), μ.IsAddRightInvariant ∧
      ∀ (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), Continuous g →
        Integrable g (measI F κ) → (∀ v, φ v ∈ SB (κ → Fv F v)) → (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) →
        Integrable (fun x => g (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i))) μ ∧
        ∫ x, g (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i)) ∂μ =
          (∫ z, g z ∂(measI F κ)) * ∏ᶠ v, ∫ z, φ v z ∂(Measure.pi fun _ : κ => measV ψ v) := by
  atlas_forward_decl GlobalTheory.WeylMeas.exists_meas
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

open GlobalTheory.SympChange in

theorem GlobalTheory.WeylFour.weyl_hasOp : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    (∀ᶠ v in cofinite, PsiUnr ψ v) → (∀ v : Pl F, ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ],
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.weylM (F := F) (κ := κ)) := by
  intro F _ _ ψ hψ hunr hnt κ _ _
  classical

  have hsp : ∀ {R : Type} [CommRing R] [Algebra F R] (w : (κ → R) × (κ → R)),
      spAct (weylM (F := F) (κ := κ)) w = (w.2, -w.1) := by
    intro R _ _ w
    ext k
    · simp [spAct, weylM, Matrix.fromBlocks_map, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Matrix.one_apply]
    · simp [spAct, weylM, Matrix.fromBlocks_map, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Matrix.one_apply]

  have hSB := fun v => GlobalTheory.T.local_fourier_schwartz_stable F ψ hψ v (hnt v) κ
  have hInv := fun v => GlobalTheory.T.local_fourier_double_reflection F ψ hψ v (hnt v) κ
  have hLaw := GlobalTheory.T.local_fourier_schrodinger_intertwine F ψ hψ
  have hInd := fun v => GlobalTheory.T.local_lattice_indicator_fourier F ψ hψ v κ
  have hsmV : ∀ v (c : ℂ) (φ : (κ → Fv F v) → ℂ), fourV ψ v (c • φ) = c • fourV ψ v φ := by
    intro v c φ; funext y
    simp only [fourV, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  have h0V : ∀ v, fourV ψ v (0 : (κ → Fv F v) → ℂ) = 0 := by
    intro v; funext y; simp [fourV]
  choose C hC using fun v : Pl F => Submodule.exists_isCompl (SB (κ → Fv F v))
  let P : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ) := fun v =>
    (SB (κ → Fv F v)).subtype ∘ₗ Submodule.linearProjOfIsCompl _ (C v) (hC v)
  have hPmem : ∀ v φ, P v φ ∈ SB (κ → Fv F v) := fun v φ => (Submodule.linearProjOfIsCompl _ (C v) (hC v) φ).2
  have hPid : ∀ v, ∀ φ ∈ SB (κ → Fv F v), P v φ = φ := fun v φ hφ =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left (hC v) ⟨φ, hφ⟩)
  let ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ) := fun v =>
    { toFun := fun φ => fourV ψ v (P v φ)
      map_add' := fun φ χ => by
        rw [map_add]; exact (hSB v).2.1 _ (hPmem v φ) _ (hPmem v χ)
      map_smul' := fun c φ => by
        rw [map_smul, RingHom.id_apply]; exact hsmV v c _ }
  have hev : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = fourV ψ v φ := fun v φ hφ => by
    show fourV ψ v (P v φ) = _
    rw [hPid v φ hφ]
  have hneg : ∀ v, ∀ φ ∈ SB (κ → Fv F v), (fun x => φ (-x)) ∈ SB (κ → Fv F v) := fun v φ hφ =>
    ⟨hφ.1.comp_continuous continuous_neg, hφ.2.comp_homeomorph (Homeomorph.neg _)⟩
  have hmap : ∀ v, (SB (κ → Fv F v)).map (ev v) = SB _ := by
    intro v
    apply le_antisymm
    · rintro _ ⟨φ, hφ, rfl⟩
      rw [hev v φ hφ]; exact (hSB v).1 φ hφ
    · intro φ hφ
      have h1 := hneg v φ hφ
      refine ⟨fourV ψ v (fun x => φ (-x)), (hSB v).1 _ h1, ?_⟩
      rw [hev v _ ((hSB v).1 _ h1), hInv v _ h1]
      simp
  have hinj : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = 0 → φ = 0 := by
    intro v φ hφ h
    rw [hev v φ hφ] at h
    have h2 := hInv v φ hφ
    rw [h, h0V] at h2
    funext x
    have h3 := congrFun h2 (-x)
    simp only [Pi.zero_apply, neg_neg] at h3
    exact h3.symm

  obtain ⟨ei, hsurj, hei, hcont⟩ := GlobalTheory.T.finite_fourier_transform_surjective_integral F κ
  obtain ⟨μ, hμ, hprod⟩ := GlobalTheory.T.exists_haar_adelic_integral_formula F ψ hψ hunr hnt κ
  haveI := hμ
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  have hspan := GlobalTheory.T.schwartz_adelic_eq_span_pure F κ
  let fA : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ := fun Φ y => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ
  have hpure : ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = indO v) → ∀ y, Integrable (fun x => pure f φ x * ψ (x ⬝ᵥ y)) μ ∧
        fA (pure f φ) y = pure (ei f) (fun v => fourV ψ v (φ v)) y := by
    intro f φ hφ hae y
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.schwartz_bruhat_restricted_product_char F ψ hψ hunr κ f φ y hφ hae
    have e : (fun x => pure f φ x * ψ (x ⬝ᵥ y)) = fun x =>
        (fun z => f z * eInf z (fun i => evI F (y i))) (fun i => evI F (x i)) *
          ∏ᶠ v, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) (fun i => evFin F v (x i)) :=
      funext h3
    obtain ⟨hc, hi⟩ := hcont f (fun i => evI F (y i))
    obtain ⟨j1, j2⟩ := hprod _ _ hc hi h1 h2
    refine ⟨e ▸ j1, ?_⟩
    show (∫ x, pure f φ x * ψ (x ⬝ᵥ y) ∂μ) = _
    rw [e, j2, ← hei]
    rfl
  have hint : ∀ Φ ∈ schA F κ, ∀ y, Integrable (fun x => Φ x * ψ (x ⬝ᵥ y)) μ := by
    intro Φ hΦ y
    rw [hspan] at hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, φ, hφ, hae, rfl⟩ := h
      exact (hpure f φ hφ hae y).1
    | zero => simp
    | add Φ Ψ _ _ h1 h2 =>
      refine (h1.add h2).congr (Filter.Eventually.of_forall fun x => ?_)
      simp [add_mul]
    | smul c Φ _ h => simpa [mul_assoc] using h.const_mul c
  have hadd : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, fA (Φ + Ψ) = fA Φ + fA Ψ := by
    intro Φ hΦ Ψ hΨ; funext y
    simp only [fA, Pi.add_apply, add_mul]
    exact integral_add (hint Φ hΦ y) (hint Ψ hΨ y)
  have hsmul : ∀ (c : ℂ) (Φ : (κ → AF F) → ℂ), fA (c • Φ) = c • fA Φ := by
    intro c Φ; funext y
    simp only [fA, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  have hkeep : ∀ Φ ∈ schA F κ, fA Φ ∈ schA F κ := by
    intro Φ hΦ
    rw [hspan] at hΦ ⊢
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, φ, hφ, hae, rfl⟩ := h
      have e : fA (pure f φ) = pure (ei f) (fun v => fourV ψ v (φ v)) := funext fun y => (hpure f φ hφ hae y).2
      rw [e]
      refine Submodule.subset_span ⟨ei f, fun v => fourV ψ v (φ v), fun v => (hSB v).1 _ (hφ v), ?_, rfl⟩
      filter_upwards [hae, hunr] with v h1 h2
      rw [h1, (hInd v).2 h2]
    | zero =>
      have : fA 0 = 0 := by funext y; simp [fA]
      rw [this]; exact zero_mem _
    | add Φ Ψ hΦ hΨ h1 h2 =>
      rw [hadd Φ (hspan ▸ hΦ) Ψ (hspan ▸ hΨ)]; exact add_mem h1 h2
    | smul c Φ _ h =>
      rw [hsmul]; exact Submodule.smul_mem _ c h
  have hlawA : ∀ w Φ, fA (schr ψ w Φ) = schr ψ (w.2, -w.1) (fA Φ) := by
    intro w Φ; funext y
    simp only [fA, schr]
    have h1 := integral_add_right_eq_self (μ := μ) (fun z => ψ ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) *
      Φ z * ψ ((z - w.1) ⬝ᵥ y)) w.1
    simp only [add_sub_cancel_right] at h1
    rw [h1, ← integral_const_mul]
    congr 1; funext z
    have h2 : (⅟(2 : AF F)) + ⅟2 = 1 := invOf_two_add_invOf_two
    have key : ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) + (z - w.1) ⬝ᵥ y =
        (y ⬝ᵥ -w.1 + ⅟2 * (w.2 ⬝ᵥ -w.1)) + z ⬝ᵥ (y + w.2) := by
      simp only [sub_dotProduct, dotProduct_add, dotProduct_neg]
      rw [dotProduct_comm w.2 w.1, dotProduct_comm y w.1]
      linear_combination (w.1 ⬝ᵥ w.2) * h2
    calc ψ ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ z * ψ ((z - w.1) ⬝ᵥ y)
        = Φ z * ψ (((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) + (z - w.1) ⬝ᵥ y) := by
          rw [AddChar.map_add_eq_mul ψ ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) ((z - w.1) ⬝ᵥ y)]; ring
      _ = _ := by
          rw [key, AddChar.map_add_eq_mul ψ (y ⬝ᵥ -w.1 + ⅟2 * (w.2 ⬝ᵥ -w.1)) (z ⬝ᵥ (y + w.2))]; ring
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl (schA F κ)
  let Q : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) := (schA F κ).subtype ∘ₗ Submodule.linearProjOfIsCompl _ D hD
  have hQmem : ∀ Φ, Q Φ ∈ schA F κ := fun Φ => (Submodule.linearProjOfIsCompl _ D hD Φ).2
  have hQid : ∀ Φ ∈ schA F κ, Q Φ = Φ := fun Φ hΦ =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hD ⟨Φ, hΦ⟩)
  let e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ :=
    { toFun := fun Φ => fA (Q Φ)
      map_add' := fun Φ Ψ => by rw [map_add]; exact hadd _ (hQmem Φ) _ (hQmem Ψ)
      map_smul' := fun c Φ => by rw [map_smul, RingHom.id_apply]; exact hsmul c _ }
  have he : ∀ Φ ∈ schA F κ, e Φ = fA Φ := fun Φ hΦ => by
    show fA (Q Φ) = _
    rw [hQid Φ hΦ]
  refine ⟨e, ei, ev, hsurj, fun Φ hΦ => ?_, fun w Φ hΦ => ?_, hmap, hinj, fun v w φ hφ => ?_, ?_, ?_⟩
  · rw [he Φ hΦ]; exact hkeep Φ hΦ
  · rw [he _ (GlobalTheory.T.schrodinger_preserves_schwartz F ψ hψ κ w Φ hΦ), he Φ hΦ, hlawA, hsp]
  · rw [hsp, hev v _ ((hSB v).2.2 w φ hφ), hev v φ hφ, hLaw v κ w φ]
  · filter_upwards [hunr] with v hv
    rw [hev v _ (hInd v).1, (hInd v).2 hv]
  · intro f φ hφ hae
    have hm : pure f φ ∈ schA F κ := by
      rw [hspan]; exact Submodule.subset_span ⟨f, φ, hφ, hae, rfl⟩
    have e2 : (fun v => ev v (φ v)) = fun v => fourV ψ v (φ v) := funext fun v => hev v _ (hφ v)
    rw [he _ hm, e2]
    exact funext fun y => (hpure f φ hφ hae y).2
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_for_weyl_element : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl F, ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ],
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.weylM (F := F) (κ := κ)) := by
  atlas_forward_decl GlobalTheory.WeylFour.weyl_hasOp
end
