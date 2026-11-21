import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormEqZeroOfLagrangianAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedDiagonalIntegralLinearFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharSupportedIdeleEqLocalAbsValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormVanishesLagrangianTestStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersAgreeInertUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerIrreducibleFinitePlaceCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedAbsDetMulIntegralCompMulVecFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceComponentAdeleNormEqLocalNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormVanishesLagrangianTest
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormEqZeroOfLagrangianAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicLeviInverseQuotientDetNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalarInertPlaceInvertibleShifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentBlockUnipotentIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.InertLagInd

variable {F : Type} [Field F] [NumberField F] {v : Pl F} {κ : Type} [Fintype κ]

theorem invOf_two_mem (h : (2 : 𝓞 F) ∉ v.asIdeal) : ⅟(2 : Fv F v) ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (algebraMap (𝓞 F) F 2) = 1 := (v.valuation_eq_one_iff_notMem (K := F)).2 h
  rw [map_ofNat] at h1
  have h2 : Valued.v (algebraMap F (Fv F v) (2 : F)⁻¹) = v.valuation F (2 : F)⁻¹ :=
    v.valuedAdicCompletion_eq_valuation' _
  simp only [map_inv₀] at h2
  rw [h1, inv_one, map_ofNat] at h2
  rw [invOf_eq_inv, map_inv₀, h2]

theorem schr_box_apply (ψ : AddChar (Fv F v) ℂ) (φ₁ φ₂ : (κ → Fv F v) → ℂ) (w : (κ → Fv F v) × (κ → Fv F v))
    (x : κ → Fv F v) :
    schr ψ (Sum.elim w.1 0, Sum.elim w.2 0) (boxFun φ₁ φ₂) (Sum.elim x x) =
      ψ (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * (φ₁ (x + w.1) * φ₂ x) := by
  simp only [schr, boxFun, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero]
  congr 2
  all_goals (congr 1; funext i; simp)

end GlobalTheory.InertLagInd

namespace GlobalTheory.InertLagInd

theorem diagW_box_indicator : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ]
    (ψ : AddChar (AF F) ℂ), PsiUnr ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ φ₀ ∈ SB (κ → Fv F v), ∃ c : ℂ, c ≠ 0 ∧ ∃ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U ∧ IsCompact U ∧ 0 ∈ U ∧
      ∀ w, diagW (psiAt ψ v) μ (boxFun φ₀ φ₀) w = U.indicator (fun _ => c) w := by
  intro F _ _ v κ _ ψ hψ h2 μ hμ
  classical
  letI : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨S, hS⟩ : ∃ S : Set (κ → Fv F v), S = {x | ∀ k, x k ∈ v.adicCompletionIntegers F} := ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ S ↔ ∀ k, x k ∈ v.adicCompletionIntegers F := fun x => by subst hS; rfl
  have hpi : S = Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x; simp [hmem]
  have hSo : IsOpen S := by
    rw [hpi]; exact isOpen_set_pi Set.finite_univ (fun _ _ => Valued.isOpen_integer _)
  have hSc : IsCompact S := by
    rw [hpi]; exact isCompact_univ_pi (fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v)
  have h0S : (0 : κ → Fv F v) ∈ S := (hmem 0).2 fun k => zero_mem _
  have hadd : ∀ {a}, a ∈ S → ∀ x, (x + a ∈ S ↔ x ∈ S) := fun {a} ha x => by
    rw [hmem, hmem]
    rw [hmem] at ha
    exact ⟨fun h k => by simpa using sub_mem (h k) (ha k), fun h k => add_mem (h k) (ha k)⟩
  have hind : ∀ {a}, a ∈ S → ∀ x, S.indicator (1 : (κ → Fv F v) → ℂ) (x + a) = S.indicator 1 x := fun ha x => by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hadd ha x).2 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hadd ha x).1 hx)]
  have hψ1 : ∀ y ∈ v.adicCompletionIntegers F, psiAt ψ v y = 1 := fun y hy => by
    rw [psiAt_apply]; simpa using (hψ 1).2 (one_mem _) y hy
  have hφ : S.indicator (1 : (κ → Fv F v) → ℂ) ∈ SB (κ → Fv F v) := by
    rw [hS]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
  refine ⟨S.indicator 1, hφ, ((μ.real S : ℝ) : ℂ), ?_, S ×ˢ S, hSo.prod hSo, hSc.prod hSc, ⟨h0S, h0S⟩, ?_⟩
  · have h1 : μ S ≠ 0 := hSo.measure_ne_zero μ ⟨0, h0S⟩
    have h2' : μ S ≠ ⊤ := hSc.measure_lt_top.ne
    exact Complex.ofReal_ne_zero.2 (by rw [measureReal_def]; exact ENNReal.toReal_ne_zero.2 ⟨h1, h2'⟩)
  intro w
  simp only [diagW, schr_box_apply]
  by_cases hw1 : w.1 ∈ S
  · by_cases hw2 : w.2 ∈ S
    · rw [Set.indicator_of_mem (Set.mem_prod.2 ⟨hw1, hw2⟩)]
      have key : ∀ x, psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) *
          (S.indicator 1 (x + w.1) * S.indicator 1 x) = S.indicator (1 : (κ → Fv F v) → ℂ) x := by
        intro x
        rw [hind hw1 x]
        by_cases hx : x ∈ S
        · rw [Set.indicator_of_mem hx, hψ1]
          · simp
          · rw [hmem] at hx hw1 hw2
            exact add_mem (sum_mem fun i _ => mul_mem (hx i) (hw2 i))
              (mul_mem (invOf_two_mem h2) (sum_mem fun i _ => mul_mem (hw1 i) (hw2 i)))
        · simp [Set.indicator_of_notMem hx]
      simp_rw [key]
      rw [show S.indicator (1 : (κ → Fv F v) → ℂ) = S.indicator (fun _ => (1 : ℂ)) from rfl,
        integral_indicator_const _ hSo.measurableSet]
      simp
    · rw [Set.indicator_of_notMem (fun h => hw2 (Set.mem_prod.1 h).2)]
      obtain ⟨i, hi⟩ : ∃ i, w.2 i ∉ v.adicCompletionIntegers F := by
        by_contra h; push_neg at h; exact hw2 ((hmem _).2 h)
      obtain ⟨y, hy, hne⟩ : ∃ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (w.2 i * y) ≠ 1 := by
        by_contra h; push_neg at h; exact hi ((hψ _).1 h)
      have ha : Pi.single i y ∈ S := (hmem _).2 fun k => by
        rw [Pi.single_apply]; split_ifs
        · exact hy
        · exact zero_mem _
      set g : (κ → Fv F v) → ℂ := fun x => psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) *
          (S.indicator 1 (x + w.1) * S.indicator 1 x) with hg
      have hshift : ∀ x, g (x + Pi.single i y) = psiAt ψ v (w.2 i * y) * g x := by
        intro x
        simp only [hg]
        rw [add_right_comm, hind ha, hind ha, add_dotProduct, single_dotProduct,
          show x ⬝ᵥ w.2 + y * w.2 i + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) =
            w.2 i * y + (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) by ring, AddChar.map_add_eq_mul]
        ring
      have hI : ∫ x, g x ∂μ = psiAt ψ v (w.2 i * y) * ∫ x, g x ∂μ := by
        rw [← integral_const_mul, ← integral_add_right_eq_self _ (Pi.single i y)]
        simp only [hshift]
      rw [psiAt_apply] at hI
      have : (1 - psiLoc ψ v (w.2 i * y)) * ∫ x, g x ∂μ = 0 := by rw [sub_mul, one_mul, ← hI, sub_self]
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne.symm)
  · rw [Set.indicator_of_notMem (fun h => hw1 (Set.mem_prod.1 h).1)]
    have hz : ∀ x, psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) *
        (S.indicator (1 : (κ → Fv F v) → ℂ) (x + w.1) * S.indicator 1 x) = 0 := by
      intro x
      by_cases hx : x ∈ S
      · have : x + w.1 ∉ S := fun h => hw1 (by rw [add_comm] at h; exact (hadd hx w.1).1 h)
        simp [Set.indicator_of_notMem this]
      · simp [Set.indicator_of_notMem hx]
    simp_rw [hz]
    exact integral_zero _ _

end GlobalTheory.InertLagInd
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_integral_heisenberg_translate_integral_indicator : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), PsiUnr ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ φ₀ ∈ SB (κ → Fv F v), ∃ c : ℂ, c ≠ 0 ∧ ∃ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U ∧ IsCompact U ∧ 0 ∈ U ∧
      ∀ w, diagW (psiAt ψ v) μ (boxFun φ₀ φ₀) w = U.indicator (fun _ => c) w := by
  atlas_forward_decl GlobalTheory.InertLagInd.diagW_box_indicator
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DiagWSB

variable {F : Type} [Field F] [NumberField F] {v : Pl F} {κ : Type} [Fintype κ]

def diagG (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) (Φ : (κ ⊕ κ → Fv F v) → ℂ)
    (w : (κ → Fv F v) × (κ → Fv F v)) : ℂ :=
  ∫ x, ψ (x ⬝ᵥ w.2) * Φ (Sum.elim (x + w.1) x) ∂μ

omit [Fintype κ] in
theorem elim_add_elim {R : Type} [AddCommGroup R] (a b c d : κ → R) :
    Sum.elim a b + Sum.elim c d = Sum.elim (a + c) (b + d) := by
  funext i; rcases i with i | i <;> rfl

theorem elim_dot_elim {R : Type} [CommRing R] (a b c d : κ → R) :
    Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem diagW_eq (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) (Φ : (κ ⊕ κ → Fv F v) → ℂ)
    (w : (κ → Fv F v) × (κ → Fv F v)) :
    diagW ψ μ Φ w = ψ (⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * diagG ψ μ Φ w := by
  unfold diagW diagG
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [schr, elim_dot_elim, dotProduct_zero, zero_dotProduct, add_zero, elim_add_elim]
  rw [AddChar.map_add_eq_mul]
  ring

omit [Fintype κ] in
theorem continuous_elim_add (a : κ → Fv F v) : Continuous fun x : κ → Fv F v => Sum.elim (x + a) x :=
  continuous_pi fun i => by rcases i with i | i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop

theorem integrable_integrand (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) (μ : @Measure (κ → Fv F v) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) (Φ : (κ ⊕ κ → Fv F v) → ℂ) (hΦ : Φ ∈ SB (κ ⊕ κ → Fv F v))
    (w : (κ → Fv F v) × (κ → Fv F v)) :
    Integrable (fun x => ψ (x ⬝ᵥ w.2) * Φ (Sum.elim (x + w.1) x)) μ := by
  let _ : MeasurableSpace (κ → Fv F v) := borel _
  have _ : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  have _ := hμ
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (hψ.comp (continuous_id.dotProduct continuous_const)).mul
      (hΦ.1.continuous.comp (continuous_elim_add w.1))
  · apply HasCompactSupport.mul_left
    refine HasCompactSupport.intro (K := (fun y : κ ⊕ κ → Fv F v => y ∘ Sum.inr) '' tsupport Φ)
      (hΦ.2.image (by fun_prop)) ?_
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hx ⟨_, h, rfl⟩

theorem diagG_zero (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) :
    diagG ψ μ (0 : (κ ⊕ κ → Fv F v) → ℂ) = 0 := by
  funext w; simp [diagG]

theorem diagG_add (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) (μ : @Measure (κ → Fv F v) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) {Φ Ψ : (κ ⊕ κ → Fv F v) → ℂ} (hΦ : Φ ∈ SB (κ ⊕ κ → Fv F v))
    (hΨ : Ψ ∈ SB (κ ⊕ κ → Fv F v)) : diagG ψ μ (Φ + Ψ) = diagG ψ μ Φ + diagG ψ μ Ψ := by
  funext w
  simp only [diagG, Pi.add_apply, mul_add]
  exact integral_add (integrable_integrand ψ hψ μ hμ Φ hΦ w) (integrable_integrand ψ hψ μ hμ Ψ hΨ w)

theorem diagG_smul (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) (a : ℂ)
    (Φ : (κ ⊕ κ → Fv F v) → ℂ) : diagG ψ μ (a • Φ) = a • diagG ψ μ Φ := by
  funext w
  simp only [diagG, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  congr 1; funext x; ring

theorem diagG_schr (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) (Φ : (κ ⊕ κ → Fv F v) → ℂ) (p₁ p₂ q₁ q₂ : κ → Fv F v)
    (w : (κ → Fv F v) × (κ → Fv F v)) :
    diagG ψ μ (schr ψ (Sum.elim p₁ p₂, Sum.elim q₁ q₂) Φ) w =
      ψ (-(p₂ ⬝ᵥ w.2) + (w.1 - p₂) ⬝ᵥ q₁ - p₂ ⬝ᵥ q₂ + ⅟(2 : Fv F v) * (p₁ ⬝ᵥ q₁ + p₂ ⬝ᵥ q₂)) *
        diagG ψ μ Φ (w + (p₁ - p₂, q₁ + q₂)) := by
  let _ : MeasurableSpace (κ → Fv F v) := borel _
  have _ : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  have _ := hμ
  unfold diagG
  rw [← integral_sub_right_eq_self _ p₂, ← integral_const_mul]
  congr 1
  funext x
  simp only [schr, elim_dot_elim, elim_add_elim, Prod.fst_add, Prod.snd_add]
  have e : Sum.elim (x - p₂ + w.1 + p₁) (x - p₂ + p₂) = Sum.elim (x + (w.1 + (p₁ - p₂))) x := by
    congr 1 <;> abel
  rw [e, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub]
  ring

theorem sb_mul {X : Type} [TopologicalSpace X] {f g : X → ℂ} (hf : IsLocallyConstant f) (hg : g ∈ SB X) :
    (fun w => f w * g w) ∈ SB X :=
  ⟨hf.mul hg.1, hg.2.mul_left⟩

theorem sb_mul_translate {X : Type} [TopologicalSpace X] [AddGroup X] [ContinuousAdd X] {f g : X → ℂ}
    (hf : IsLocallyConstant f) (hg : g ∈ SB X) (t : X) : (fun w => f w * g (w + t)) ∈ SB X :=
  ⟨hf.mul (hg.1.comp_continuous (continuous_add_right t)), (hg.2.comp_homeomorph (Homeomorph.addRight t)).mul_left⟩

omit [Fintype κ] in
theorem isLocallyConstant_indicator {X : Type} [TopologicalSpace X] {S : Set X} (hS : IsClopen S) (c : ℂ) :
    IsLocallyConstant (S.indicator fun _ => c) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ S
  · exact ⟨S, hS.isOpen, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨Sᶜ, hS.compl.isOpen, hx, fun y hy => by rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

theorem diagW_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ]
    (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ Φ₀ ∈ SB (κ ⊕ κ → Fv F v), ∀ c : ℂ, c ≠ 0 → ∀ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U → IsCompact U →
      0 ∈ U → (∀ w, diagW ψ μ Φ₀ w = U.indicator (fun _ => c) w) →
    ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), diagW ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v)) := by
  intro F _ _ v κ _ ψ hψ h1 μ hμ Φ₀ hΦ₀ c hc U hUo hUc h0U hU Φ hΦ
  have _ := GlobalTheory.WeilM.nonarch_field (Fv F v)
  have hlc := GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ

  have hph : ∀ a : Fv F v, IsLocallyConstant fun w : (κ → Fv F v) × (κ → Fv F v) => ψ (a * (w.1 ⬝ᵥ w.2)) :=
    fun a => hlc.comp_continuous (continuous_const.mul (continuous_fst.dotProduct continuous_snd))
  let N : Submodule ℂ ((κ ⊕ κ → Fv F v) → ℂ) :=
    { carrier := {Φ | Φ ∈ SB (κ ⊕ κ → Fv F v) ∧ diagG ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v))}
      zero_mem' := ⟨zero_mem _, by rw [diagG_zero]; exact zero_mem _⟩
      add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, by
        rw [diagG_add ψ hψ μ hμ ha.1 hb.1]; exact add_mem ha.2 hb.2⟩
      smul_mem' := fun a Φ h => ⟨Submodule.smul_mem _ a h.1, by
        rw [diagG_smul]; exact Submodule.smul_mem _ a h.2⟩ }
  have hNle : N ≤ SB (κ ⊕ κ → Fv F v) := fun Φ h => h.1
  have hS : ∀ w, ∀ φ ∈ N, schr ψ w φ ∈ N := by
    rintro ⟨P, Q⟩ φ ⟨hφ1, hφ2⟩
    refine ⟨GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ (P, Q) φ hφ1, ?_⟩
    rw [← Sum.elim_comp_inl_inr P, ← Sum.elim_comp_inl_inr Q]
    have e : diagG ψ μ (schr ψ (Sum.elim (P ∘ Sum.inl) (P ∘ Sum.inr), Sum.elim (Q ∘ Sum.inl) (Q ∘ Sum.inr)) φ) =
        fun w => ψ (-((P ∘ Sum.inr) ⬝ᵥ w.2) + (w.1 - P ∘ Sum.inr) ⬝ᵥ (Q ∘ Sum.inl) - (P ∘ Sum.inr) ⬝ᵥ (Q ∘ Sum.inr) +
          ⅟(2 : Fv F v) * ((P ∘ Sum.inl) ⬝ᵥ (Q ∘ Sum.inl) + (P ∘ Sum.inr) ⬝ᵥ (Q ∘ Sum.inr))) *
          diagG ψ μ φ (w + (P ∘ Sum.inl - P ∘ Sum.inr, Q ∘ Sum.inl + Q ∘ Sum.inr)) :=
      funext fun w => diagG_schr ψ μ hμ φ _ _ _ _ w
    rw [e]
    refine sb_mul_translate (hlc.comp_continuous ?_) hφ2 _
    fun_prop

  have hUcl : IsClopen U := ⟨hUc.isClosed, hUo⟩
  have hW₀ : diagW ψ μ Φ₀ ∈ SB ((κ → Fv F v) × (κ → Fv F v)) := by
    rw [show diagW ψ μ Φ₀ = U.indicator (fun _ => c) from funext hU]
    exact ⟨isLocallyConstant_indicator hUcl c,
      HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _⟩
  have hG : ∀ Φ : (κ ⊕ κ → Fv F v) → ℂ, diagG ψ μ Φ =
      fun w => ψ (-⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * diagW ψ μ Φ w := by
    intro Φ
    funext w
    rw [diagW_eq, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  have h0N : Φ₀ ∈ N := ⟨hΦ₀, by rw [hG]; exact sb_mul (hph _) hW₀⟩
  have hne : Φ₀ ≠ 0 := by
    rintro rfl
    have h := hU 0
    rw [Set.indicator_of_mem h0U, diagW_zero] at h
    simp at h
    exact hc h.symm
  have hN := GlobalTheory.SchrIrred.schr_irreducible v ψ hψ h1 N hNle hS Φ₀ h0N hne
  have hΦN : Φ ∈ N := hN ▸ hΦ
  rw [show diagW ψ μ Φ = fun w => ψ (⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * diagG ψ μ Φ w from funext (diagW_eq ψ μ Φ)]
  exact sb_mul (hph _) hΦN.2

end GlobalTheory.DiagWSB

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDiagonalIntegral_mem_schwartzBruhat : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ Φ₀ ∈ SB (κ ⊕ κ → Fv F v), ∀ c : ℂ, c ≠ 0 → ∀ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U → IsCompact U → 0 ∈ U →
      (∀ w, diagW ψ μ Φ₀ w = U.indicator (fun _ => c) w) →
    ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), diagW ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v)) := by
  atlas_forward_decl GlobalTheory.DiagWSB.diagW_mem_SB
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.InertLagChar.LinForm

theorem hasCompactSupport_comp_of_leftInverse {X Y M : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    [Zero M] {f : X → Y} {l : Y → X} (hl : Continuous l) (hlf : ∀ x, l (f x) = x) {g : Y → M}
    (hg : HasCompactSupport g) : HasCompactSupport (g ∘ f) := by
  refine IsCompact.of_isClosed_subset (hg.image hl) isClosed_closure ?_
  refine closure_minimal ?_ (hg.image hl).isClosed
  intro x hx
  exact ⟨f x, subset_tsupport _ hx, hlf x⟩

theorem integrable_of_cont_cs {X : Type} [TopologicalSpace X] (μ : @Measure X (borel X))
    [IsFiniteMeasureOnCompacts μ] {f : X → ℂ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Integrable f μ := by
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  exact hf.integrable_of_hasCompactSupport hcs

end GlobalTheory.InertLagChar.LinForm

open GlobalTheory.InertLagChar.LinForm in
theorem GlobalTheory.InertLagChar.lagInt_linForm : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    (∀ Φ ∈ SB (κ ⊕ κ → Fv F v), diagW ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v))) →
    ∃ Λ : ((κ ⊕ κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Λ Φ = lagInt ψ μ ν j Φ := by
  intro F _ _ v κ _ ψ hψ μ hμ N ν hν j hj hdiag

  have hd : Continuous (fun x : κ → Fv F v => (Sum.elim x x : κ ⊕ κ → Fv F v)) := by
    refine continuous_pi fun i => ?_
    cases i <;> exact continuous_apply _
  have hdl : Continuous (fun z : κ ⊕ κ → Fv F v => fun i => z (Sum.inl i)) :=
    continuous_pi fun i => continuous_apply _

  have hin : ∀ w : (κ → Fv F v) × (κ → Fv F v), ∀ Φ ∈ SB (κ ⊕ κ → Fv F v),
      Integrable (fun x => schr ψ (Sum.elim w.1 0, Sum.elim w.2 0) Φ (Sum.elim x x)) μ := by
    intro w Φ hΦ
    have hs := GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ (Sum.elim w.1 0, Sum.elim w.2 0) Φ hΦ
    exact integrable_of_cont_cs μ (hs.1.continuous.comp hd)
      (hasCompactSupport_comp_of_leftInverse hdl (fun x => rfl) hs.2)
  have hschr_add : ∀ w (Φ Φ' : (κ ⊕ κ → Fv F v) → ℂ), schr ψ w (Φ + Φ') = schr ψ w Φ + schr ψ w Φ' := by
    intro w Φ Φ'; funext x; simp [schr, mul_add]
  have hschr_smul : ∀ w (c : ℂ) (Φ : (κ ⊕ κ → Fv F v) → ℂ), schr ψ w (c • Φ) = c • schr ψ w Φ := by
    intro w c Φ; funext x; simp [schr]; ring
  have hdiag_add : ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), ∀ Φ' ∈ SB (κ ⊕ κ → Fv F v),
      diagW ψ μ (Φ + Φ') = diagW ψ μ Φ + diagW ψ μ Φ' := by
    intro Φ hΦ Φ' hΦ'
    funext w
    simp only [diagW, Pi.add_apply, hschr_add]
    exact integral_add (hin w Φ hΦ) (hin w Φ' hΦ')
  have hdiag_smul : ∀ (c : ℂ) (Φ : (κ ⊕ κ → Fv F v) → ℂ), diagW ψ μ (c • Φ) = c • diagW ψ μ Φ := by
    intro c Φ
    funext w
    simp only [diagW, Pi.smul_apply, hschr_smul, smul_eq_mul]
    exact integral_const_mul (μ := μ) c _

  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  have hjc : Continuous j := IsModuleTopology.continuous_of_linearMap j
  have hlc : Continuous l := IsModuleTopology.continuous_of_linearMap l
  have hlj : ∀ y, l (j y) = y := fun y => by
    have := LinearMap.congr_fun hl y
    simpa using this
  have hout : ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Integrable (fun y => diagW ψ μ Φ (j y)) ν := by
    intro Φ hΦ
    have hs := hdiag Φ hΦ
    have hcs : HasCompactSupport (diagW ψ μ Φ ∘ (j : (Fin N → Fv F v) → (κ → Fv F v) × (κ → Fv F v))) :=
      hasCompactSupport_comp_of_leftInverse (f := (j : (Fin N → Fv F v) → (κ → Fv F v) × (κ → Fv F v)))
        (l := (l : (κ → Fv F v) × (κ → Fv F v) → (Fin N → Fv F v))) hlc hlj hs.2
    have hc : Continuous (diagW ψ μ Φ ∘ (j : (Fin N → Fv F v) → (κ → Fv F v) × (κ → Fv F v))) :=
      hs.1.continuous.comp hjc
    exact integrable_of_cont_cs ν hc hcs
  let f : SB (κ ⊕ κ → Fv F v) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => lagInt ψ μ ν j Φ.1
      map_add' := by
        intro Φ Φ'
        simp only [Submodule.coe_add, lagInt, hdiag_add _ Φ.2 _ Φ'.2, Pi.add_apply]
        exact integral_add (hout _ Φ.2) (hout _ Φ'.2)
      map_smul' := by
        intro c Φ
        simp only [Submodule.coe_smul, lagInt, hdiag_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul (μ := ν) c _ }
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  exact ⟨g, fun Φ hΦ => LinearMap.congr_fun hg ⟨Φ, hΦ⟩⟩
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangian_diagonal_integral_extends_linearForm : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    (∀ Φ ∈ SB (κ ⊕ κ → Fv F v), diagW ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v))) →
    ∃ Λ : ((κ ⊕ κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Λ Φ = lagInt ψ μ ν j Φ := by
  atlas_forward_decl GlobalTheory.InertLagChar.lagInt_linForm
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.integral_indicator_preimage_injective_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ],
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    ∀ c : ℂ, c ≠ 0 → ∀ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U → IsCompact U → 0 ∈ U →
    ∫ y, U.indicator (fun _ => c) (j y) ∂ν ≠ 0 := by
  intro F _ _ v κ _ N ν hν j hj c hc U hUo hUc h0
  letI : MeasurableSpace (Fin N → Fv F v) := borel _
  haveI : BorelSpace (Fin N → Fv F v) := ⟨rfl⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  have hjc : Continuous j := IsModuleTopology.continuous_of_linearMap j
  have hgc : Continuous g := IsModuleTopology.continuous_of_linearMap g
  set S : Set (Fin N → Fv F v) := j ⁻¹' U with hSdef
  have hSo : IsOpen S := hUo.preimage hjc
  have hSsub : S ⊆ g '' U := by
    intro y hy
    refine ⟨j y, hy, ?_⟩
    have := congrArg (fun f => f y) hg
    simpa using this
  have hfin : ν S < ⊤ := lt_of_le_of_lt (measure_mono hSsub) ((hUc.image hgc).measure_lt_top)
  have hpos : 0 < ν S := hSo.measure_pos ν ⟨0, by simp [hSdef, h0]⟩
  have heq : (fun y => U.indicator (fun _ => c) (j y)) = S.indicator (fun _ => c) := by
    funext y
    by_cases hy : j y ∈ U
    · have : y ∈ S := hy
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem this]
    · have : y ∉ S := hy
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem this]
  rw [heq, integral_indicator_const c hSo.measurableSet]
  refine smul_ne_zero ?_ hc
  rw [Measure.real]
  exact ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_injectiveSubspace_compactOpen_const_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ],
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    ∀ c : ℂ, c ≠ 0 → ∀ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U → IsCompact U → 0 ∈ U →
    ∫ y, U.indicator (fun _ => c) (j y) ∂ν ≠ 0 := by
  atlas_forward_decl GlobalTheory.integral_indicator_preimage_injective_ne_zero
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearForm_eq_zero_of_kills_productSchwartzBruhat : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ κ' : Type) [Fintype κ] [Fintype κ'] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ Λ : ((κ ⊕ κ' → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), Λ (boxFun φ₁ φ₂) = 0) → ∀ Φ ∈ SB (κ ⊕ κ' → Fv F v), Λ Φ = 0 := by
  first | exact @GlobalTheory.BoxSpan.boxSpan_ker | exact GlobalTheory.BoxSpan.boxSpan_ker | (intros; apply GlobalTheory.BoxSpan.boxSpan_ker <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LagIntTransl

def liftFst {R : Type} [CommRing R] {κ : Type} (a : (κ → R) × (κ → R)) : (κ ⊕ κ → R) × (κ ⊕ κ → R) :=
  (Sum.elim a.1 0, Sum.elim a.2 0)

theorem liftFst_add {R : Type} [CommRing R] {κ : Type} (a b : (κ → R) × (κ → R)) :
    liftFst (a + b) = liftFst a + liftFst b := by
  simp only [liftFst, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  refine Prod.ext ?_ ?_ <;> funext i <;> cases i <;> simp

theorem liftFst_dot {R : Type} [CommRing R] {κ : Type} [Fintype κ] (a b : (κ → R) × (κ → R)) :
    (liftFst a).1 ⬝ᵥ (liftFst b).2 = a.1 ⬝ᵥ b.2 := by
  simp [liftFst, dotProduct, Fintype.sum_sum_type]

theorem boxFun_schr {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a : (κ → R) × (κ → R)) (φ₁ φ₂ : (κ → R) → ℂ) :
    boxFun (schr ψ a φ₁) φ₂ = schr ψ (liftFst a) (boxFun φ₁ φ₂) := by
  funext z
  simp only [boxFun, schr, liftFst, dotProduct, Fintype.sum_sum_type, Function.comp_apply, Sum.elim_inl, Sum.elim_inr,
    Pi.add_apply, Pi.zero_apply, mul_zero, add_zero, mul_assoc]
  have e1 : (z + Sum.elim a.1 0) ∘ Sum.inl = z ∘ Sum.inl + a.1 := by funext i; simp
  have e2 : (z + Sum.elim a.1 0) ∘ Sum.inr = z ∘ Sum.inr := by funext i; simp
  rw [e1, e2]
  simp

theorem diagW_schr (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ)
    (μ : @Measure (κ → Fv F v) (borel _)) (a w : (κ → Fv F v) × (κ → Fv F v)) (h : w.1 ⬝ᵥ a.2 = a.1 ⬝ᵥ w.2)
    (φ₁ φ₂ : (κ → Fv F v) → ℂ) :
    diagW ψ μ (boxFun (schr ψ a φ₁) φ₂) w = diagW ψ μ (boxFun φ₁ φ₂) (w + a) := by
  unfold diagW
  rw [boxFun_schr]
  congr 1
  funext x
  have h' : (liftFst w).1 ⬝ᵥ (liftFst a).2 = (liftFst a).1 ⬝ᵥ (liftFst w).2 := by
    rw [liftFst_dot, liftFst_dot, h]
  have := GlobalTheory.MixXEvUniq.schr_add ψ (liftFst w) (liftFst a) h' (boxFun φ₁ φ₂)
  rw [← liftFst_add] at this
  rw [show ((Sum.elim (w + a).1 0, Sum.elim (w + a).2 0) : (κ ⊕ κ → Fv F v) × (κ ⊕ κ → Fv F v)) = liftFst (w + a) from rfl,
    this]
  rfl

theorem main : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), (∀ y y', (j y).1 ⬝ᵥ (j y').2 = (j y').1 ⬝ᵥ (j y).2) →
    ∀ (y₀ : Fin N → Fv F v) (φ₁ φ₂ : (κ → Fv F v) → ℂ),
      lagInt ψ μ ν j (boxFun (schr ψ (j y₀) φ₁) φ₂) = lagInt ψ μ ν j (boxFun φ₁ φ₂) := by
  intro F _ _ v κ _ ψ μ _ N ν hν j hj y₀ φ₁ φ₂
  unfold lagInt
  have h1 : ∀ y, diagW ψ μ (boxFun (schr ψ (j y₀) φ₁) φ₂) (j y) = diagW ψ μ (boxFun φ₁ φ₂) (j (y + y₀)) := fun y => by
    rw [diagW_schr F v κ ψ μ _ _ (hj y y₀), map_add]
  simp only [h1]
  letI : MeasurableSpace (Fin N → Fv F v) := borel _
  haveI : BorelSpace (Fin N → Fv F v) := ⟨rfl⟩
  exact integral_add_right_eq_self (μ := ν) (fun y => diagW ψ μ (boxFun φ₁ φ₂) (j y)) y₀

end GlobalTheory.LagIntTransl
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicIntegral_invariant_heisenberg_first_vars : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), (∀ y y', (j y).1 ⬝ᵥ (j y').2 = (j y').1 ⬝ᵥ (j y).2) →
    ∀ (y₀ : Fin N → Fv F v) (φ₁ φ₂ : (κ → Fv F v) → ℂ),
      lagInt ψ μ ν j (boxFun (schr ψ (j y₀) φ₁) φ₂) = lagInt ψ μ ν j (boxFun φ₁ φ₂) := by
  first | exact @GlobalTheory.LagIntTransl.main | exact GlobalTheory.LagIntTransl.main | (intros; apply GlobalTheory.LagIntTransl.main <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedAbsDet_mul_integral_comp_mulVec_finitePlace : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ (T : GL (Fin N) (Fv F v)) (f : (Fin N → Fv F v) → ℂ),
      ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det T) : ℝ) : ℂ) * ∫ y, f (T.val *ᵥ y) ∂ν = ∫ y, f y ∂ν := by
  first | exact @GlobalTheory.InertLagChar.nabs_det_mul_integral_comp_mulVec | exact GlobalTheory.InertLagChar.nabs_det_mul_integral_comp_mulVec | (intros; apply GlobalTheory.InertLagChar.nabs_det_mul_integral_comp_mulVec <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePlaceComponent_adeleNorm_eq_localNorm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (x : AE F E),
    evFin F v (Algebra.norm (AF F) x) = Algebra.norm (Fv F v) (compFin F E v x) := by
  first | exact @GlobalTheory.NormAtPlace.evFin_norm_eq | exact GlobalTheory.NormAtPlace.evFin_norm_eq | (intros; apply GlobalTheory.NormAtPlace.evFin_norm_eq <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertLagParam

open GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagUniq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev lift (v : Pl F) : Fv F v ⊗[F] E →ₗ[F] AE F E := (liftV v).rTensor E

theorem compFin_lift (v : Pl F) (t : Fv F v ⊗[F] E) : compFin F E v (lift v t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => simp [compFin, evFin_liftV]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem liftV_one_smul_eq (v : Pl F) (a : AE F E) : liftV v (1 : Fv F v) • a = lift v (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]
    simp [compFin]
  | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]

theorem compFin_smul (v : Pl F) (r : AF F) (a : AE F E) : compFin F E v (r • a) = evFin F v r • compFin F E v a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp [compFin, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem at_map_lift {α β : Type} (v : Pl F) (A : Matrix α β (Fv F v ⊗[F] E)) : At (evFin F v) (A.map (lift v)) := by
  intro u hu
  ext i k
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]
  induction A i k using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.smul_tmul', smul_eq_mul]
    rw [← smul_eq_mul, at_liftV v x u hu, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]

theorem eq_map_lift {α β : Type} (v : Pl F) (z : Matrix α β (AE F E)) (hz : At (evFin F v) z) :
    z = (z.map (compFin F E v)).map (lift v) := by
  conv_lhs => rw [← liftV_one_smul v z hz]
  ext i k
  simp only [Matrix.smul_apply, Matrix.map_apply, liftV_one_smul_eq]

theorem map_lift_compFin {α β : Type} (v : Pl F) (A : Matrix α β (Fv F v ⊗[F] E)) :
    (A.map (lift v)).map (compFin F E v) = A := by
  ext i k; simp [compFin_lift]

end GlobalTheory.InertLagParam
end

namespace GlobalTheory.InertLagParam
open GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagUniq
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem card_eq_of_inv {R : Type} [CommRing R] [Nontrivial R] {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (A : Matrix α β R) (B : Matrix β α R) (h1 : A * B = 1) (h2 : B * A = 1) :
    Fintype.card α = Fintype.card β := by
  let f : (β → R) ≃ₗ[R] (α → R) := LinearEquiv.ofLinear (Matrix.toLin' A) (Matrix.toLin' B)
    (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  have := f.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at this
  exact this.symm

theorem eq_zero_of_locCo {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ) (v : Pl F) (u : W) (hu : At (evFin F v) u) (h0 : locCo co v u = 0) : u = 0 := by
  have h1 : co.e u = liftV v (1 : Fv F v) • co.e u := by rw [← LinearEquiv.map_smul, liftV_one_smul v u hu]
  have h2 : co.e u = 0 := by
    rw [h1]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · have := congrArg (fun p => p.1 k) h0
      simp only [locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.fst_zero, Pi.zero_apply] at this
      simp [liftV_one_mul, this]
    · have := congrArg (fun p => p.2 k) h0
      simp only [locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.snd_zero, Pi.zero_apply] at this
      simp [liftV_one_mul, this]
  exact co.e.map_eq_zero_iff.1 h2

end GlobalTheory.InertLagParam

namespace GlobalTheory.InertLagParam

def mulLeft {R : Type} [CommRing R] (n m : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin m) R →ₗ[R] Matrix (Fin n) (Fin m) R where
  toFun x := A * x
  map_add' x y := Matrix.mul_add A x y
  map_smul' c x := Matrix.mul_smul A c x

theorem det_mulLeft {R : Type} [CommRing R] (n m : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    LinearMap.det (mulLeft n m A) = A.det ^ m := by
  let τ : Matrix (Fin n) (Fin m) R ≃ₗ[R] (Fin m → Fin n → R) :=
    { toFun := fun x k i => x i k
      invFun := fun y => Matrix.of fun i k => y k i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : (τ : _ →ₗ[R] _) ∘ₗ mulLeft n m A ∘ₗ (τ.symm : (Fin m → Fin n → R) →ₗ[R] _) =
      LinearMap.pi fun k : Fin m => Matrix.toLin' A ∘ₗ LinearMap.proj k := by
    refine LinearMap.ext fun y => ?_
    funext k i
    rfl
  rw [← LinearMap.det_conj (mulLeft n m A) τ, h, LinearMap.det_pi]
  simp [LinearMap.det_toLin']

end GlobalTheory.InertLagParam

namespace GlobalTheory.InertLagParam
open GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagUniq

theorem param : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (v : Pl F)
    (m : ℕ) (C : Matrix (Fin d) (Fin m) (AE F E)), IsLagrAt σ W v C →
    d = 2 * m ∧ ∃ (N : ℕ) (j : (Fin N → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))
      (ζ : (Fin N → Fv F v) → Matrix (Fin n) (Fin m) (AE F E)), Function.Injective j ∧
      (∀ y, At (evFin F v) (ζ y) ∧ locCo M.co v (ζ y * Cᵀ) = j y) ∧
      (∀ z : Matrix (Fin n) (Fin m) (AE F E), At (evFin F v) z → ∃ y, ζ y = z) ∧
      ∀ s : GL (Fin n) (AE F E), ∃ T : GL (Fin N) (Fv F v), (∀ y, ζ (T.val *ᵥ y) = s.val * ζ y) ∧
        T.val.det = Algebra.norm (Fv F v) (compFin F E v s.val.det) ^ m := by
  intro F E _ _ _ _ _ σ n d X W M v m C hC
  obtain ⟨h0, Cx, P, hx, h1, h2⟩ := hC
  have hP1 : P.toRows₁ * C.map (compFin F E v) = 1 := by
    have h2' := h2
    rw [← Matrix.fromRows_toRows P, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one,
      Matrix.fromBlocks_inj] at h2'
    exact h2'.1
  refine ⟨?_, ?_⟩
  · have := card_eq_of_inv _ _ h1 h2
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  let Z := Matrix (Fin n) (Fin m) (Fv F v ⊗[F] E)
  let N := Module.finrank (Fv F v) Z
  let e : (Fin N → Fv F v) ≃ₗ[Fv F v] Z := (Module.finBasis (Fv F v) Z).equivFun.symm
  let ζ : (Fin N → Fv F v) → Matrix (Fin n) (Fin m) (AE F E) := fun y => (e y).map (lift v)
  have hζat : ∀ y, At (evFin F v) (ζ y) := fun y => at_map_lift v _
  have hζc : ∀ y, (ζ y).map (compFin F E v) = e y := fun y => map_lift_compFin v _
  have hζadd : ∀ y y', ζ (y + y') = ζ y + ζ y' := fun y y' => by
    simp only [ζ, map_add]
    exact Matrix.map_add _ (map_add _) _ _
  have hζsmul : ∀ (a : Fv F v) y, ζ (a • y) = liftV v a • ζ y := fun a y => by
    have hat : At (evFin F v) (liftV v a • ζ y) := fun u hu => by rw [smul_comm, hζat y u hu, smul_zero]
    rw [eq_map_lift v _ hat]
    congr 1
    ext i k
    simp [ζ, compFin_smul, evFin_liftV, compFin_lift] <;> rfl
  let j : (Fin N → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun y => locCo M.co v (ζ y * Cᵀ)
      map_add' := fun y y' => by rw [hζadd, Matrix.add_mul, map_add]
      map_smul' := fun a y => by
        rw [hζsmul, Matrix.smul_mul]
        ext k <;> simp [locCo, evFin_liftV, -Matrix.smul_mul] }
  refine ⟨N, j, ζ, ?_, fun y => ⟨hζat y, rfl⟩, fun z hz => ?_, fun s => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hu := eq_zero_of_locCo M.co v _ (at_mul v _ (hζat y) _) hy
    have h3 : e y * (C.map (compFin F E v))ᵀ = 0 := by
      have := congrArg (fun x => Matrix.map x (compFin F E v)) hu
      simp only [Matrix.map_mul, Matrix.transpose_map, hζc, Matrix.map_zero _ (map_zero _)] at this
      exact this
    have h4 : e y = 0 := by
      have h5 : e y = e y * (P.toRows₁ * C.map (compFin F E v))ᵀ := by
        rw [hP1, Matrix.transpose_one, Matrix.mul_one]
      rw [h5, Matrix.transpose_mul, ← Matrix.mul_assoc, h3, Matrix.zero_mul]
    exact e.map_eq_zero_iff.1 h4
  · exact ⟨e.symm (z.map (compFin F E v)), by simp only [ζ, LinearEquiv.apply_symm_apply]; exact (eq_map_lift v z hz).symm⟩
  · let sv := s.val.map (compFin F E v)
    let L : Z →ₗ[Fv F v] Z := (mulLeft n m sv).restrictScalars (Fv F v)
    let f := e.symm.toLinearMap ∘ₗ L ∘ₗ e.toLinearMap
    have hdet : (LinearMap.toMatrix' f).det = Algebra.norm (Fv F v) (compFin F E v s.val.det) ^ m := by
      rw [LinearMap.det_toMatrix']
      have hf : f = e.symm.toLinearMap ∘ₗ L ∘ₗ e.symm.symm.toLinearMap := rfl
      rw [hf, LinearMap.det_conj, LinearMap.det_restrictScalars, det_mulLeft, map_pow, RingHom.map_det]
      rfl
    have hs : IsUnit s.val.det := by simpa using (Matrix.GeneralLinearGroup.det s).isUnit
    have hne : (LinearMap.toMatrix' f).det ≠ 0 := by
      rw [hdet]
      exact (((hs.map (compFin F E v)).map (Algebra.norm (Fv F v))).pow m).ne_zero
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hne, fun y => ?_, hdet⟩
    show ζ (LinearMap.toMatrix' f *ᵥ y) = s.val * ζ y
    rw [LinearMap.toMatrix'_mulVec]
    have hat : At (evFin F v) (s.val * ζ y) := fun u hu => by rw [← Matrix.mul_smul, hζat y u hu, Matrix.mul_zero]
    rw [eq_map_lift v _ hat, Matrix.map_mul, hζc]
    simp [ζ, f, L, mulLeft, sv]

end GlobalTheory.InertLagParam
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangianColumns_linear_parametrisation_finitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (v : Pl F)
    (m : ℕ) (C : Matrix (Fin d) (Fin m) (AE F E)), IsLagrAt σ W v C →
    d = 2 * m ∧ ∃ (N : ℕ) (j : (Fin N → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))
      (ζ : (Fin N → Fv F v) → Matrix (Fin n) (Fin m) (AE F E)), Function.Injective j ∧
      (∀ y, At (evFin F v) (ζ y) ∧ locCo M.co v (ζ y * Cᵀ) = j y) ∧
      (∀ z : Matrix (Fin n) (Fin m) (AE F E), At (evFin F v) z → ∃ y, ζ y = z) ∧
      ∀ s : GL (Fin n) (AE F E), ∃ T : GL (Fin N) (Fv F v), (∀ y, ζ (T.val *ᵥ y) = s.val * ζ y) ∧
        T.val.det = Algebra.norm (Fv F v) (compFin F E v s.val.det) ^ m := by
  first | exact @GlobalTheory.InertLagParam.param | exact GlobalTheory.InertLagParam.param | (intros; apply GlobalTheory.InertLagParam.param <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.InertLagChar

theorem at_mul_left' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    {a b c : Type} [Fintype b] (P : Matrix a b (AE F E)) {z : Matrix b c (AE F E)} (hz : At (evFin F v) z) :
    At (evFin F v) (P * z) := fun u hu => by rw [← Matrix.mul_smul, hz u hu, Matrix.mul_zero]

theorem at_mul_right' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    {a b c : Type} [Fintype b] {z : Matrix a b (AE F E)} (hz : At (evFin F v) z) (P : Matrix b c (AE F E)) :
    At (evFin F v) (z * P) := fun u hu => by rw [← Matrix.smul_mul, hz u hu, Matrix.zero_mul]

theorem at_fromCols_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    {a b c : Type} {u : Matrix a b (AE F E)} (hu : At (evFin F v) u) :
    At (evFin F v) (Matrix.fromCols uᵀ (0 : Matrix b c (AE F E))) := fun t ht => by
  ext i j
  rcases j with j | j
  · have := congrArg (fun M => M j i) (hu t ht)
    simpa using this
  · simp

theorem fromCols_add_fromCols {R : Type} [Add R] {a b c : Type} (x z : Matrix a b R) (y w : Matrix a c R) :
    Matrix.fromCols x y + Matrix.fromCols z w = Matrix.fromCols (x + z) (y + w) := by
  ext i j; rcases j with j | j <;> rfl

theorem fromCols_mul_transpose_split {R : Type} [CommRing R] {a b : Type} [Fintype a] (u : Matrix a b R)
    (P : Matrix (a ⊕ a) (a ⊕ a) R) :
    Matrix.fromCols uᵀ (0 : Matrix b a R) * Pᵀ =
      Matrix.fromCols (P.toBlocks₂₁ * u)ᵀ (P.toBlocks₂₁ * u)ᵀ + Matrix.fromCols ((P.toBlocks₁₁ - P.toBlocks₂₁) * u)ᵀ 0 := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks P, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]
  rw [fromCols_add_fromCols]
  simp only [Matrix.zero_mul, add_zero, Matrix.transpose_mul, Matrix.transpose_sub, Matrix.mul_sub]
  congr 1
  abel

theorem diagW_omd_point : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W)
    (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ (v : Pl F) (m : ℕ) (C : Matrix (Fin d) (Fin m) (AE F E)), IsLagrAt σ W v C →
    ∀ d' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d),
    (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
    ∀ dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
    IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd →
    ∀ omd : UG (cA σ) (dbl (incM F X.J)) →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ),
    IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd →
    ∀ l : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ℂ,
    (∀ z : Matrix (Fin d) (Fin n) (AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      l (dd.rho ψ (z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) Φ) = l Φ) →
    ∀ r₀ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ,
    (∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), Rest (evFin F v) φ r₀) →
    ∀ c₀ : ℂ, c₀ ≠ 0 → ∀ μ : @Measure (Fin n × Fin d → Fv F v) (borel _),
    (∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), l (tens (evFin F v) φ r₀) = c₀ * ∫ x, φ (Sum.elim x x) ∂μ) →
    ∀ (p : UG (cA σ) (dbl (incM F X.J))) (ρ₀ : ℂ),
    (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), l (omd p Φ) = ρ₀ * l Φ) →
    ∀ Φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), ∀ Φ₁ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
    Acts (evFin F v) (omd p) Φ Φ₁ → ∀ z : Matrix (Fin n) (Fin m) (AE F E), At (evFin F v) z →
      diagW (psiAt ψ v) μ Φ₁ (locCo M.co v (z * Cᵀ)) = ρ₀ * diagW (psiAt ψ v) μ Φ (locCo M.co v
        (((((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₁₁ - ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₂₁) * z) * Cᵀ)) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ v m C hL d' hd' dd hdd omd hsp l hlinv r₀ hr₀ c₀ hc₀ μ hlint p ρ₀ hρ Φ hΦ Φ₁ hΦ₁ hacts z hz

  have hstep : ∀ γ, At (evFin F v) γ → ∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
      dd.rho ψ γ (tens (evFin F v) φ r₀) = tens (evFin F v) (schr (psiAt ψ v) (locCo dd v γ) φ) r₀ :=
    fun γ hγ φ hφ => GlobalTheory.VacBridge.rho_acts_locCo dd ψ v γ hγ φ r₀ (hr₀ φ hφ)
  have hmem : ∀ γ, At (evFin F v) γ → ∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
      dd.rho ψ γ (tens (evFin F v) φ r₀) ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := fun γ hγ φ hφ => by
    rw [hstep γ hγ φ hφ]
    exact (hr₀ _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ v _ φ hφ)).2
  have hW : ∀ u : Matrix (Fin n) (Fin d) (AE F E), locCo dd v (Matrix.fromCols uᵀ 0) =
      (Sum.elim (locCo M.co v u).1 0, Sum.elim (locCo M.co v u).2 0) := fun u => by
    ext k <;> rcases k with k | k <;> simp [locCo, hdd uᵀ 0, hd' u]
  have hkey : ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) u →
      ∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
      c₀ * diagW (psiAt ψ v) μ φ (locCo M.co v u) = l (dd.rho ψ (Matrix.fromCols uᵀ 0) (tens (evFin F v) φ r₀)) :=
    fun u hu φ hφ => by
      rw [hstep _ (at_fromCols_zero hu) φ hφ, hlint _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ v _ φ hφ), hW, diagW]

  set P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) with hP
  set u : Matrix (Fin n) (Fin d) (AE F E) := z * Cᵀ with hu
  set u' : Matrix (Fin n) (Fin d) (AE F E) := ((P.toBlocks₁₁ - P.toBlocks₂₁) * z) * Cᵀ with hu'
  have hzat : At (evFin F v) u := at_mul_right' hz _
  have hu'at : At (evFin F v) u' := at_mul_right' (at_mul_left' _ hz) _
  set xm : Matrix (Fin d) (Fin n) (AE F E) := (P.toBlocks₂₁ * u)ᵀ with hxm
  set δ : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) :=
    xm * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ with hδ
  have hδc : δ = Matrix.fromCols xm xm := by
    rw [hδ, diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
  set Ψ := tens (evFin F v) Φ r₀ with hΨ
  have hΨm : Ψ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := (hr₀ Φ hΦ).2
  have h1 : tens (evFin F v) Φ₁ r₀ = omd p Ψ := (hacts r₀ (hr₀ Φ hΦ)).symm
  set γ := actB (cA σ) p⁻¹ (Matrix.fromCols uᵀ (0 : Matrix (Fin d) (Fin n) (AE F E))) with hγ
  have hγat : At (evFin F v) γ := at_mul_right' (at_fromCols_zero hzat) _
  have hinv : dd.rho ψ (Matrix.fromCols uᵀ 0) (omd p Ψ) = omd p (dd.rho ψ γ Ψ) := by
    have h := hsp.impl p⁻¹ (Matrix.fromCols uᵀ 0) (omd p Ψ) (hsp.pres p Ψ hΨm)
    have e1 : ∀ Y, omd p⁻¹ (omd p Y) = Y := fun Y => by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have e2 : ∀ Y, omd p (omd p⁻¹ Y) = Y := fun Y => by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [e1] at h
    rw [← h, e2]
  have hdec : γ = δ + Matrix.fromCols u'ᵀ 0 := by
    have e : u' = (P.toBlocks₁₁ - P.toBlocks₂₁) * u := by rw [hu', hu, Matrix.mul_assoc]
    rw [e, hδc, hxm]
    exact fromCols_mul_transpose_split u P
  have hsum : ∀ Y, dd.rho ψ γ Y = dd.rho ψ δ (dd.rho ψ (Matrix.fromCols u'ᵀ 0) Y) := fun Y => by
    rw [hdec]
    unfold Darboux.rho
    rw [map_add]
    apply GlobalTheory.MixXEvUniq.schr_add
    rw [hδc, hdd xm xm, hdd u'ᵀ 0, hd' u', map_zero, hxm, hd' (P.toBlocks₂₁ * u)]
    simp only [Prod.fst_zero, Prod.snd_zero, neg_zero, sumElim_dotProduct_sumElim, dotProduct_zero,
      zero_dotProduct, add_zero]
    have hform := M.co.form (P.toBlocks₂₁ * u) u'
    have h0 := GlobalTheory.InertVacIso.symp_eq_zero_of_lagAt σ X.J W v C hL (-1) (P.toBlocks₂₁ * u) u'
      ⟨at_mul_left' _ hzat, P.toBlocks₂₁ * z, by rw [hu, Matrix.mul_assoc]⟩ ⟨hu'at, (P.toBlocks₁₁ - P.toBlocks₂₁) * z, rfl⟩
    rw [h0] at hform
    exact (sub_eq_zero.mp hform.symm)
  have hW'm : dd.rho ψ (Matrix.fromCols u'ᵀ 0) Ψ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) :=
    hmem _ (at_fromCols_zero hu'at) Φ hΦ
  have hγm : dd.rho ψ γ Ψ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := hmem γ hγat Φ hΦ
  apply mul_left_cancel₀ hc₀
  rw [hkey u hzat Φ₁ hΦ₁, h1, hinv, hρ _ hγm, hsum, hδ, hlinv xm _ hW'm, ← hkey u' hu'at Φ hΦ]
  ring

end GlobalTheory.InertLagChar
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeilOperator_diagonalIntegral_heisenberg_point : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W)
    (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ (v : Pl F) (m : ℕ) (C : Matrix (Fin d) (Fin m) (AE F E)), IsLagrAt σ W v C →
    ∀ d' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d),
    (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
    ∀ dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
    IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd →
    ∀ omd : UG (cA σ) (dbl (incM F X.J)) →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ),
    IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd →
    ∀ l : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ℂ,
    (∀ z : Matrix (Fin d) (Fin n) (AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      l (dd.rho ψ (z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) Φ) = l Φ) →
    ∀ r₀ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ,
    (∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), Rest (evFin F v) φ r₀) →
    ∀ c₀ : ℂ, c₀ ≠ 0 → ∀ μ : @Measure (Fin n × Fin d → Fv F v) (borel _),
    (∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), l (tens (evFin F v) φ r₀) = c₀ * ∫ x, φ (Sum.elim x x) ∂μ) →
    ∀ (p : UG (cA σ) (dbl (incM F X.J))) (ρ₀ : ℂ),
    (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), l (omd p Φ) = ρ₀ * l Φ) →
    ∀ Φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), ∀ Φ₁ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
    Acts (evFin F v) (omd p) Φ Φ₁ → ∀ z : Matrix (Fin n) (Fin m) (AE F E), At (evFin F v) z →
      diagW (psiAt ψ v) μ Φ₁ (locCo M.co v (z * Cᵀ)) = ρ₀ * diagW (psiAt ψ v) μ Φ (locCo M.co v
        (((((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₁₁ - ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₂₁) * z) * Cᵀ)) := by
  atlas_forward_decl GlobalTheory.InertLagChar.diagW_omd_point
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelParabolic_leviInverse_quotient_det_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 →
    ∀ (v : Pl F) (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), At (evFin F v) ((p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) - 1) →
    (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.val →
    At (evFin F v) (t.val.det - 1) ∧ At (evFin F v) (Algebra.norm (AF F) t.val.det - 1) ∧
      ∃ s : GL (Fin n) (AE F E), s.val = ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₁₁ - ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₂₁ ∧
        Algebra.norm (AF F) s.val.det = Algebra.norm (AF F) t.val.det := by
  first | exact @GlobalTheory.InertLagLevi.levi_det | exact GlobalTheory.InertLagLevi.levi_det | (intros; apply GlobalTheory.InertLagLevi.levi_det <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BoxAct

theorem tens_boxFun {F : Type} [Field F] [NumberField F] {R κ κ' : Type} (ev : AF F → R)
    (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) (r₁ : (κ → AF F) → ℂ) (r₂ : (κ' → AF F) → ℂ) :
    tens ev (boxFun φ₁ φ₂) (boxFun r₁ r₂) = boxFun (tens ev φ₁ r₁) (tens ev φ₂ r₂) := by
  funext x
  simp only [tens, boxFun, Function.comp_def]
  ring

theorem boxFun_acts : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ κ' : Type) [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (Td : ((κ ⊕ κ' → AF F) → ℂ) → (κ ⊕ κ' → AF F) → ℂ),
    (∀ Φ₁ ∈ schA F κ, ∀ Φ₂ ∈ schA F κ', Td (boxFun Φ₁ Φ₂) = boxFun (T Φ₁) Φ₂) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), ∀ (φ₁' : (κ → Fv F v) → ℂ) (Φ' : (κ ⊕ κ' → Fv F v) → ℂ),
      Acts (evFin F v) T φ₁ φ₁' → Acts (evFin F v) Td (boxFun φ₁ φ₂) Φ' → Φ' = boxFun φ₁' φ₂ := by
  intro F _ _ v κ κ' _ _ T Td hT φ₁ hφ₁ φ₂ hφ₂ φ₁' Φ' h₁ hd
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  obtain ⟨R', hR0', hR'⟩ := GlobalTheory.RestWitness.exists_rest κ' v
  have r₁ := hR φ₁ hφ₁
  have r₂ := hR' φ₂ hφ₂
  have hRest : Rest (evFin F v) (boxFun φ₁ φ₂) (boxFun R R') := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · have hz₁ : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inl i)
      have hz₂ : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inr i)
      have e₁ := r₁.1 (x ∘ Sum.inl) (z ∘ Sum.inl) hz₁
      have e₂ := r₂.1 (x ∘ Sum.inr) (z ∘ Sum.inr) hz₂
      simp only [boxFun]
      have a₁ : (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl := rfl
      have a₂ : (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr := rfl
      rw [a₁, a₂, e₁, e₂]
    · rw [tens_boxFun]
      exact GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ' _ r₁.2 _ r₂.2
  have key : tens (evFin F v) Φ' (boxFun R R') = tens (evFin F v) (boxFun φ₁' φ₂) (boxFun R R') := by
    rw [← hd _ hRest, tens_boxFun, hT _ r₁.2 _ r₂.2, h₁ R r₁, tens_boxFun]
  funext y
  let z : κ ⊕ κ' → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
  have hz : ∀ (ι : Type) (w : ι → κ ⊕ κ'), At (evFin F v) (z ∘ w) := by
    intro ι w u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v (y (w i)) u hu
  have hRz : boxFun R R' z = R 0 * R' 0 := by
    have e₁ := (hR φ₁ hφ₁).1 0 (z ∘ Sum.inl) (hz κ Sum.inl)
    have e₂ := (hR' φ₂ hφ₂).1 0 (z ∘ Sum.inr) (hz κ' Sum.inr)
    rw [zero_add] at e₁ e₂
    simp only [boxFun]
    rw [e₁, e₂]
  have hev : (fun i => evFin F v (z i)) = y := by
    funext i; exact GlobalTheory.LatVac.evFin_liftV v (y i)
  have e := congrFun key z
  simp only [tens, hev, hRz] at e
  exact mul_right_cancel₀ (mul_ne_zero hR0 hR0') e

end GlobalTheory.BoxAct
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localProduct_acts_of_adelicProduct_acts_first : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ κ' : Type) [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (Td : ((κ ⊕ κ' → AF F) → ℂ) → (κ ⊕ κ' → AF F) → ℂ),
    (∀ Φ₁ ∈ schA F κ, ∀ Φ₂ ∈ schA F κ', Td (boxFun Φ₁ Φ₂) = boxFun (T Φ₁) Φ₂) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), ∀ (φ₁' : (κ → Fv F v) → ℂ) (Φ' : (κ ⊕ κ' → Fv F v) → ℂ),
      Acts (evFin F v) T φ₁ φ₁' → Acts (evFin F v) Td (boxFun φ₁ φ₂) Φ' → Φ' = boxFun φ₁' φ₂ := by
  atlas_forward_decl GlobalTheory.BoxAct.boxFun_acts
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.InertLagChar

theorem box_mem_SB {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

def boxL {k κ κ' : Type} [CommRing k] (φ₂ : (κ' → k) → ℂ) : ((κ → k) → ℂ) →ₗ[ℂ] ((κ ⊕ κ' → k) → ℂ) where
  toFun φ := boxFun φ φ₂
  map_add' a b := by funext x; simp [boxFun, add_mul]
  map_smul' a b := by funext x; simp [boxFun, mul_assoc]

variable {F : Type} [Field F] [NumberField F]

theorem one_sub_smul_of_at {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl F} {u : M} (hu : At (evFin F v) u) :
    (1 - liftV v (1 : Fv F v)) • u = 0 := hu _ (by rw [map_sub, map_one, evFin_liftV, sub_self])

theorem smul_of_at {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl F} {u : M} (hu : At (evFin F v) u) :
    liftV v (1 : Fv F v) • u = u := by
  have h := one_sub_smul_of_at hu
  rw [sub_smul, one_smul] at h
  exact (sub_eq_zero.1 h).symm

theorem at_of_one_sub_smul {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl F} {u : M}
    (h : (1 - liftV v (1 : Fv F v)) • u = 0) : At (evFin F v) u := fun t ht => by
  have h1 : t * (1 - liftV v (1 : Fv F v)) = t := by
    have h2 := at_liftV v (1 : Fv F v) t ht
    rw [smul_eq_mul] at h2
    rw [mul_sub, mul_one, h2, sub_zero]
  rw [← h1, mul_smul, h, smul_zero]

def Scales {κ : Type} [Fintype κ] (v : Pl F) (Λ : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (a : ℂ) : Prop :=
  ∀ Φ ∈ SB (κ → Fv F v), ∃ Φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) T Φ Φ₁ ∧ Λ Φ₁ = a * Λ Φ

theorem Scales.mul {κ : Type} [Fintype κ] {v : Pl F} {Λ : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ}
    {T T' : Module.End ℂ ((κ → AF F) → ℂ)} {a a' : ℂ} (h : Scales v Λ T a) (h' : Scales v Λ T' a')
    (hp : ∀ Φ ∈ schA F κ, T' Φ ∈ schA F κ) : Scales v Λ (T * T') (a * a') := by
  intro Φ hΦ
  obtain ⟨Φ₁, hΦ₁, hA₁, e₁⟩ := h' Φ hΦ
  obtain ⟨Φ₂, hΦ₂, hA₂, e₂⟩ := h Φ₁ hΦ₁
  refine ⟨Φ₂, hΦ₂, fun r hr => ?_, by rw [e₂, e₁, mul_assoc]⟩
  have hr1 : Rest (evFin F v) Φ₁ r := ⟨hr.1, by rw [← hA₁ r hr]; exact hp _ hr.2⟩
  show T (T' _) = _
  rw [hA₁ r hr, hA₂ r hr1]

theorem Scales.unique {κ : Type} [Fintype κ] {v : Pl F} {Λ : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ}
    {T : Module.End ℂ ((κ → AF F) → ℂ)} {a a' : ℂ} (h : Scales v Λ T a) (h' : Scales v Λ T a')
    {Φ : (κ → Fv F v) → ℂ} (hΦ : Φ ∈ SB (κ → Fv F v)) (h0 : Λ Φ ≠ 0) : a = a' := by
  obtain ⟨Φ₁, -, hA₁, e₁⟩ := h Φ hΦ
  obtain ⟨Φ₂, -, hA₂, e₂⟩ := h' Φ hΦ
  have e : Φ₁ = Φ₂ := GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v Φ Φ₁ Φ₂ hΦ fun r hr => (hA₁ r hr).symm.trans (hA₂ r hr)
  rw [e, e₂] at e₁
  exact (mul_right_cancel₀ h0 e₁).symm

theorem scales_one {κ : Type} [Fintype κ] (v : Pl F) (Λ : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) : Scales v Λ 1 1 :=
  fun Φ hΦ => ⟨Φ, hΦ, fun _ _ => rfl, (one_mul _).symm⟩

theorem scales_of_box {κ : Type} [Fintype κ] {v : Pl F} (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (Λ : ((κ ⊕ κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (T : Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)) (a : ℂ)
    (hex : ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), ∃ Φ₁ ∈ SB (κ ⊕ κ → Fv F v), Acts (evFin F v) T Φ Φ₁)
    (r : (κ ⊕ κ → AF F) → ℂ) (hr0 : r 0 ≠ 0) (hr : ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Rest (evFin F v) Φ r)
    (hbox : ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v), ∀ Φ₁, Acts (evFin F v) T (boxFun φ₁ φ₂) Φ₁ →
      Λ Φ₁ = a * Λ (boxFun φ₁ φ₂)) : Scales v Λ T a := by
  let S : ((κ ⊕ κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ ⊕ κ → Fv F v) → ℂ) :=
    { toFun := fun f t => (r 0)⁻¹ * T (tens (evFin F v) f r) (fun i => liftV v (t i))
      map_add' := fun f f' => by
        have e : tens (evFin F v) (f + f') r = tens (evFin F v) f r + tens (evFin F v) f' r := by
          funext x; simp [tens, add_mul]
        funext t; simp only [e, map_add, Pi.add_apply]; ring
      map_smul' := fun c f => by
        have e : tens (evFin F v) (c • f) r = c • tens (evFin F v) f r := by
          funext x; simp [tens, mul_assoc]
        funext t; simp only [e, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hS : ∀ f ∈ SB (κ ⊕ κ → Fv F v), ∀ f₁, Acts (evFin F v) T f f₁ → f₁ = S f := by
    intro f hf f₁ hA
    funext t
    show f₁ t = (r 0)⁻¹ * T (tens (evFin F v) f r) (fun i => liftV v (t i))
    rw [hA r (hr f hf)]
    have hat : At (evFin F v) (fun i => liftV v (t i)) := by
      intro u hu; funext i; exact at_liftV v _ u hu
    have h1 : r (fun i => liftV v (t i)) = r 0 := by
      simpa using (hr f hf).1 0 _ hat
    simp only [tens, h1, evFin_liftV]
    field_simp
  have key := GlobalTheory.T.linearForm_eq_zero_of_kills_productSchwartzBruhat F v κ κ ψ hψ hψ1 (Λ ∘ₗ S - a • Λ) (fun φ₁ h₁ φ₂ h₂ => by
    obtain ⟨Φ₁, -, hA⟩ := hex _ (box_mem_SB h₁ h₂)
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply]
    rw [← hS _ (box_mem_SB h₁ h₂) Φ₁ hA, hbox φ₁ h₁ φ₂ h₂ Φ₁ hA, sub_self])
  intro Φ hΦ
  obtain ⟨Φ₁, hΦ₁, hA⟩ := hex Φ hΦ
  refine ⟨Φ₁, hΦ₁, hA, ?_⟩
  have h := key Φ hΦ
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply] at h
  rw [hS Φ hΦ Φ₁ hA]
  exact sub_eq_zero.1 h

theorem char_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (AE F E)), GlobalTheory.InertVacLag.IsLagrAt σ G.W v C →
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    (∃ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), l φ ≠ 0) →
    ∀ c : UA σ G.V'.J → ℂ, (∀ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) φ φ₁ → l φ₁ = c g * l φ) →
    ∀ g ∈ UAt σ G.V' (evFin F v), c g = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hv m C hC l hl hne c hc g hg
  obtain ⟨h2, -, hunr⟩ := hT.base.inert v w hin
  have hψc : Continuous (psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hT.base.std.1 v
  have hψ1 : psiAt B.ψ v ≠ 1 := by
    obtain ⟨t, ht⟩ := GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace B.ψ hT.base.std v
    intro h; exact ht (by rw [h]; rfl)
  have hJ : IsUnit G.V'.J.det := GlobalTheory.isUnit_det_of_isHerm F E σ B a' G.V' _ _ hT.geo.hV'
  obtain ⟨-, ⟨d', hd', hBw⟩, -⟩ := hT.weil'
  obtain ⟨-, dd, omd, hdd, ⟨-, hspl, hsieg⟩, hres⟩ := hBw
  obtain ⟨L, hL, hinv, r₀, hr₀, c₀, hc₀, μ, hμ, hLφ, -⟩ := GlobalTheory.T.exists_admitted_diagonal_integral_linearForm F E σ a a' G B.ψ d' dd hdd v
  obtain ⟨hdm, N, j, ζ, hj, hζ, hζs, hT'⟩ := GlobalTheory.T.lagrangianColumns_linear_parametrisation_finitePlace F E σ a' (a + a') G.V' G.W G.M' v m C hC
  obtain ⟨ν, hν⟩ : ∃ ν : @Measure (Fin N → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν := by
    letI : MeasurableSpace (Fin N → Fv F v) := borel _
    haveI : BorelSpace (Fin N → Fv F v) := ⟨rfl⟩
    exact ⟨Measure.addHaar, inferInstance⟩
  obtain ⟨φ₀, hφ₀, c₁, hc₁, U, hUo, hUc, hU0, hU⟩ := GlobalTheory.T.diagonal_integral_heisenberg_translate_integral_indicator F v _ B.ψ hunr h2 μ hμ
  have hSB := GlobalTheory.T.heisenbergDiagonalIntegral_mem_schwartzBruhat F v _ _ hψc hψ1 μ hμ _ (box_mem_SB hφ₀ hφ₀) c₁ hc₁ U hUo hUc hU0 hU
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.lagrangian_diagonal_integral_extends_linearForm F v _ _ hψc μ hμ N ν hν j hj hSB
  have hΛ0 : Λ (boxFun φ₀ φ₀) ≠ 0 := by
    rw [hΛ _ (box_mem_SB hφ₀ hφ₀), lagInt]
    simp only [hU]
    exact GlobalTheory.T.integral_injectiveSubspace_compactOpen_const_ne_zero F v _ N ν hν j hj c₁ hc₁ U hUo hUc hU0
  have hlag : ∀ y, ζ y * Cᵀ ∈ lagAt v C := fun y =>
    ⟨fun t ht => by rw [← Matrix.smul_mul, (hζ y).1 t ht, Matrix.zero_mul], ζ y, rfl⟩
  have hiso : ∀ y y', (j y).1 ⬝ᵥ (j y').2 = (j y').1 ⬝ᵥ (j y).2 := by
    intro y y'
    have h0 := GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ G.V'.J G.W v C hC (-1) _ _ (hlag y) (hlag y')
    rw [G.M'.co.form] at h0
    have h1 := congrArg (evFin F v) h0
    rw [← sub_eq_zero, ← (hζ y).2, ← (hζ y').2]
    simpa [locCo, dotProduct, map_sum, map_mul, map_sub] using h1

  have hHeis : ∀ φ₂ ∈ SB (Fin a' × Fin (a + a') → Fv F v), HeisInv G.M' B.ψ v C (Λ ∘ₗ boxL φ₂) := by
    rintro φ₂ hφ₂ u ⟨hu, z, hz⟩ φ hφ φ₁ hφ₁ hA
    obtain ⟨y, hy⟩ := hζs (liftV v (1 : Fv F v) • z) (fun t ht => by
      rw [smul_smul, ← smul_eq_mul, at_liftV v _ t ht, zero_smul])
    have hu' : u = ζ y * Cᵀ := by rw [hy, Matrix.smul_mul, ← hz, smul_of_at hu]
    have hA' := GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v u hu φ
    have e : φ₁ = _ := GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => (hA r hr).symm.trans (hA' r hr)
    show Λ (boxFun φ₁ φ₂) = Λ (boxFun φ φ₂)
    rw [hΛ _ (box_mem_SB hφ₁ hφ₂), hΛ _ (box_mem_SB hφ hφ₂), e, hu', (hζ y).2]
    exact GlobalTheory.T.isotropicIntegral_invariant_heisenberg_first_vars F v _ _ μ hμ N ν hν j hiso y φ φ₂
  obtain ⟨φt, hφt, hline⟩ := GlobalTheory.T.heisenberg_invariant_form_vanishes_lagrangian_test F E σ a' (a + a') G.V' G.W G.M' B.ψ v hunr m C hC
  have hlt : l φt ≠ 0 := fun h => by
    obtain ⟨f, hf, hne⟩ := hne; exact hne (hline l hl h f hf)
  have hprop : ∀ φ₂ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      Λ (boxFun φ φ₂) = Λ (boxFun φt φ₂) / l φt * l φ := by
    intro φ₂ hφ₂ φ hφ
    have hl' : HeisInv G.M' B.ψ v C (Λ ∘ₗ boxL φ₂ - (Λ (boxFun φt φ₂) / l φt) • l) := by
      intro u hu f hf f₁ hf₁ hA'
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hHeis φ₂ hφ₂ u hu f hf f₁ hf₁ hA', hl u hu f hf f₁ hf₁ hA']
    have h0 : (Λ ∘ₗ boxL φ₂ - (Λ (boxFun φt φ₂) / l φt) • l) φt = 0 := by
      show Λ (boxFun φt φ₂) - (Λ (boxFun φt φ₂) / l φt) * l φt = 0
      rw [div_mul_cancel₀ _ hlt, sub_self]
    exact sub_eq_zero.1 (hline _ hl' h0 φ hφ)
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))) v

  have hdiag : ∀ k ∈ UAt σ G.V' (evFin F v), ∀ kd : UG (cA σ) (dbl (incM F G.V'.J)),
      (kd.1.1 : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) = Matrix.fromBlocks (mat k) 0 0 1 →
      Scales v Λ (omd kd) (c k) := by
    intro k hk kd hkd
    have hAt : At (evFin F v) ((kd.1.1 : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) := by
      intro u hu
      have hk1 : u • (mat k - 1) = 0 := hk u hu
      have e : Matrix.fromBlocks (mat k) 0 0 (1 : Matrix (Fin a') (Fin a') (AE F E)) - 1 =
          Matrix.fromBlocks (mat k - 1) 0 0 0 := by
        rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
        simp [sub_eq_add_neg]
      rw [hkd, e, Matrix.fromBlocks_smul]
      simp [hk1]
    refine scales_of_box _ hψc hψ1 Λ (omd kd) (c k) (GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v kd hAt) R hR0 hR ?_
    intro φ₁ h₁ φ₂ h₂ Φ₁ hA
    obtain ⟨S, hS⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hT v k hk
    rw [GlobalTheory.T.localProduct_acts_of_adelicProduct_acts_first F v _ _ (om' (k, 1)) (omd kd) (fun Φ₁ h₁ Φ₂ h₂ => hres k kd hkd Φ₁ h₁ Φ₂ h₂) φ₁ h₁ φ₂ h₂ _ Φ₁ (hS φ₁ h₁).2 hA,
      hprop φ₂ h₂ _ (hS φ₁ h₁).1, hprop φ₂ h₂ φ₁ h₁, hc k hk φ₁ h₁ _ (hS φ₁ h₁).1 (hS φ₁ h₁).2]
    ring

  have hpar : ∀ (p : UG (cA σ) (dbl (incM F G.V'.J))) (t : GL (Fin a') (AE F E)),
      At (evFin F v) ((p.1.1 : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) →
      (p.1.1 : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) * diagCols (Fin a') = diagCols (Fin a') * t.val →
      Scales v Λ (omd p) 1 := by
    intro p t hp hpt Φ hΦ
    obtain ⟨Φ₁, hΦ₁, hA⟩ := GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v p hp Φ hΦ
    refine ⟨Φ₁, hΦ₁, hA, ?_⟩
    obtain ⟨hdt, hnt, s, hs, hns⟩ := GlobalTheory.T.siegelParabolic_leviInverse_quotient_det_norm F E σ hT.base.cm a' G.V'.J hJ.ne_zero v p t hp hpt
    obtain ⟨T, hTζ, hTd⟩ := hT' s
    have hpt' := GlobalTheory.T.doubledWeilOperator_diagonalIntegral_heisenberg_point F E σ a' (a + a') G.V' G.W G.M' B.ψ hT.base.std.1 v m C hC d' hd' dd hdd omd hspl.toIsSplitting
      L hinv r₀ hr₀ c₀ hc₀ μ hLφ p _ (hsieg L hL hinv p t hpt) Φ hΦ Φ₁ hΦ₁ hA
    have hχ : (X.α / X.β) (Matrix.GeneralLinearGroup.det t) = 1 := by
      rw [MonoidHom.div_apply, GlobalTheory.InertChars.beta_eq_alpha_of_inert F E σ B a a' G X om om' hT v w hin hv
        (Matrix.GeneralLinearGroup.det t) hdt, div_self']
    set u : (AF F)ˣ := Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t) with hu
    have hmod : (((adeleClass F).modu u : NNReal) : ℝ) =
        GlobalTheory.SplitWeil.nabs (Fv F v) (Units.map (evFin F v : AF F →* Fv F v) u) := GlobalTheory.T.distribHaarChar_supportedIdele_eq_localAbsValue F v u hnt
    have hdT : Matrix.GeneralLinearGroup.det T = (Units.map (evFin F v : AF F →* Fv F v) u) ^ m := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hTd, ← GlobalTheory.T.finitePlaceComponent_adeleNorm_eq_localNorm, hns, Units.val_pow_eq_pow_val]
      rfl
    have hpow : ∀ (x : (Fv F v)ˣ) (k : ℕ), GlobalTheory.SplitWeil.nabs (Fv F v) (x ^ k) = GlobalTheory.SplitWeil.nabs (Fv F v) x ^ k := by
      intro x k
      induction k with
      | zero => rw [pow_zero, pow_zero, GlobalTheory.SplitWeil.nabs_one]
      | succ k ih => rw [pow_succ, pow_succ, GlobalTheory.SplitWeil.nabs_mul, ih]
    have hexp : ((Fintype.card (Fin (a + a')) : ℝ) / 2) = (m : ℝ) := by
      rw [Fintype.card_fin, hdm]; push_cast; ring
    rw [hχ, hmod, hexp, Real.rpow_natCast, ← hpow, ← hdT, Circle.coe_one, one_mul] at hpt'
    rw [hΛ _ hΦ₁, hΛ _ hΦ, one_mul, lagInt, lagInt, ← GlobalTheory.T.normalizedAbsDet_mul_integral_comp_mulVec_finitePlace F v N ν hν T (fun y => diagW (psiAt B.ψ v) μ Φ (j y)),
      ← integral_const_mul]
    refine congrArg _ (funext fun y => ?_)
    rw [← (hζ y).2, hpt' _ (hζ y).1, ← hs, ← hTζ, (hζ _).2]

  obtain ⟨k, hk, α, β, hα, hβ, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_unitaryScalar_inertPlace_invertible_shifts F E σ B hT.base v w hin a' G.V'.J g
  obtain ⟨gd, hgd⟩ := GlobalTheory.unitary_diag_one_mem_dbl (AF F) (AE F E) (cA σ) (Fin a') (incM F G.V'.J) g
  obtain ⟨kd, hkd⟩ := GlobalTheory.unitary_diag_one_mem_dbl (AF F) (AE F E) (cA σ) (Fin a') (incM F G.V'.J) k
  have hJA : IsUnit (incM F G.V'.J).det := by
    rw [incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hJ.map _
  have hee : liftV v (1 : Fv F v) * liftV v (1 : Fv F v) = liftV v (1 : Fv F v) := smul_of_at (at_liftV v 1)
  obtain ⟨p₁, p₂, t₁, t₂, hp₁, hp₂, ht₁, ht₂, hdec⟩ := GlobalTheory.T.idempotent_block_unipotent_identity (AF F) (AE F E) (cA σ) (Fin a') (incM F G.V'.J) hJA _ hee g k
    (one_sub_smul_of_at hg) (one_sub_smul_of_at hk) α β (smul_of_at hα) (smul_of_at hβ) e1 e2 e3 e4 gd kd hgd hkd
  have hkk : mat k * mat k⁻¹ = 1 := Units.mul_inv k.1
  have hki : k⁻¹ ∈ UAt σ G.V' (evFin F v) := fun u hu => by
    have e : mat k⁻¹ - 1 = -((mat k - 1) * mat k⁻¹) := by rw [Matrix.sub_mul, hkk, Matrix.one_mul, neg_sub]
    rw [e, smul_neg, ← Matrix.smul_mul, hk u hu, Matrix.zero_mul, neg_zero]
  have hkdi : ((kd⁻¹).1.1 : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) = Matrix.fromBlocks (mat k⁻¹) 0 0 1 := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hkd, Matrix.fromBlocks_multiply]
    have : (k.1.1 : Matrix (Fin a') (Fin a') (AE F E)) * mat k⁻¹ = 1 := hkk
    simp [this, Matrix.fromBlocks_one]
  have s1 := hdiag k hk kd hkd
  have s2 := hdiag k⁻¹ hki kd⁻¹ hkdi
  have q1 := hpar p₁ t₁ (at_of_one_sub_smul hp₁) ht₁
  have q2 := hpar p₂ t₂ (at_of_one_sub_smul hp₂) ht₂
  have hb := box_mem_SB hφ₀ hφ₀
  have f1 : c k * c k⁻¹ = 1 := by
    have h := s1.mul s2 (hspl.pres _)
    rw [← map_mul, mul_inv_cancel, map_one] at h
    exact h.unique (scales_one v Λ) hb hΛ0
  have h := ((s1.mul q1 (hspl.pres _)).mul s2 (hspl.pres _)).mul q2 (hspl.pres _)
  rw [← map_mul, ← map_mul, ← map_mul, ← hdec, mul_one, mul_one, f1] at h
  exact (hdiag g hg gd hgd).unique h hb hΛ0

end GlobalTheory.InertLagChar
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_place_transforming_character_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (AE F E)), GlobalTheory.InertVacLag.IsLagrAt σ G.W v C →
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    (∃ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), l φ ≠ 0) →
    ∀ c : UA σ G.V'.J → ℂ, (∀ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) φ φ₁ → l φ₁ = c g * l φ) →
    ∀ g ∈ UAt σ G.V' (evFin F v), c g = 1 := by
  atlas_forward_decl GlobalTheory.InertLagChar.char_eq_one
end
