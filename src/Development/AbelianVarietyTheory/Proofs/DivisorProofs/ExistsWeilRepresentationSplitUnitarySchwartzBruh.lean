import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfBigCellGenericRelations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierIntertwinesSiegelLeviOperator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformTwiceEqPosSmulReflect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformMemSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateInCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualBicharacterPairingOfSymmBilinForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitarySiegelParabolicBlockRelations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InCellIffDetNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixColumnPairingAlgebraicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralHermitianQuadraticCharacter

section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_of_bigCell_generic_relations : ∀ (G H : Type) [Group G] [Group H] (P : Subgroup G) (w : G) (ρ : P →* H) (W : H), (∀ p q : P, w * p = q * w → W * ρ p = ρ q * W) → (∀ p : P, (∃ p₁ p₂ : P, w * p * w = p₁ * w * p₂) → ∃ p₁ p₂ : P, w * p * w = p₁ * w * p₂ ∧ W * ρ p * W = ρ p₁ * W * ρ p₂) → (∀ s : Finset G, ∃ u : G, ∀ g ∈ s, ∃ p₁ p₂ : P, g * u = p₁ * w * p₂) → ∃ Φ : G →* H, (∀ p : P, Φ p = ρ p) ∧ Φ w = W := by
  first | exact @GlobalTheory.bigCell_hom | exact GlobalTheory.bigCell_hom | (intros; apply GlobalTheory.bigCell_hom <;> assumption)
end

section
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem GlobalTheory.KSp.parFun_sieg_mul : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)), (∀ φ : Matrix α ν E → ℂ, parFun c ψ χ Q (mat c (1 : UG c (stdJ ν E))) φ = φ) ∧ ∀ p ∈ sieg c ν, ∀ q ∈ sieg c ν, ∀ φ : Matrix α ν E → ℂ, parFun c ψ χ Q (mat c (p * q)) φ = parFun c ψ χ Q (mat c p) (parFun c ψ χ Q (mat c q) φ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψ0 χ hχ hres
  obtain ⟨β, hβ, hsymm, -, hadj, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  obtain ⟨hsc1, hscmul, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
  refine ⟨?_, ?_⟩
  · intro φ
    funext x
    have h1 : mat c (1 : UG c (stdJ ν E)) = 1 := rfl
    have h11 : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₁ = 1 := by
      ext i j; simp [toBlocks₁₁, one_apply]
    have h12 : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₂ = 0 := by
      ext i j; simp [toBlocks₁₂, one_apply]
    have hp0 : pr c Q x 0 = 0 := by rw [← hβ]; simp
    simp only [parFun, h1, h11, h12, det_one, hsc1, Matrix.mul_one, Matrix.mul_zero, hp0, mul_zero,
      AddChar.map_zero_eq_one, one_mul]
  · intro p hp q hq φ
    funext x
    have hmul : mat c (p * q) = mat c p * mat c q := rfl
    obtain ⟨hq1, -, -⟩ := GlobalTheory.T.splitUnitarySiegelParabolic_block_relations F E c δ hE ν q hq
    have hP : mat c p = fromBlocks (mat c p).toBlocks₁₁ (mat c p).toBlocks₁₂ 0 (mat c p).toBlocks₂₂ := by
      rw [← (mem_sieg c).mp hp]; exact (fromBlocks_toBlocks _).symm
    have hQ' : mat c q = fromBlocks (mat c q).toBlocks₁₁ (mat c q).toBlocks₁₂ 0 (mat c q).toBlocks₂₂ := by
      rw [← (mem_sieg c).mp hq]; exact (fromBlocks_toBlocks _).symm
    set A := (mat c p).toBlocks₁₁
    set B := (mat c p).toBlocks₁₂
    set A' := (mat c q).toBlocks₁₁
    set B' := (mat c q).toBlocks₁₂
    set D' := (mat c q).toBlocks₂₂
    have e11 : (mat c (p * q)).toBlocks₁₁ = A * A' := by
      rw [hmul, hP, hQ', fromBlocks_multiply]; simp
    have e12 : (mat c (p * q)).toBlocks₁₂ = A * B' + B * D' := by
      rw [hmul, hP, hQ', fromBlocks_multiply]; simp
    have hcc : ∀ M : Matrix ν ν E, (M.map c).map c = M := fun M => by ext; simp [hE.invol]
    have hDA : D' * (A'.map c)ᵀ = 1 := by
      have h := congrArg (fun M : Matrix ν ν E => (M.map c)ᵀ) hq1
      have hm : ∀ M N : Matrix ν ν E, (M * N).map c = M.map c * N.map c := fun M N => by
        ext i j; simp [Matrix.mul_apply, map_sum, map_mul]
      have h1c : ((1 : Matrix ν ν E).map c)ᵀ = 1 := by
        rw [Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
      simp only [hm, Matrix.transpose_map, hcc, transpose_mul, transpose_transpose, h1c] at h
      exact h
    have hadd : ∀ u v w : Matrix α ν E, pr c Q u (v + w) = pr c Q u v + pr c Q u w := by
      intro u v w; rw [← hβ, ← hβ, ← hβ, map_add]
    have hkey : pr c Q (x * A * A') (x * B * D') = pr c Q (x * A) (x * B) := by
      rw [← hβ, ← hβ, hadj, Matrix.mul_assoc (x * B), hDA, Matrix.mul_one]
    simp only [parFun, e11, e12, det_mul, hscmul, Matrix.mul_add, ← Matrix.mul_assoc, hadd, hkey, mul_add,
      AddChar.map_add_eq_mul]
    ring
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parFun_sieg_mul' : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)), (∀ φ : Matrix α ν E → ℂ, parFun c ψ χ Q (mat c (1 : UG c (stdJ ν E))) φ = φ) ∧ ∀ p ∈ sieg c ν, ∀ q ∈ sieg c ν, ∀ φ : Matrix α ν E → ℂ, parFun c ψ χ Q (mat c (p * q)) φ = parFun c ψ χ Q (mat c p) (parFun c ψ χ Q (mat c q) φ) := by
  atlas_forward_decl GlobalTheory.KSp.parFun_sieg_mul
end

section
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp.WeilFormula

theorem setIntegral_addSubgroup_add_right {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddLeftInvariant] (L : AddSubgroup V) (hLo : IsOpen (L : Set V)) (g : V → ℂ)
    {t : V} (ht : t ∈ L) :
    ∫ z in (L : Set V), g (z + t) ∂μ = ∫ z in (L : Set V), g z ∂μ := by
  simp_rw [add_comm _ t]
  rw [← integral_indicator hLo.measurableSet, ← integral_indicator hLo.measurableSet,
    ← integral_add_left_eq_self (μ := μ) ((L : Set V).indicator g) t]
  congr 1
  funext z
  by_cases hz : z ∈ L
  · rw [Set.indicator_of_mem (show z ∈ (L : Set V) from hz),
      Set.indicator_of_mem (show t + z ∈ (L : Set V) from L.add_mem ht hz)]
  · have hz' : t + z ∉ L := fun h => hz ((L.add_mem_cancel_left ht).1 h)
    rw [Set.indicator_of_notMem (show z ∉ (L : Set V) from hz),
      Set.indicator_of_notMem (show t + z ∉ (L : Set V) from hz')]

theorem weil_formula : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e →
    ∀ (f g : X → ℂ) (s : X → X) (γ : ℂ), Continuous f → Continuous s →
    (∀ y u, f y * e y u = g u * f (y + s u)) → HasGauss μ f γ → ∀ φ ∈ SB X, ∀ x,
    four μ e (fun y => f y * four μ e φ y) x = γ * ∫ z, g (x + z) * φ z ∂μ := by
  intro X _ _ _ _ hG μ _ e he f g s γ hf hs hfg hga φ hφ x
  haveI := hG.grp; haveI := hG.t2; haveI := hG.lc; haveI := hG.sc
  have hφ4 : four μ e φ ∈ SB X := GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat X hG μ e he φ hφ
  have hK1 : IsCompact (tsupport (four μ e φ)) := hφ4.2
  have hφc : IsCompact (tsupport φ) := hφ.2
  have hK2 : IsCompact (s '' ((fun z => x + z) '' tsupport φ)) :=
    (hφc.image (continuous_const.add continuous_id)).image hs
  obtain ⟨L, hLc, hLo, hKL, hLγ⟩ := hga _ (hK1.union hK2)
  have hLm : MeasurableSet (L : Set X) := hLo.measurableSet
  have he_cont : Continuous (fun p : X × X => e p.1 p.2) := he.lc.continuous
  have hφcont : Continuous φ := hφ.1.continuous
  have h0 : ∀ y, y ∉ (L : Set X) → e x y * (f y * four μ e φ y) = 0 := by
    intro y hy
    have : four μ e φ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hKL (Or.inl h)))
    simp [this]
  have h1 : four μ e (fun y => f y * four μ e φ y) x
      = ∫ y in (L : Set X), ∫ z, e x y * f y * (e y z * φ z) ∂μ ∂μ := by
    calc four μ e (fun y => f y * four μ e φ y) x = ∫ y, e x y * (f y * four μ e φ y) ∂μ := rfl
      _ = ∫ y in (L : Set X), e x y * (f y * four μ e φ y) ∂μ :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero h0).symm
      _ = _ := by
          congr 1; funext y
          simp only [four]
          rw [← mul_assoc, ← integral_const_mul]
  have hint : Integrable (Function.uncurry fun y z => e x y * f y * (e y z * φ z))
      ((μ.restrict (L : Set X)).prod μ) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    have hc : Continuous (Function.uncurry fun y z => e x y * f y * (e y z * φ z)) := by
      have h1' : Continuous fun p : X × X => e x p.1 := he_cont.comp (continuous_const.prodMk continuous_fst)
      exact (h1'.mul (hf.comp continuous_fst)).mul (he_cont.mul (hφcont.comp continuous_snd))
    have hon : IntegrableOn (Function.uncurry fun y z => e x y * f y * (e y z * φ z))
        ((L : Set X) ×ˢ tsupport φ) (μ.prod μ) := hc.continuousOn.integrableOn_compact (hLc.prod hφc)
    refine hon.of_forall_sdiff_eq_zero (hLm.prod MeasurableSet.univ) ?_
    rintro ⟨y, z⟩ ⟨⟨hy, -⟩, hn⟩
    have hz : z ∉ tsupport φ := fun h => hn ⟨hy, h⟩
    simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hz]
  have h3 : ∀ z, ∫ y in (L : Set X), e x y * f y * (e y z * φ z) ∂μ = γ * (g (x + z) * φ z) := by
    intro z
    by_cases hz : φ z = 0
    · simp [hz]
    · have hzt : z ∈ tsupport φ := subset_tsupport _ hz
      have hsL : s (x + z) ∈ L := hKL (Or.inr ⟨x + z, ⟨z, hzt, rfl⟩, rfl⟩)
      have hpt : ∀ y, e x y * f y * (e y z * φ z) = φ z * g (x + z) * f (y + s (x + z)) := by
        intro y
        have hexy : e x y * e y z = e y (x + z) := by
          rw [he.symm y (x + z), he.add, he.symm z y]
        rw [mul_assoc (φ z), ← hfg y (x + z), ← hexy]; ring
      simp_rw [hpt]
      rw [integral_const_mul, setIntegral_addSubgroup_add_right μ L hLo f hsL, hLγ]; ring
  rw [h1, integral_integral_swap hint]
  simp_rw [h3]
  rw [integral_const_mul]

end GlobalTheory.KSp.WeilFormula
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_formula_fourier_quadratic_character : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ (f g : X → ℂ) (s : X → X) (γ : ℂ), Continuous f → Continuous s → (∀ y u, f y * e y u = g u * f (y + s u)) → HasGauss μ f γ → ∀ φ ∈ SB X, ∀ x, four μ e (fun y => f y * four μ e φ y) x = γ * ∫ z, g (x + z) * φ z ∂μ := by
  atlas_forward_decl GlobalTheory.KSp.WeilFormula.weil_formula
end

section
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem braid_relation : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (b : Matrix ν ν E) (γ : ℂ), (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) γ → ∀ φ ∈ SB (Matrix α ν E), sc F χ (Fintype.card α) (-b⁻¹).det • fou c ψ Q μ (parFun c ψ χ Q (fromBlocks 1 b 0 1) (fou c ψ Q μ φ)) = γ • parFun c ψ χ Q (fromBlocks (-b⁻¹) 1 0 (-b)) (fou c ψ Q μ (parFun c ψ χ Q (fromBlocks 1 (-b⁻¹) 0 1) φ)) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hn h1 χ _ hχ _ _ μ _ b γ hb hd hG φ hφ
  obtain ⟨hfd, hring, -, -, -, -, -, hM⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨hmod, hgood⟩ := hM α ν
  obtain ⟨β, hβ, hs, hnd, hadj, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  have hsc := (GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hχ).1
  have hP := GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm F (Matrix α ν E) ψ hψ hn h1 β hs hnd
  have hu : IsUnit b.det := isUnit_iff_ne_zero.mpr hd
  have hi : b⁻¹ * b = 1 := Matrix.nonsing_inv_mul b hu
  have hi' : b * b⁻¹ = 1 := Matrix.mul_nonsing_inv b hu
  have hbb : ∀ x y : Matrix α ν E, β (x * b) y = β x (y * b) := fun x y => by rw [hadj, hb]
  have hbi : ∀ x y : Matrix α ν E, β (x * b⁻¹) y = β x (y * b⁻¹) := fun x y => by
    have := hbb (x * b⁻¹) (y * b⁻¹)
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hi, Matrix.mul_one, Matrix.mul_one] at this
    exact this.symm
  have hpr : (pr c Q : Matrix α ν E → Matrix α ν E → F) = fun x y => β x y := by
    funext x y; exact (hβ x y).symm
  have hf : Continuous fun y : Matrix α ν E => ψ (2⁻¹ * β y (y * b)) := by
    have h2 : Continuous fun y : Matrix α ν E => (y, y * ((2⁻¹ : F) • b)) :=
      continuous_id.prodMk (continuous_id.matrix_mul continuous_const)
    have := hP.lc.continuous.comp h2
    refine this.congr fun y => ?_
    simp [Matrix.mul_smul]
  have hW := GlobalTheory.T.weil_formula_fourier_quadratic_character (Matrix α ν E) hgood μ _ hP (fun y => ψ (2⁻¹ * β y (y * b)))
    (fun u => ψ (-(2⁻¹ * β (u * b⁻¹) u))) (fun u => u * b⁻¹) γ hf
    (continuous_id.matrix_mul continuous_const) (fun y u => by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      have h3 : β (u * b⁻¹) (y * b) = β y u := by
        rw [← hbb, Matrix.mul_assoc, hi, Matrix.mul_one, hs]
      rw [Matrix.add_mul, Matrix.mul_assoc u, hi, Matrix.mul_one]
      simp only [map_add, LinearMap.add_apply, h3]
      ring) (by simpa only [hpr] using hG) φ hφ
  funext x
  have hL : parFun c ψ χ Q (fromBlocks 1 b 0 1) (fou c ψ Q μ φ) =
      fun y => ψ (2⁻¹ * β y (y * b)) * four μ (fun x y => ψ (β x y)) φ y := by
    funext y
    simp [parFun, fou, hsc, hpr]
  rw [hL]
  simp only [Pi.smul_apply, smul_eq_mul, fou, hpr]
  rw [hW x]
  simp only [parFun, four, hpr, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, det_one, hsc, Matrix.mul_one, one_mul]
  rw [mul_left_comm, ← integral_const_mul (ψ _)]
  congr 3
  funext z
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  have h4 : β (z * b⁻¹) x = β (x * b⁻¹) z := by rw [hbi, hs]
  simp only [Matrix.add_mul, Matrix.mul_neg, map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply, h4, ← hbi z z]
  ring

end GlobalTheory.KSp
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_hermitianMultiplier_braid_relation : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (b : Matrix ν ν E) (γ : ℂ), (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) γ → ∀ φ ∈ SB (Matrix α ν E), sc F χ (Fintype.card α) (-b⁻¹).det • fou c ψ Q μ (parFun c ψ χ Q (fromBlocks 1 b 0 1) (fou c ψ Q μ φ)) = γ • parFun c ψ χ Q (fromBlocks (-b⁻¹) 1 0 (-b)) (fou c ψ Q μ (parFun c ψ χ Q (fromBlocks 1 (-b⁻¹) 0 1) φ)) := by
  atlas_forward_decl GlobalTheory.KSp.braid_relation
end

section
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.WeylCellRel

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {ν : Type} [Fintype ν] [DecidableEq ν]

theorem mat_mul (p q : UG c (stdJ ν E)) : mat c (p * q) = mat c p * mat c q := rfl

theorem mat_weyl_inv : mat c (weyl c ν)⁻¹ = -stdJ ν E := rfl

theorem mat_unip_inv (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) : mat c (unip c b hb)⁻¹ = fromBlocks 1 (-b) 0 1 := rfl

theorem mat_weyl : mat c (weyl c ν) = fromBlocks 0 1 (-1) 0 := rfl

theorem mat_levi (hc : ∀ z, c (c z) = z) (a : GL ν E) :
    mat c (levi c hc a) = fromBlocks (a : Matrix ν ν E) 0 0 (((a⁻¹ : GL ν E) : Matrix ν ν E).map c)ᵀ := rfl

theorem mat_unip (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) : mat c (unip c b hb) = fromBlocks 1 b 0 1 := rfl

theorem splitUnitaryElementMatrix_bigCell_product (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) (hb0 : b.det ≠ 0) (hb' : ((-b⁻¹).map c)ᵀ = -b⁻¹) :
    mat c (weyl c ν * unip c b hb * weyl c ν * (unip c (-b⁻¹) hb')⁻¹ * (weyl c ν)⁻¹) =
      fromBlocks (-b⁻¹) 1 0 (-b) := by
  have h1 : b * b⁻¹ = 1 := mul_nonsing_inv b (isUnit_iff_ne_zero.mpr hb0)
  rw [mat_mul, mat_mul, mat_mul, mat_mul, mat_weyl_inv, mat_unip_inv, mat_unip, mat_weyl]
  simp only [stdJ, fromBlocks_multiply, fromBlocks_neg, h1]
  simp [h1]

theorem conj_levi_mem (hc : ∀ z, c (c z) = z) (a : GL ν E) :
    weyl c ν * levi c hc a * (weyl c ν)⁻¹ ∈ sieg c ν := by
  rw [mem_sieg, mat_mul, mat_mul, mat_weyl_inv, mat_weyl, mat_levi]
  simp [stdJ, fromBlocks_multiply, fromBlocks_neg]

theorem herm_neg_inv (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) (hb0 : b.det ≠ 0) : ((-b⁻¹).map c)ᵀ = -b⁻¹ := by
  have h1 : ((b⁻¹).map c)ᵀ * b = 1 := by
    have h3 : ((b⁻¹).map c)ᵀ * (b.map c)ᵀ = 1 := by
      rw [← transpose_mul, ← Matrix.map_mul (f := c), mul_nonsing_inv b (isUnit_iff_ne_zero.mpr hb0),
        Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
    rwa [hb] at h3
  have h2 : ((b⁻¹).map c)ᵀ = b⁻¹ := (Matrix.inv_eq_left_inv h1).symm
  rw [Matrix.map_neg _ (map_neg c), transpose_neg, h2]

theorem lower_left (hc : ∀ z, c (c z) = z) (a : GL ν E) (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) :
    (mat c (weyl c ν * (levi c hc a * unip c b hb) * weyl c ν)).toBlocks₂₁ = (a : Matrix ν ν E) * b := by
  rw [mat_mul, mat_mul, mat_mul, mat_weyl, mat_levi, mat_unip]
  simp [fromBlocks_multiply]

end GlobalTheory.KSp.WeylCellRel

theorem GlobalTheory.KSp.WeylCellRel.gauss_const_ne_zero : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (γ₀ : ℂ), (∀ b : Matrix ν ν E, (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) (γ₀ * sc F χ (Fintype.card α) b.det⁻¹)) → γ₀ ≠ 0 := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres _ _ μ _ γ₀ hγ hγ0
  obtain ⟨hfd, -, -, -, -, -, -, hmat⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨hmt, hgood⟩ := hmat α ν
  haveI : FiniteDimensional F (Matrix α ν E) := inferInstance
  obtain ⟨β, hβ, hsymm, hnd, -, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  have hpair := GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm F (Matrix α ν E) ψ hψ hψ1 hψne β hsymm hnd
  have hfou : ∀ f, fou c ψ Q μ f = four μ (fun x y => ψ (β x y)) f := by
    intro f
    have hfe : (fun x y => ψ (β x y)) = (fun x y => ψ (pr c Q x y)) := by funext x y; rw [hβ]
    rw [hfe]; rfl
  obtain ⟨C, hC, hinv⟩ := GlobalTheory.T.bicharacterFourierTransform_twice_eq_pos_smul_reflect (Matrix α ν E) hgood μ _ hpair
  have inj : ∀ g ∈ SB (Matrix α ν E), fou c ψ Q μ g = 0 → g = 0 := by
    intro g hg h0
    funext x
    have h1 := hinv g hg (-x)
    rw [← hfou g, h0, neg_neg] at h1
    have h2 : four μ (fun x y => ψ (β x y)) (0 : Matrix α ν E → ℂ) (-x) = 0 := by simp [four]
    rw [h2] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (by exact_mod_cast hC.ne')
  haveI := hgood.grp
  haveI := hgood.t2
  obtain ⟨L, hLc, hLo, -⟩ := hgood.small Set.univ Filter.univ_mem
  have hLcl : IsClopen (L : Set (Matrix α ν E)) :=
    ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  set φ : Matrix α ν E → ℂ := (L : Set (Matrix α ν E)).indicator 1 with hφd
  have hφ : φ ∈ SB (Matrix α ν E) := by
    refine ⟨?_, HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _⟩
    have := (LocallyConstant.indicator (1 : LocallyConstant (Matrix α ν E) ℂ) hLcl).isLocallyConstant
    convert this using 1
    funext y
    exact (LocallyConstant.indicator_apply (1 : LocallyConstant (Matrix α ν E) ℂ) hLcl y).symm
  have hφ0 : φ 0 = 1 := by simp [hφd, Set.indicator_of_mem (zero_mem L)]
  have hfφ : fou c ψ Q μ φ ∈ SB (Matrix α ν E) := by
    rw [hfou]; exact GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat (Matrix α ν E) hgood μ _ hpair φ hφ
  have h1 : ((1 : Matrix ν ν E).map c)ᵀ = 1 := by
    rw [Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
  have hu : unip c 1 h1 ∈ sieg c ν := by rw [mem_sieg, WeylCellRel.mat_unip]; simp
  have hg := GlobalTheory.T.siegelParabolic_preserves_schwartzBruhat F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres (unip c 1 h1) hu _ hfφ
  obtain ⟨sc1, scmul, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
  have sc_ne : ∀ z : E, z ≠ 0 → sc F χ (Fintype.card α) z ≠ 0 := fun z hz h => by
    have h' := scmul z z⁻¹
    rw [mul_inv_cancel₀ hz, sc1, h, zero_mul] at h'
    exact one_ne_zero h'
  have br := GlobalTheory.T.fourier_hermitianMultiplier_braid_relation F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ 1 _ h1 (by simp)
    (hγ 1 h1 (by simp)) φ hφ
  rw [hγ0, zero_mul, zero_smul] at br
  have hs : sc F χ (Fintype.card α) (-(1 : Matrix ν ν E)⁻¹).det ≠ 0 := sc_ne _ (by simp [det_neg])
  have hX := (smul_eq_zero.mp br).resolve_left hs
  have hpar0 := inj _ hg hX
  apply one_ne_zero (α := ℂ)
  rw [← hφ0]
  have hF0 : fou c ψ Q μ φ = 0 := by
    funext x
    have h2 := congrFun hpar0 x
    have hψ0 : ∀ t, ψ t ≠ 0 := by
      intro t h4; have := hψ1 t; rw [h4, norm_zero] at this; exact zero_ne_one this
    simpa [parFun, WeylCellRel.mat_unip, sc1, hψ0] using h2
  rw [inj φ hφ hF0]; rfl

theorem GlobalTheory.KSp.weyl_cell_relation : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ κ : ℂ, κ ≠ 0 ∧ ∀ p ∈ sieg c ν, InCell c (weyl c ν * p * weyl c ν) → ∃ p₁ ∈ sieg c ν, ∃ p₂ ∈ sieg c ν, weyl c ν * p * weyl c ν = p₁ * weyl c ν * p₂ ∧ ∀ φ ∈ SB (Matrix α ν E), κ • fou c ψ Q μ (parFun c ψ χ Q (mat c p) (κ • fou c ψ Q μ φ)) = parFun c ψ χ Q (mat c p₁) (κ • fou c ψ Q μ (parFun c ψ χ Q (mat c p₂) φ)) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres _ _ μ _
  obtain ⟨γ₀, hγ⟩ := GlobalTheory.T.hasGaussIntegral_hermitian_quadratic_character F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ
  have hγ0 : γ₀ ≠ 0 :=
    GlobalTheory.KSp.WeylCellRel.gauss_const_ne_zero F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ γ₀ hγ
  obtain ⟨sc1, scmul, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
  have sc_ne : ∀ z : E, z ≠ 0 → sc F χ (Fintype.card α) z ≠ 0 := fun z hz h => by
    have h' := scmul z z⁻¹
    rw [mul_inv_cancel₀ hz, sc1, h, zero_mul] at h'
    exact one_ne_zero h'
  have hs1 : sc F χ (Fintype.card α) (-1 : Matrix ν ν E).det ≠ 0 := sc_ne _ (by simp [det_neg])
  refine ⟨sc F χ (Fintype.card α) (-1 : Matrix ν ν E).det / γ₀, div_ne_zero hs1 hγ0, ?_⟩
  intro p hp hcell
  obtain ⟨-, -, a, b, hb, rfl⟩ := GlobalTheory.T.splitUnitarySiegelParabolic_block_relations F E c δ hE ν p hp
  have hb0 : b.det ≠ 0 := by
    have h := (GlobalTheory.T.inCell_iff_det_lower_left_block_ne_zero F E c δ hE ν _).mp hcell
    rw [WeylCellRel.lower_left, det_mul] at h
    exact right_ne_zero_of_mul h
  have hb' := WeylCellRel.herm_neg_inv c b hb hb0
  have hunip : ∀ (b' : Matrix ν ν E) (h' : (b'.map c)ᵀ = b'), unip c b' h' ∈ sieg c ν := by
    intro b' h'; rw [mem_sieg, WeylCellRel.mat_unip]; simp
  have hlevi : levi c hE.invol a ∈ sieg c ν := by rw [mem_sieg, WeylCellRel.mat_levi]; simp
  obtain ⟨q, hqd⟩ : ∃ q, q = weyl c ν * levi c hE.invol a * (weyl c ν)⁻¹ := ⟨_, rfl⟩
  obtain ⟨p₀, hp0d⟩ : ∃ p₀, p₀ = weyl c ν * unip c b hb * weyl c ν * (unip c (-b⁻¹) hb')⁻¹ * (weyl c ν)⁻¹ :=
    ⟨_, rfl⟩
  have hq : q ∈ sieg c ν := hqd ▸ WeylCellRel.conj_levi_mem c hE.invol a
  have hp0m : mat c p₀ = fromBlocks (-b⁻¹) 1 0 (-b) := hp0d ▸ WeylCellRel.splitUnitaryElementMatrix_bigCell_product c b hb hb0 hb'
  have hp0 : p₀ ∈ sieg c ν := by rw [mem_sieg, hp0m]; simp
  refine ⟨q * p₀, mul_mem hq hp0, unip c (-b⁻¹) hb', hunip _ _, by rw [hqd, hp0d]; group, ?_⟩
  intro φ hφ
  obtain ⟨-, pm⟩ := GlobalTheory.T.parFun_sieg_mul' F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres
  have fl := GlobalTheory.T.fourier_intertwines_siegelLeviOperator F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ (levi c hE.invol a) hlevi q hq
    (by rw [hqd]; group)
  have br := GlobalTheory.T.fourier_hermitianMultiplier_braid_relation F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres μ b _ hb hb0 (hγ b hb hb0) φ hφ
  rw [← WeylCellRel.mat_unip c b hb, ← WeylCellRel.mat_unip c (-b⁻¹) hb', ← hp0m] at br
  have pf_smul : ∀ (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E) (k : ℂ) (f : Matrix α ν E → ℂ),
      parFun c ψ χ Q g (k • f) = k • parFun c ψ χ Q g f := by
    intro g k f; funext x; simp only [parFun, Pi.smul_apply, smul_eq_mul]; ring
  have fou_smul : ∀ (k : ℂ) (f : Matrix α ν E → ℂ), fou c ψ Q μ (k • f) = k • fou c ψ Q μ f := by
    intro k f; funext x; simp only [fou, four, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]; congr 1; funext y; ring
  have e : (-b⁻¹ : Matrix ν ν E).det = (-1 : Matrix ν ν E).det * b.det⁻¹ := by
    rw [← neg_one_mul, det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
  have hκγ : sc F χ (Fintype.card α) (-1 : Matrix ν ν E).det / γ₀ * (γ₀ * sc F χ (Fintype.card α) b.det⁻¹) =
      sc F χ (Fintype.card α) (-b⁻¹).det := by
    rw [e, scmul]; field_simp
  have hs : sc F χ (Fintype.card α) (-b⁻¹).det ≠ 0 := sc_ne _ (by
    rw [e]; exact mul_ne_zero (by simp [det_neg]) (inv_ne_zero hb0))
  have hγne : γ₀ * sc F χ (Fintype.card α) b.det⁻¹ ≠ 0 := by
    intro h; rw [h, mul_zero] at hκγ; exact hs hκγ.symm
  set κ := sc F χ (Fintype.card α) (-1 : Matrix ν ν E).det / γ₀ with hκ
  have key : κ • fou c ψ Q μ (parFun c ψ χ Q (mat c (unip c b hb)) (fou c ψ Q μ φ)) =
      parFun c ψ χ Q (mat c p₀) (fou c ψ Q μ (parFun c ψ χ Q (mat c (unip c (-b⁻¹) hb')) φ)) := by
    apply smul_right_injective _ hγne
    simp only
    rw [smul_smul, mul_comm, hκγ, br]
  rw [pf_smul, fou_smul, pm _ hlevi _ (hunip _ _), fl, ← pf_smul, key, pf_smul, pm _ hq _ hp0]

end
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilRepresentation_bigCell_relation_fourier : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ κ : ℂ, κ ≠ 0 ∧ ∀ p ∈ sieg c ν, InCell c (weyl c ν * p * weyl c ν) → ∃ p₁ ∈ sieg c ν, ∃ p₂ ∈ sieg c ν, weyl c ν * p * weyl c ν = p₁ * weyl c ν * p₂ ∧ ∀ φ ∈ SB (Matrix α ν E), κ • fou c ψ Q μ (parFun c ψ χ Q (mat c p) (κ • fou c ψ Q μ φ)) = parFun c ψ χ Q (mat c p₁) (κ • fou c ψ Q μ (parFun c ψ χ Q (mat c p₂) φ)) := by
  atlas_forward_decl GlobalTheory.KSp.weyl_cell_relation
end

section
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.Exist

theorem exists_isKW : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψn hψ1 χ hχ hη _ _ μ _
  obtain ⟨hFD, -, -, -, -, -, -, hM⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI := hFD
  obtain ⟨hMT, hGood⟩ := hM α ν
  haveI := hMT
  haveI := hGood.grp
  obtain ⟨β, hβ, hβs, hβn, -, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  have hpair : IsPair (fun x y : Matrix α ν E => ψ (pr c Q x y)) := by
    have h := GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm F (Matrix α ν E) ψ hψ hψn hψ1 β hβs hβn
    simpa only [hβ] using h
  have hfm : ∀ φ ∈ SB (Matrix α ν E), fou c ψ Q μ φ ∈ SB (Matrix α ν E) := fun φ hφ =>
    GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat (Matrix α ν E) hGood μ _ hpair φ hφ
  have hpm := GlobalTheory.T.siegelParabolic_preserves_schwartzBruhat F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη
  obtain ⟨hp1, hpmul⟩ := GlobalTheory.T.parFun_sieg_mul' F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη
  obtain ⟨κ, hκ, hrel⟩ := GlobalTheory.T.exists_weilRepresentation_bigCell_relation_fourier F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη μ
  obtain ⟨C, hC, hff⟩ := GlobalTheory.T.bicharacterFourierTransform_twice_eq_pos_smul_reflect (Matrix α ν E) hGood μ _ hpair

  let parL : sieg c ν → Module.End ℂ (SB (Matrix α ν E)) := fun p =>
    { toFun := fun φ => ⟨parFun c ψ χ Q (mat c p) φ, hpm p p.2 φ φ.2⟩
      map_add' := fun φ φ' => Subtype.ext (funext fun x => by
        simp only [parFun, Submodule.coe_add, Pi.add_apply]; ring)
      map_smul' := fun z φ => Subtype.ext (funext fun x => by
        simp only [parFun, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring) }
  let ρ₀ : sieg c ν →* Module.End ℂ (SB (Matrix α ν E)) :=
    { toFun := parL
      map_one' := LinearMap.ext fun φ => Subtype.ext (hp1 φ)
      map_mul' := fun p q => LinearMap.ext fun φ => Subtype.ext (hpmul p p.2 q q.2 φ) }

  have hint : ∀ φ : Matrix α ν E → ℂ, φ ∈ SB (Matrix α ν E) → ∀ x,
      Integrable (fun y => ψ (pr c Q x y) * φ y) μ := by
    intro φ hφ x
    have hlc : IsLocallyConstant (fun y => ψ (pr c Q x y) * φ y) :=
      (hpair.lc.comp_continuous (continuous_const.prodMk continuous_id)).mul hφ.1
    exact hlc.continuous.integrable_of_hasCompactSupport hφ.2.mul_left
  have fou_smul : ∀ (k : ℂ) (f : Matrix α ν E → ℂ) x, fou c ψ Q μ (k • f) x = k * fou c ψ Q μ f x := by
    intro k f x
    simp only [fou, four, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1; funext y; ring
  let Fo : Module.End ℂ (SB (Matrix α ν E)) :=
    { toFun := fun φ => ⟨fou c ψ Q μ φ, hfm φ φ.2⟩
      map_add' := fun φ φ' => Subtype.ext (funext fun x => by
        simp only [fou, four, Submodule.coe_add, Pi.add_apply, mul_add]
        exact integral_add (hint _ φ.2 x) (hint _ φ'.2 x))
      map_smul' := fun z φ => Subtype.ext (funext fun x => by
        simp only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        exact fou_smul z _ x) }
  have hne : (κ ^ 2 * (C : ℂ)) ≠ 0 := mul_ne_zero (pow_ne_zero _ hκ) (by exact_mod_cast hC.ne')
  have key : ∀ φ : SB (Matrix α ν E),
      (((κ • Fo) ((κ • Fo) φ) : SB (Matrix α ν E)) : Matrix α ν E → ℂ) = fun x => (κ ^ 2 * (C : ℂ)) * (φ : Matrix α ν E → ℂ) (-x) := by
    intro φ
    funext x
    show κ * fou c ψ Q μ (κ • fou c ψ Q μ φ) x = _
    rw [fou_smul]
    have h := hff φ φ.2 x
    change fou c ψ Q μ (fou c ψ Q μ φ) x = _ at h
    rw [h]
    ring
  have hW : IsUnit (κ • Fo) := by
    rw [Module.End.isUnit_iff]
    constructor
    · intro a b hab
      have h2 := congrArg (fun φ => (((κ • Fo) φ : SB (Matrix α ν E)) : Matrix α ν E → ℂ)) hab
      simp only [key] at h2
      apply Subtype.ext
      funext x
      have h3 := congrFun h2 (-x)
      simp only [neg_neg] at h3
      exact mul_left_cancel₀ hne h3
    · intro φ
      have hr : (fun x => (φ : Matrix α ν E → ℂ) (-x)) ∈ SB (Matrix α ν E) :=
        ⟨φ.2.1.comp_continuous continuous_neg, φ.2.2.comp_homeomorph (Homeomorph.neg _)⟩
      refine ⟨(κ ^ 2 * (C : ℂ))⁻¹ • (κ • Fo) ⟨_, hr⟩, Subtype.ext (funext fun x => ?_)⟩
      rw [map_smul, Submodule.coe_smul, Pi.smul_apply, key]
      simp only [neg_neg, smul_eq_mul]
      exact inv_mul_cancel_left₀ hne _
  obtain ⟨Φ, hΦp, hΦw⟩ := GlobalTheory.T.exists_hom_of_bigCell_generic_relations (UG c (stdJ ν E)) (Module.End ℂ (SB (Matrix α ν E)))ˣ (sieg c ν)
    (weyl c ν) ρ₀.toHomUnits hW.unit
    (by
      intro p q hpq
      apply Units.ext
      apply LinearMap.ext
      intro φ
      apply Subtype.ext
      funext x
      have h := GlobalTheory.T.fourier_intertwines_siegelLeviOperator F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη μ p p.2 q q.2 hpq φ
      show κ * fou c ψ Q μ (parFun c ψ χ Q (mat c p) φ) x =
        parFun c ψ χ Q (mat c q) (κ • fou c ψ Q μ φ) x
      rw [h]
      simp only [parFun, Pi.smul_apply, smul_eq_mul]
      ring)
    (by
      rintro p ⟨p₁, p₂, h⟩
      obtain ⟨q₁, hq₁, q₂, hq₂, he, hop⟩ := hrel p p.2 ⟨p₁, p₁.2, p₂, p₂.2, h⟩
      refine ⟨⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩, he, ?_⟩
      apply Units.ext
      apply LinearMap.ext
      intro φ
      apply Subtype.ext
      exact hop φ φ.2)
    (by
      intro s
      obtain ⟨u, hu⟩ := GlobalTheory.T.exists_translate_inCell' F E c δ hE ν s
      refine ⟨u, fun g hg => ?_⟩
      obtain ⟨p, hp, q, hq, h⟩ := hu g hg
      exact ⟨⟨p, hp⟩, ⟨q, hq⟩, h⟩)
  refine ⟨κ, (Units.coeHom _).comp Φ, ⟨fun p hp φ => ?_, fun φ => ?_⟩⟩
  · have h := hΦp ⟨p, hp⟩
    change ((Φ ((⟨p, hp⟩ : sieg c ν) : UG c (stdJ ν E)) : Module.End ℂ (SB (Matrix α ν E))) φ :
      Matrix α ν E → ℂ) = _
    rw [h]
    rfl
  · change ((Φ (weyl c ν) : Module.End ℂ (SB (Matrix α ν E))) φ : Matrix α ν E → ℂ) = _
    rw [hΦw, IsUnit.unit_spec]
    rfl

end GlobalTheory.KSp.Exist

end
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weil_representation_split_unitary_schwartzBruhat : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω := by
  atlas_forward_decl GlobalTheory.KSp.Exist.exists_isKW
end
