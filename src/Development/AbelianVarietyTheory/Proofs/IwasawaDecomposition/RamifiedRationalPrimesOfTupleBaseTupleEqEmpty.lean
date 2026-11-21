import Mathlib
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypeDimensionAndLocalIntegralsDegreeOne
import Formalism.DoubleCosetMeasures.LatticeCoset
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsNrm
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardGLFiniteFieldEqPowMulProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharUnramifiedInverseSplitPair

section
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem.HD

private theorem lt_one_iff_le_exp_neg_one (g : WithZero (Multiplicative ℤ)) :
    g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
  induction g using WithZero.expRecOn with
  | zero => simp
  | exp a => rw [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]; omega

theorem isLocalAt_adicCompletionIntegers_uniformizer (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) :
    IsLocalAt (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) := by
  have hv : Valued.v ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L)
      = WithZero.exp (-1 : ℤ) := unif_spec P
  have hne : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ≠ 0 := Units.ne_zero _
  have mem : ∀ x : P.adicCompletion L, x ∈ OP P ↔ Valued.v x ≤ 1 := fun x =>
    HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 L) (K := L) (v := P)
  have hexp : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp (-1 : ℤ) :=
    zero_lt_iff.2 WithZero.exp_ne_zero
  refine ⟨?_, ?_⟩
  · intro h
    have h1 := (mem _).1 h
    rw [map_inv₀, hv, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  · intro x hx hnot
    have hx1 : Valued.v x ≤ 1 := (mem x).1 hx
    have hx_eq : Valued.v x = 1 := by
      by_contra hne1
      have hlt : Valued.v x < 1 := lt_of_le_of_ne hx1 hne1
      have hle := (lt_one_iff_le_exp_neg_one _).1 hlt
      refine hnot (((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L)⁻¹ * x) ?_ ?_
      · rw [mem, map_mul, map_inv₀, hv]
        exact inv_mul_le_one_of_le₀ hle hexp.le
      · rw [mul_inv_cancel_left₀ hne]
    rw [mem, map_inv₀, hx_eq, inv_one]

end GlobalTheory.Mem.HD
end

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalAt_completionIntegers_chosenUniformiser : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)), IsLocalAt (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) := by
  atlas_forward_decl GlobalTheory.Mem.HD.isLocalAt_adicCompletionIntegers_uniformizer
end

section
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.ResidueCardUnif

theorem card_kF_piP : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (h : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ∈ OP P), Nat.card (kF (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) h) = qP P := by
  intro L _ _ P h
  have ha : Valued.v ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
    unif_spec P
  have h1 : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ∈ P.adicCompletionIntegers L := h
  have e : IsLocalRing.maximalIdeal (P.adicCompletionIntegers L) = Ideal.span {⟨_, h1⟩} := by
    ext y
    rw [GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers P
      (by rw [ha]; exact WithZero.exp_ne_zero)]
    rw [ha, ← GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp]
    exact Valuation.mem_maximalIdeal_iff _ _
  have c := GlobalTheory.GaugeProdFormula.card_residue L P
  rw [IsLocalRing.ResidueField, e] at c
  exact c

end GlobalTheory.ResidueCardUnif
end

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_residueRing_completion_chosenUniformiser : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (h : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ∈ OP P), Nat.card (kF (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) h) = qP P := by
  atlas_forward_decl GlobalTheory.ResidueCardUnif.card_kF_piP
end

section
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory

theorem haar_glInt_one : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (r : ℕ), ∃ μ : Measure (GL (Fin r) (P.adicCompletion L)), μ.IsMulLeftInvariant ∧ μ ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L))) = 1 := by
  intro L _ _ P r
  have hc : IsCompact ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L))) :=
    Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.glR_compact (OP P) (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers P) r
  have ho : IsOpen ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L))) :=
    Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.glR_open (OP P) (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers P) r
  let K₀ : TopologicalSpace.PositiveCompacts (GL (Fin r) (P.adicCompletion L)) :=
    ⟨⟨_, hc⟩, by
      rw [ho.interior_eq]; exact ⟨1, (GLint (OP P) r).one_mem⟩⟩
  refine ⟨Measure.haarMeasure K₀, Measure.isMulLeftInvariant_haarMeasure K₀, ?_⟩
  exact Measure.haarMeasure_self

end GlobalTheory
end

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_GL_completion_integers_vol_one : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (r : ℕ), ∃ μ : Measure (GL (Fin r) (P.adicCompletion L)), μ.IsMulLeftInvariant ∧ μ ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L))) = 1 := by
  atlas_forward_decl GlobalTheory.haar_glInt_one
end

section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addHaar_completionIntegralMatrices_vol_one : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (n m : ℕ), letI : MeasurableSpace (P.adicCompletion L) := borel _; ∃ ν : Measure (Matrix (Fin n) (Fin m) (P.adicCompletion L)), ν.IsAddLeftInvariant ∧ SFinite ν ∧ ν (intMat (OP P) n m) = 1 := by
  first | exact @GlobalTheory.HaarMat.exists_haar_intMat | exact GlobalTheory.HaarMat.exists_haar_intMat | (intros; apply GlobalTheory.HaarMat.exists_haar_intMat <;> assumption)
end

section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_GL_finiteField_eq_pow_mul_prod : ∀ (k : Type) [Field k] [Fintype k] (r : ℕ), (Nat.card (GL (Fin r) k) : ℝ) = (Fintype.card k : ℝ) ^ (r * r) * Formalism.MainNotions.ZetaProductPairs.qE (Fintype.card k : ℝ) 1 r := by
  first | exact @GlobalTheory.Mem.card_GL_eq_pow_mul_qE | exact GlobalTheory.Mem.card_GL_eq_pow_mul_qE | (intros; apply GlobalTheory.Mem.card_GL_eq_pow_mul_qE <;> assumption)
end

section
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.Mem.SingleQ

section Gen

variable {F : Type} [Field F]

theorem unitCharExtendedByZero_det_eq_char_det (δ : Fˣ →* ℂˣ) {n : ℕ} (k : GL (Fin n) F) :
    chi0 δ (k : Matrix (Fin n) (Fin n) F).det = ((δ (GeneralLinearGroup.det k) : ℂˣ) : ℂ) := by
  have h : (k : Matrix (Fin n) (Fin n) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  have e : Units.mk0 _ h = GeneralLinearGroup.det k :=
    Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply])
  rw [chi0, dif_neg h, e]

def rowEq (r t : ℕ) : Matrix (Fin r ⊕ Fin t) (Fin r) F ≃ Matrix (Fin (r + t)) (Fin r) F :=
  Matrix.reindex finSumFinEquiv (Equiv.refl _)

omit [Field F] in
theorem rowEq_apply {r t : ℕ} (x : Matrix (Fin r ⊕ Fin t) (Fin r) F) (i : Fin (r + t)) (j : Fin r) :
    rowEq r t x i j = x (finSumFinEquiv.symm i) j := rfl

theorem rowEq_mul {r t : ℕ} (x : Matrix (Fin r ⊕ Fin t) (Fin r) F) (g : Matrix (Fin r) (Fin r) F) :
    rowEq r t (x * g) = rowEq r t x * g := by
  ext i j
  simp only [rowEq_apply, Matrix.mul_apply]

theorem phiQ_rowEq (O : Subring F) (ϖ : F) (δ : Fˣ →* ℂˣ) (r t : ℕ) (x : Matrix (Fin r ⊕ Fin t) (Fin r) F) :
    phiQ O ϖ δ r t 0 (rowEq r t x) =
      phiU O ϖ (GLint O r) (δ.comp (GeneralLinearGroup.det.comp (GLint O r).subtype))⁻¹ x := by
  have hA : bAA (d := t) (c := 0) (rowEq r t x) = Matrix.toRows₁ x := by
    ext i j; simp only [bAA, Matrix.submatrix_apply, rowEq_apply, finSumFinEquiv_symm_apply_castAdd]; rfl
  have hD : bDA (d := t) (c := 0) (rowEq r t x) = Matrix.toRows₂ x := by
    ext i j; simp only [bDA, Matrix.submatrix_apply, rowEq_apply, finSumFinEquiv_symm_apply_natAdd]; rfl
  have hB : bAD (d := t) (c := 0) (rowEq r t x) ∈ intMat O r 0 := fun _ j => j.elim0
  have hC : bDD (d := t) (c := 0) (rowEq r t x) ∈ intMat O t 0 := fun _ j => j.elim0
  unfold phiQ phiU
  by_cases h : (∃ k : GLint O r, ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = Matrix.toRows₁ x) ∧
      Matrix.toRows₂ x ∈ IIset O ϖ
  · rw [dif_pos h]
    have hc : bAA (d := t) (c := 0) (rowEq r t x) ∈ Jset (GLint O r) ∧
        bDA (d := t) (c := 0) (rowEq r t x) ∈ IIset O ϖ ∧
        bAD (d := t) (c := 0) (rowEq r t x) ∈ intMat O r 0 ∧
        bDD (d := t) (c := 0) (rowEq r t x) ∈ intMat O t 0 := by
      rw [hA, hD]
      obtain ⟨k, hk⟩ := h.1
      exact ⟨⟨k, k.2, hk⟩, h.2, hB, hC⟩
    rw [if_pos hc, hA]
    have hk := Classical.choose_spec h.1
    have e : chi0 δ (Matrix.toRows₁ x).det =
        ((δ (GeneralLinearGroup.det ((Classical.choose h.1 : GLint O r) : GL (Fin r) F)) : ℂˣ) : ℂ) := by
      rw [← unitCharExtendedByZero_det_eq_char_det, hk]
    rw [e]
    simp [Units.val_inv_eq_inv_val]
  · rw [dif_neg h, if_neg]
    rintro ⟨h1, h2, -, -⟩
    rw [hA] at h1
    rw [hD] at h2
    obtain ⟨k, hk, e⟩ := h1
    exact h ⟨⟨⟨k, hk⟩, e⟩, h2⟩

end Gen

end GlobalTheory.Mem.SingleQ

namespace GlobalTheory.Mem.SingleQ

section Triv

variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

omit [IsTopologicalRing F] in
theorem isUnrM_one (O : Subring F) (nrm : AbsoluteValue F ℝ) (r : ℕ) (χ : Fin 0 → F → ℂ) :
    IsUnrM O nrm r 0 χ (1 : GL (Fin r) F × GL (Fin 0) F →* (ℂ ≃ₗᵢ[ℂ] ℂ)) where
  smooth x := by
    convert isOpen_univ using 1
    ext m
    simp
  irred W _ := Ideal.eq_bot_or_top W
  sph := by
    haveI : Subsingleton (GL (Fin 0) F) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    refine ⟨1, by simp, fun _ _ _ _ => rfl, fun _ => 1, Measure.dirac 1, ?_, ?_, ?_, ?_⟩
    · intro b _ k _
      simp
    · exact ⟨fun g => by
        rw [show (fun x : GL (Fin 0) F => g * x) = id from funext fun _ => Subsingleton.elim _ _,
          Measure.map_id]⟩
    · exact Measure.dirac_apply_of_mem (GLint O 0).one_mem
    · intro g
      rw [setIntegral_const, Measure.real, Measure.dirac_apply_of_mem (GLint O 0).one_mem]
      simp

omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem one_mem_typeSp (O : Subring F) (ϖ : F) (nrm : AbsoluteValue F ℝ) (δ : Fˣ →* ℂˣ) (r : ℕ) :
    (fun _ => (1 : ℂ)) ∈ typeSp O ϖ nrm δ r 0 (1 : GL (Fin r) F × GL (Fin 0) F →* (ℂ ≃ₗᵢ[ℂ] ℂ)) := by
  refine ⟨fun p m₁ m₂ _ _ _ g => ?_, fun k _ g => ?_⟩
  · obtain rfl : m₂ = 1 := Subsingleton.elim _ _
    simp
  · simp [lamJ, chi0]

end Triv

end GlobalTheory.Mem.SingleQ

namespace GlobalTheory.Mem.SingleQ

section Tr

variable {F : Type} [Field F] [MeasurableSpace F]

def rowEqM (r t : ℕ) : Matrix (Fin r ⊕ Fin t) (Fin r) F ≃ᵐ Matrix (Fin (r + t)) (Fin r) F where
  toEquiv := rowEq r t
  measurable_toFun := by
    change Measurable fun (x : Fin r ⊕ Fin t → Fin r → F) (i : Fin (r + t)) => x (finSumFinEquiv.symm i)
    exact measurable_pi_lambda _ fun i => measurable_pi_apply _
  measurable_invFun := by
    change Measurable fun (x : Fin (r + t) → Fin r → F) (i : Fin r ⊕ Fin t) => x (finSumFinEquiv i)
    refine measurable_pi_lambda _ fun i => ?_
    exact measurable_pi_apply _

omit [Field F] in
theorem rowEqM_apply {r t : ℕ} (x : Matrix (Fin r ⊕ Fin t) (Fin r) F) : rowEqM r t x = rowEq r t x := rfl

variable [TopologicalSpace F] [IsTopologicalRing F]

omit [IsTopologicalRing F] in
theorem localZ_map {r t : ℕ} (μ : Measure (GL (Fin r) F)) (m : Measure (Matrix (Fin r ⊕ Fin t) (Fin r) F))
    (χ : Fˣ →* ℂˣ) (nrm : AbsoluteValue F ℝ) (Φ : Matrix (Fin (r + t)) (Fin r) F → ℂ) (c : GL (Fin r) F → ℂ) :
    localZ μ (m.map (rowEqM r t)) χ nrm Φ Φ c = localZ μ m χ nrm (Φ ∘ rowEq r t) (Φ ∘ rowEq r t) c := by
  unfold localZ
  congr 1 with g
  congr 1
  unfold weilIP
  rw [integral_map_equiv]
  congr 1 with x
  simp only [omegaS, rowEqM_apply, Function.comp_apply, rowEq_mul, Fintype.card_sum, Fintype.card_fin]

end Tr

end GlobalTheory.Mem.SingleQ

namespace GlobalTheory.Mem.SingleQ

section Loc

theorem isMaximal_span {F : Type} [Field F] {O : Subring F} {ϖ : F} (hϖ : ϖ ∈ O) (h : IsLocalAt O ϖ) :
    (Ideal.span {(⟨ϖ, hϖ⟩ : O)}).IsMaximal := by
  obtain ⟨h1, h2⟩ := h
  rw [Ideal.isMaximal_iff]
  refine ⟨fun hm => ?_, fun J x _ hx hxJ => ?_⟩
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hm
    have hc' : (c : F) * ϖ = 1 := by simpa using congrArg Subtype.val hc
    exact h1 ((eq_inv_of_mul_eq_one_left hc') ▸ c.2)
  · have hx' : ∀ o ∈ O, (x : F) ≠ ϖ * o := by
      rintro o ho he
      exact hx (Ideal.mem_span_singleton'.mpr ⟨⟨o, ho⟩, Subtype.ext (by simp [he, mul_comm])⟩)
    have hx0 : (x : F) ≠ 0 := fun h0 => hx' 0 O.zero_mem (by simp [h0])
    have hinv := h2 x x.2 hx'
    have e : (1 : O) = x * ⟨(x : F)⁻¹, hinv⟩ := Subtype.ext (by simp [hx0])
    rw [e]
    exact J.mul_mem_right _ hxJ

variable {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))

theorem isOpen_OP : IsOpen ((OP P : Subring (P.adicCompletion L)) : Set (P.adicCompletion L)) := by
  have hc : Continuous fun x : P.adicCompletion L => (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => x) :=
    continuous_pi fun _ => continuous_pi fun _ => continuous_id
  convert (GlobalTheory.HaarMat.isOpen_intMat P 1 1).preimage hc using 1
  ext x
  simp [intMat]

theorem mem_adicCompletionIntegers_iff₂ (x : P.adicCompletion L) : x ∈ OP P ↔ Valued.v x ≤ 1 := by
  first
  | exact Iff.rfl
  | exact HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

theorem piP_mem : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ∈ OP P := by
  rw [mem_adicCompletionIntegers_iff₂]
  have h := unif_spec P
  unfold IsUnifAt at h
  rw [piP, h, ← WithZero.exp_zero, WithZero.exp_le_exp]
  norm_num

theorem isCompact_GLint (r : ℕ) :
    IsCompact ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L))) := by
  have hK : IsCompact (intMat (OP P) r r ×ˢ (MulOpposite.unop ⁻¹' intMat (OP P) r r)) :=
    (GlobalTheory.HaarMat.isCompact_intMat P r r).prod
      ((MulOpposite.opHomeomorph.symm.isCompact_preimage).2 (GlobalTheory.HaarMat.isCompact_intMat P r r))
  convert Units.isClosedEmbedding_embedProduct.isCompact_preimage hK using 1
  ext g
  exact Iff.rfl

theorem isUnitAt_det {r : ℕ} {k : GL (Fin r) (P.adicCompletion L)} (hk : k ∈ GLint (OP P) r) :
    IsUnitAt P (GeneralLinearGroup.det k) := by
  obtain ⟨h1, h2⟩ := hk
  have hdet : ∀ M : Matrix (Fin r) (Fin r) (P.adicCompletion L), IsInt (OP P) M → M.det ∈ OP P := by
    intro M hM
    have e : M = (OP P).subtype.mapMatrix (Matrix.of fun i j => (⟨M i j, hM i j⟩ : OP P)) := by
      ext i j; rfl
    rw [e, ← RingHom.map_det]
    exact Subtype.property _
  have a := (mem_adicCompletionIntegers_iff₂ P _).1 (hdet _ h1)
  have b := (mem_adicCompletionIntegers_iff₂ P _).1 (hdet _ h2)
  have hmul : (k : Matrix (Fin r) (Fin r) (P.adicCompletion L)).det * ((k⁻¹ : GL (Fin r) (P.adicCompletion L)) : Matrix (Fin r) (Fin r) (P.adicCompletion L)).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  unfold IsUnitAt
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  apply le_antisymm a
  calc (1 : _) = Valued.v (k : Matrix (Fin r) (Fin r) (P.adicCompletion L)).det *
        Valued.v ((k⁻¹ : GL (Fin r) (P.adicCompletion L)) : Matrix (Fin r) (Fin r) (P.adicCompletion L)).det := by rw [← map_mul, hmul, map_one]
    _ ≤ Valued.v (k : Matrix (Fin r) (Fin r) (P.adicCompletion L)).det * 1 := by
      first
      | exact mul_le_mul_left' b _
      | exact mul_le_mul_of_nonneg_left b (zero_le _)
      | gcongr
    _ = _ := mul_one _

end Loc

end GlobalTheory.Mem.SingleQ

namespace GlobalTheory.Mem.SingleQ

section Dx

variable {F : Type} [Field F] [MeasurableSpace F]

omit [Field F] in
theorem measurable_fromRows' (r t : ℕ) :
    Measurable (fun p : Matrix (Fin r) (Fin r) F × Matrix (Fin t) (Fin r) F => Matrix.fromRows p.1 p.2) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  rcases i with i | i
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst)
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd)

def rowsH (r t : ℕ) : (Matrix (Fin r) (Fin r) F × Matrix (Fin t) (Fin r) F) →ₙ+ Matrix (Fin (r + t)) (Fin r) F where
  toFun p := rowEq r t (Matrix.fromRows p.1 p.2)
  map_add' p q := by
    ext i j
    simp only [rowEq_apply, Prod.fst_add, Prod.snd_add, Matrix.add_apply]
    rcases finSumFinEquiv.symm i with k | k <;> simp

theorem measurable_rowsH (r t : ℕ) : Measurable (rowsH (F := F) r t) := (rowEqM r t).measurable.comp (measurable_fromRows' r t)

omit [MeasurableSpace F] in
theorem rowsH_surj (r t : ℕ) : Function.Surjective (rowsH (F := F) r t) := fun y => ⟨(((rowEq r t).symm y).toRows₁, ((rowEq r t).symm y).toRows₂), by
  show rowEq r t (Matrix.fromRows _ _) = y
  rw [Matrix.fromRows_toRows, Equiv.apply_symm_apply]⟩

theorem map_rowsH (r t : ℕ) (m : Measure (Matrix (Fin r) (Fin r) F × Matrix (Fin t) (Fin r) F)) :
    (m.map (fun p => Matrix.fromRows p.1 p.2)).map (rowEqM r t) = m.map (rowsH r t) := by
  rw [Measure.map_map (rowEqM r t).measurable (measurable_fromRows' r t)]
  rfl

theorem measurableSet_intMat [TopologicalSpace F] [OpensMeasurableSpace F] {O : Subring F} (hO : IsOpen (O : Set F)) (n m : ℕ) :
    MeasurableSet (intMat O n m) := by
  have e : intMat O n m = ⋂ i, ⋂ j, (fun y : Matrix (Fin n) (Fin m) F => y i j) ⁻¹' (O : Set F) := by
    ext y; simp [intMat]
  rw [e]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    ((measurable_pi_apply j).comp (measurable_pi_apply i)) hO.measurableSet

omit [MeasurableSpace F] in
theorem preimage_rowsH (O : Subring F) (r t : ℕ) :
    (rowsH (F := F) r t) ⁻¹' intMat O (r + t) r = intMat O r r ×ˢ intMat O t r := by
  ext ⟨A, B⟩
  simp only [Set.mem_preimage, Set.mem_prod]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i j
      have hij := h (finSumFinEquiv (Sum.inl i)) j
      change rowEq r t (Matrix.fromRows A B) _ j ∈ O at hij
      rw [rowEq_apply, Equiv.symm_apply_apply] at hij
      exact hij
    · intro i j
      have hij := h (finSumFinEquiv (Sum.inr i)) j
      change rowEq r t (Matrix.fromRows A B) _ j ∈ O at hij
      rw [rowEq_apply, Equiv.symm_apply_apply] at hij
      exact hij
  · rintro ⟨h1, h2⟩ i j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
    change rowEq r t (Matrix.fromRows A B) _ j ∈ O
    rw [rowEq_apply, Equiv.symm_apply_apply]
    rcases s with k | k
    · exact h1 k j
    · exact h2 k j

end Dx

end GlobalTheory.Mem.SingleQ

namespace GlobalTheory.Mem.SingleQ

section Main

variable {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))

theorem absNorm_ne_zero₂ : qP P ≠ 0 := by
  unfold qP
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact P.ne_bot

theorem finite_kF : Finite (kF (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) (piP_mem P)) := Nat.finite_of_card_ne_zero (by rw [GlobalTheory.T.card_residueRing_completion_chosenUniformiser L P (piP_mem P)]; exact absNorm_ne_zero₂ P)

theorem vol_Jset (r : ℕ) [MeasurableSpace (P.adicCompletion L)] [BorelSpace (P.adicCompletion L)]
    (ν₁ : Measure (Matrix (Fin r) (Fin r) (P.adicCompletion L))) [ν₁.IsAddLeftInvariant]
    (h1 : ν₁ (intMat (OP P) r r) = 1) :
    (ν₁ (Jset (GLint (OP P) r))).toReal = Formalism.MainNotions.ZetaProductPairs.qE (qP P : ℝ) 1 r := by
  haveI := isMaximal_span (piP_mem P) (GlobalTheory.T.isLocalAt_completionIntegers_chosenUniformiser L P)
  letI : Field (kF (OP P) _ (piP_mem P)) := Ideal.Quotient.field _
  letI : Fintype (kF (OP P) _ (piP_mem P)) := @Fintype.ofFinite _ (finite_kF P)
  have hc : Nat.card (kF (OP P) _ (piP_mem P)) = qP P := GlobalTheory.T.card_residueRing_completion_chosenUniformiser L P (piP_mem P)
  have h := Formalism.DoubleCosetMeasures.Final.volJadd (P.adicCompletion L) (OP P) (isOpen_OP P) _ (piP_mem P) (Units.ne_zero _)
    (GlobalTheory.T.isLocalAt_completionIntegers_chosenUniformiser L P) (finite_kF P) r ν₁ (GLint (OP P) r) (fun g hg => hg.1) le_rfl
  rw [Formalism.DoubleCosetMeasures.Final.glRed (P.adicCompletion L) (OP P) _ (piP_mem P) (Units.ne_zero _) (GlobalTheory.T.isLocalAt_completionIntegers_chosenUniformiser L P)
    (finite_kF P) r, h1, mul_one, hc] at h
  have hG := GlobalTheory.T.card_GL_finiteField_eq_pow_mul_prod (kF (OP P) _ (piP_mem P)) r
  rw [Fintype.card_eq_nat_card, hc] at hG
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_natCast, hG] at h'
  have hq : (qP P : ℝ) ^ (r * r) ≠ 0 := pow_ne_zero _ (by exact_mod_cast absNorm_ne_zero₂ P)
  exact mul_right_cancel₀ hq (by rw [h', mul_comm])

theorem vol_II (r t : ℕ) [MeasurableSpace (P.adicCompletion L)] [BorelSpace (P.adicCompletion L)]
    (ν₂ : Measure (Matrix (Fin t) (Fin r) (P.adicCompletion L))) [ν₂.IsAddLeftInvariant]
    (h2 : ν₂ (intMat (OP P) t r) = 1) :
    (ν₂ (IIset (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L))).toReal =
      (qP P : ℝ) ^ (-((t * r : ℕ) : ℤ)) := by
  have hq : (Nat.card (kF (OP P) _ (piP_mem P)) : ENNReal) = (qP P : ENNReal) := by
    rw [GlobalTheory.T.card_residueRing_completion_chosenUniformiser L P (piP_mem P)]
  have h := Formalism.DoubleCosetMeasures.Final.volII (P.adicCompletion L) (OP P) (isOpen_OP P) _ (piP_mem P) (Units.ne_zero _)
    (finite_kF P) t r ν₂
  rw [h2, hq] at h
  have e : ν₂ (IIset (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L)) = ((qP P : ENNReal) ^ (t * r))⁻¹ :=
    ENNReal.eq_inv_of_mul_eq_one_left h
  rw [e, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast, _root_.zpow_neg, zpow_natCast]

end Main

end GlobalTheory.Mem.SingleQ

namespace GlobalTheory.Mem.SingleQ

theorem parJ_zero {F : Type} [Field F] (O : Subring F) (ϖ : F) (r : ℕ) :
    parJ O ϖ r 0 = ((GLint O r : Subgroup (GL (Fin r) F)) : Set (GL (Fin r) F)) := by
  ext k
  simp only [parJ, Set.mem_setOf_eq, SetLike.mem_coe]
  exact ⟨fun h => h.1, fun h => ⟨h, fun i => i.elim0⟩⟩

theorem stepAt_one : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)), Deg1 P →
    ∀ (δ ν : (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → IsNu P ν → ∀ r t : ℕ, 1 ≤ t →
    StepAt P δ (fun _ => ν) r t 0 (zVal1 (qP P) r t : ℂ) := by
  intro L _ _ P _ δ ν hδ hν r t _
  obtain ⟨nrm, hnrm⟩ := GlobalTheory.Mem.NrmCompl.exists_isNrm L P
  letI : MeasurableSpace (P.adicCompletion L) := borel _
  haveI : BorelSpace (P.adicCompletion L) := ⟨rfl⟩
  refine ⟨nrm, hnrm, ?_⟩
  have hchar : ∀ k : GLint (OP P) r,
      (((ν * δ) (GeneralLinearGroup.det (k : GL (Fin r) (P.adicCompletion L))) : ℂˣ) : ℂ) *
        (((nrm (((GeneralLinearGroup.det (k : GL (Fin r) (P.adicCompletion L))) : (P.adicCompletion L)ˣ) :
          P.adicCompletion L)) ^ (((r + t : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        (((δ.comp (GeneralLinearGroup.det.comp (GLint (OP P) r).subtype))⁻¹ k : ℂˣ) : ℂ) *
        (starRingEnd ℂ) (((1 : GLint (OP P) r →* ℂˣ) k : ℂˣ) : ℂ) = 1 := by
    intro k
    have hu := isUnitAt_det P k.2
    have hd : (((δ (GeneralLinearGroup.det (k : GL (Fin r) (P.adicCompletion L)))) : ℂˣ) : ℂ) ≠ 0 :=
      Units.ne_zero _
    rw [MonoidHom.mul_apply, Units.val_mul, hν.unr _ hu, (hnrm _).1 hu, Real.one_rpow]
    simp [Units.val_inv_eq_inv_val, hd]
  obtain ⟨μ, hμ, hμ1⟩ := GlobalTheory.T.exists_haar_GL_completion_integers_vol_one L P r
  obtain ⟨ν₁, hν₁, hs₁, hν₁1⟩ := GlobalTheory.T.exists_addHaar_completionIntegralMatrices_vol_one L P r r
  obtain ⟨ν₂, hν₂, hs₂, hν₂1⟩ := GlobalTheory.T.exists_addHaar_completionIntegralMatrices_vol_one L P t r
  haveI := hν₁
  haveI := hν₂
  haveI := hs₁
  haveI := hs₂
  haveI hA1 : MeasurableAdd (Matrix (Fin r) (Fin r) (P.adicCompletion L)) :=
    inferInstanceAs (MeasurableAdd (Fin r → Fin r → P.adicCompletion L))
  haveI hA2 : MeasurableAdd (Matrix (Fin t) (Fin r) (P.adicCompletion L)) :=
    inferInstanceAs (MeasurableAdd (Fin t → Fin r → P.adicCompletion L))
  haveI hA3 : MeasurableAdd (Matrix (Fin (r + t)) (Fin r) (P.adicCompletion L)) :=
    inferInstanceAs (MeasurableAdd (Fin (r + t) → Fin r → P.adicCompletion L))
  haveI hA4 : MeasurableAdd (Matrix (Fin r) (Fin r) (P.adicCompletion L) × Matrix (Fin t) (Fin r) (P.adicCompletion L)) :=
    ⟨fun c => by
      first
      | exact ((measurable_const_add c.1).comp measurable_fst).prodMk ((measurable_const_add c.2).comp measurable_snd)
      | exact ((measurable_const_add c.1).comp measurable_fst).prod_mk ((measurable_const_add c.2).comp measurable_snd),
     fun c => by
      first
      | exact ((measurable_add_const c.1).comp measurable_fst).prodMk ((measurable_add_const c.2).comp measurable_snd)
      | exact ((measurable_add_const c.1).comp measurable_fst).prod_mk ((measurable_add_const c.2).comp measurable_snd)⟩
  have hc : ∀ g, mcoef (OP P) μ (fun _ : GL (Fin r) (P.adicCompletion L) => (1 : ℂ)) g = 1 := by
    intro g
    simp [mcoef, setIntegral_const, Measure.real, hμ1]
  show IsStep (OP P) _ nrm δ (fun _ => ν) r t 0 _
  unfold IsStep
  rw [Nat.zero_mul, Nat.zero_add, Nat.one_mul]
  refine ⟨ℂ, inferInstance, inferInstance, 1, isUnrM_one (OP P) nrm r _, fun _ => 1,
    one_mem_typeSp (OP P) _ nrm δ r, μ, (ν₁.prod ν₂).map (rowsH r t), hμ, ?_, hc 1, ?_, ?_, ?_⟩
  · rw [parJ_zero]; exact hμ1
  · exact isAddLeftInvariant_map (rowsH r t) (measurable_rowsH r t) (rowsH_surj r t)
  · show Measure.map (rowsH r t) (ν₁.prod ν₂) (intMat (OP P) (r + t) r) = 1
    rw [Measure.map_apply (measurable_rowsH r t) (measurableSet_intMat (isOpen_OP P) _ _), preimage_rowsH,
      Measure.prod_prod, hν₁1, hν₂1, one_mul]
  · have hlam : ∀ (g : GL (Fin r) (P.adicCompletion L)) (k : GLint (OP P) r),
        mcoef (OP P) μ (fun _ => (1 : ℂ)) (g * k) =
          (((1 : GLint (OP P) r →* ℂˣ) k : ℂˣ) : ℂ) * mcoef (OP P) μ (fun _ => (1 : ℂ)) g := by
      intro g k; rw [hc, hc]; simp
    have hρ : ∀ k, ‖(((δ.comp (GeneralLinearGroup.det.comp (GLint (OP P) r).subtype))⁻¹ k : ℂˣ) : ℂ)‖ = 1 := by
      intro k; simp [hδ.unitary]
    have key := Formalism.DoubleCosetMeasures.Final.lemmaUSplit (P.adicCompletion L) r t (OP P) (isOpen_OP P) _ (Units.ne_zero (piP P))
      (GLint (OP P) r) (isCompact_GLint P r) (fun k hk => hk.1)
      ((δ.comp (GeneralLinearGroup.det.comp (GLint (OP P) r).subtype))⁻¹) hρ (ν * δ) nrm 1
      hchar
      (mcoef (OP P) μ fun _ => (1 : ℂ)) hlam μ ν₁ ν₂
    have hΦ : (phiQ (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) δ r t 0 ∘ rowEq r t) =
        phiU (OP P) _ (GLint (OP P) r) ((δ.comp (GeneralLinearGroup.det.comp (GLint (OP P) r).subtype))⁻¹) :=
      funext (phiQ_rowEq (OP P) _ δ r t)
    rw [← hΦ, ← localZ_map, map_rowsH] at key
    refine Eq.trans ?_ key.symm
    rw [hμ1, vol_Jset P r ν₁ hν₁1, vol_II P r t ν₂ hν₂1, hc 1]
    simp [zVal1]

end GlobalTheory.Mem.SingleQ
end
end

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.singleBlock_doublingIntegral_value : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)), Deg1 P → ∀ (δ ν : (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → IsNu P ν → ∀ r t : ℕ, 1 ≤ t → StepAt P δ (fun _ => ν) r t 0 (zVal1 (qP P) r t : ℂ) := by
  atlas_forward_decl GlobalTheory.Mem.SingleQ.stepAt_one
end

section
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

noncomputable section
namespace GlobalTheory.Mem.HD.RamBoth

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add]
  simpa using h

theorem exists_intCast_cong {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (hp : (Ideal.absNorm w.asIdeal).Prime) (z : w.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ k : ℤ, Valued.v (algebraMap E (w.adicCompletion E) (k : E) - z) ≤ WithZero.exp (-1 : ℤ) := by
  obtain ⟨b, hb⟩ := GlobalTheory.CMVal.Euler.SplitPair.exists_int_cong w z hz
  have hc : Nat.card (𝓞 E ⧸ w.asIdeal) = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Fact (Nat.card (𝓞 E ⧸ w.asIdeal)).Prime := ⟨hc ▸ hp⟩
  haveI : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  have htop : AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal) = ⊤ := by
    rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card (AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal)) with h | h
    · exfalso
      have : (1 : 𝓞 E ⧸ w.asIdeal) ∈ AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal) := AddSubgroup.mem_zmultiples 1
      rw [h, AddSubgroup.mem_bot] at this
      exact one_ne_zero this
    · exact h
  obtain ⟨k, hk⟩ : Ideal.Quotient.mk w.asIdeal b ∈ AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal) := htop ▸ AddSubgroup.mem_top _
  have hk' : ((k : 𝓞 E ⧸ w.asIdeal)) = Ideal.Quotient.mk w.asIdeal b := by simpa using hk
  have hmem : b - (k : 𝓞 E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hk', map_intCast, sub_self]
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) ((b : E) - (k : E))) ≤ WithZero.exp (-1 : ℤ) := by
    have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
    rw [hval]
    refine le_exp_neg_one_of_lt_one ?_
    have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w (b - (k : 𝓞 E))).2 hmem
    simpa using this
  have hb' : Valued.v (algebraMap E (w.adicCompletion E) (b : E) - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := hb
  refine ⟨k, ?_⟩
  have := Valuation.map_sub_le _ (hb'.trans (by simp)) h1
  rw [map_sub (algebraMap E (w.adicCompletion E)), sub_sub_sub_cancel_left] at this
  exact this

theorem mem_aboveF_iff (D : D7) {v : HeightOneSpectrum (𝓞 D.host.F)} {R : HeightOneSpectrum (𝓞 D.host.E)} :
    R ∈ aboveF (L := D.host.E) D.host.F v ↔ R.under (𝓞 D.host.F) = v := by
  rw [aboveF, Set.Finite.mem_toFinset]; rfl

open Classical in

theorem aboveF_eq_pair (D : D7) {v : HeightOneSpectrum (𝓞 D.host.F)} {w P : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ aboveF (L := D.host.E) D.host.F v) (hP : P ∈ aboveF (L := D.host.E) D.host.F v) (hne : w ≠ P) :
    aboveF (L := D.host.E) D.host.F v = {w, P} := by
  haveI := v.isMaximal
  haveI : NoZeroSMulDivisors (𝓞 D.host.F) (𝓞 D.host.E) := ⟨fun {c x} e => by
    rw [Algebra.smul_def, mul_eq_zero,
      map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))] at e
    exact e⟩
  have h1 := Ideal.card_primesOverFinset_le_finrank (𝓞 D.host.E) D.host.F D.host.E v.ne_bot
  rw [D.sp.cm.deg2] at h1
  have h2 : (aboveF (L := D.host.E) D.host.F v).card ≤ (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 D.host.E)).card := by
    refine Finset.card_le_card_of_injOn HeightOneSpectrum.asIdeal (fun R hR => ?_)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
    rw [Finset.mem_coe, mem_aboveF_iff] at hR
    rw [IsDedekindDomain.coe_primesOverFinset v.ne_bot]
    exact ⟨R.isPrime, ⟨hR ▸ rfl⟩⟩
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro R hR
    rw [Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl <;> assumption
  · rw [Finset.card_pair hne]; omega

theorem unrAt_of_pair {E : Type} [Field E] [NumberField E] {F : Type} [Field F] [NumberField F] [Algebra F E]
    [DecidableEq (HeightOneSpectrum (𝓞 E))] (χ : HChar E) {v : HeightOneSpectrum (𝓞 F)} {w P : HeightOneSpectrum (𝓞 E)}
    (hw : w.under (𝓞 F) = v) (hP : P.under (𝓞 F) = v) (hne : w ≠ P) (hS : aboveF (L := E) F v = {w, P})
    (hp : (Ideal.absNorm w.asIdeal).Prime) (hF : χ.TrivOn F) (ht : χ.TameAt w) (hun : χ.UnrAt P) : χ.UnrAt w := by
  intro u hu
  have hu1 : Valued.v (u : w.adicCompletion E) = 1 := hu
  obtain ⟨k, hk⟩ := exists_intCast_cong w hp u hu1.le
  have hval : ∀ (R : HeightOneSpectrum (𝓞 E)), Valued.v (algebraMap E (R.adicCompletion E) (k : E)) = 1 ↔
      (k : 𝓞 E) ∉ R.asIdeal := fun R => by
    have h1 : Valued.v (algebraMap E (R.adicCompletion E) (k : E)) = R.valuation E (k : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' R (k : E)
    have h2 : R.valuation E (k : E) = R.intValuation (k : 𝓞 E) := by
      rw [← map_intCast (algebraMap (𝓞 E) E) k]
      exact HeightOneSpectrum.valuation_of_algebraMap (K := E) R (k : 𝓞 E)
    rw [h1, h2, HeightOneSpectrum.intValuation_eq_one_iff]
  have hmem : ∀ (R : HeightOneSpectrum (𝓞 E)), R.under (𝓞 F) = v → ((k : 𝓞 E) ∈ R.asIdeal ↔ (k : 𝓞 F) ∈ v.asIdeal) :=
    fun R hR => by
      rw [← hR, ← map_intCast (algebraMap (𝓞 F) (𝓞 E)) k]
      exact Iff.rfl
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have h5 : Valued.v (algebraMap E (w.adicCompletion E) (k : E)) = 1 := by
    rw [Valuation.map_eq_of_sub_lt _ (hu1 ▸ hk.trans_lt hlt), hu1]
  have hkw := (hval w).1 h5
  have hkP : (k : 𝓞 E) ∉ P.asIdeal := fun h => hkw ((hmem w hw).2 ((hmem P hP).1 h))
  have hk0 : (k : F) ≠ 0 := by
    intro h
    have : k = 0 := by exact_mod_cast h
    exact hkw (by simp [this])
  have hco : ∀ R : HeightOneSpectrum (𝓞 E), ((atFin R (upF F (Units.mk0 (k : F) hk0)) : (R.adicCompletion E)ˣ) :
      R.adicCompletion E) = algebraMap E (R.adicCompletion E) (k : E) := fun R => by
    rw [← map_intCast (algebraMap F E) k]
    rfl
  have h7 := hF.1 v (Units.mk0 (k : F) hk0)
  unfold HChar.resFin at h7
  rw [MonoidHom.finsetProd_apply, hS, Finset.prod_pair hne] at h7
  have h6 : χ.loc P (atFin P (upF F (Units.mk0 (k : F) hk0))) = 1 := hun _ (by
    unfold IsUnitAt
    rw [hco, (hval P).2 hkP])
  change χ.loc w (atFin w (upF F (Units.mk0 (k : F) hk0))) * χ.loc P (atFin P (upF F (Units.mk0 (k : F) hk0))) = 1 at h7
  rw [h6, mul_one] at h7
  have h8 : χ.loc w (atFin w (upF F (Units.mk0 (k : F) hk0)) / u) = 1 := by
    refine ht _ ?_ ?_
    · unfold IsUnitAt
      rw [Units.val_div_eq_div_val, map_div₀, hco, h5, hu1, div_one]
    · rw [Units.val_div_eq_div_val, div_sub_one u.ne_zero, map_div₀, hu1, div_one, hco]
      exact hk
  rw [map_div, div_eq_one, h7] at h8
  exact h8.symm

theorem ram_both : ∀ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch), TupPins Tp →
    ∀ (μ : D.what₂.Tup) (v : HeightOneSpectrum (𝓞 D.host.F)) (w P : HeightOneSpectrum (𝓞 D.host.E)),
    w ∈ aboveF (L := D.host.E) D.host.F v → P ∈ aboveF (L := D.host.E) D.host.F v →
    ¬ (Tp.xi μ).UnrAt w → ¬ (Tp.xi μ).UnrAt P := by
  classical
  intro D C nch Tp hT μ v w P hw hP hr hun
  by_cases hne : w = P
  · exact hr (hne ▸ hun)
  · exact hr (unrAt_of_pair _ ((mem_aboveF_iff D).1 hw) ((mem_aboveF_iff D).1 hP) hne
      (by convert aboveF_eq_pair D hw hP hne) (hT.ram μ w hr).2.1 (Tp.xi_triv μ) (Tp.xi_tame μ w) hun)

end GlobalTheory.Mem.HD.RamBoth

end
end

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupleChar_ramified_at_all_primes_over_place : ∀ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch), TupPins Tp → ∀ (μ : D.what₂.Tup) (v : HeightOneSpectrum (𝓞 D.host.F)) (w P : HeightOneSpectrum (𝓞 D.host.E)), w ∈ aboveF (L := D.host.E) D.host.F v → P ∈ aboveF (L := D.host.E) D.host.F v → ¬ (Tp.xi μ).UnrAt w → ¬ (Tp.xi μ).UnrAt P := by
  atlas_forward_decl GlobalTheory.Mem.HD.RamBoth.ram_both
end

section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

noncomputable section

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

theorem mem_aboveF_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {P : HeightOneSpectrum (𝓞 D.host.E)} :
    P ∈ aboveF (L := D.host.E) D.host.F v ↔ P.under (𝓞 D.host.F) = v := by
  rw [aboveF, Set.Finite.mem_toFinset]; rfl

theorem absNorm_eq_of_mem {v : HeightOneSpectrum (𝓞 D.host.F)} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : P ∈ aboveF (L := D.host.E) D.host.F v) (h : (Ideal.absNorm P.asIdeal).Prime) :
    Ideal.absNorm v.asIdeal = Ideal.absNorm P.asIdeal := by
  rw [mem_aboveF_iff] at hP
  subst hP
  have hd : Ideal.absNorm (P.under (𝓞 D.host.F)).asIdeal ∣ Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact AddSubgroup.card_dvd_of_injective
      (Ideal.quotientMap P.asIdeal (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) le_rfl).toAddMonoidHom
      Ideal.quotientMap_injective
  exact ((Nat.dvd_prime h).1 hd).resolve_left fun h1 =>
    (P.under (𝓞 D.host.F)).isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)

theorem eq_exp_of_le {x : WithZero (Multiplicative ℤ)} {m : ℤ} (h : x ≤ WithZero.exp m)
    (h' : ¬ x ≤ WithZero.exp (m - 1)) : x = WithZero.exp m := by
  refine le_antisymm h (not_lt.1 fun h1 => h' ?_)
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, sub_add_cancel]
  exact h1

theorem degreeOne_of_prime_absNorm_not_mem_sq {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))
    (h1 : (Ideal.absNorm P.asIdeal).Prime) (h2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L) ∉ P.asIdeal ^ 2) : Deg1 P := by
  refine ⟨h1, ?_⟩
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L) ∈ P.asIdeal := Ideal.absNorm_mem _
  have e : ((qP P : ℕ) : P.adicCompletion L) =
      algebraMap L (P.adicCompletion L) (algebraMap (𝓞 L) L ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L)) := by
    simp [qP]
  have hv : ∀ y : L, Valued.v (algebraMap L (P.adicCompletion L) y) = P.valuation L y := fun y =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P y
  rw [e, hv, HeightOneSpectrum.valuation_of_algebraMap]
  have a1 := (P.intValuation_le_pow_iff_mem _ 1).2 (by simpa using hmem)
  have a2 : ¬ P.intValuation ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((P.intValuation_le_pow_iff_mem _ 2).1 h)
  refine eq_exp_of_le (by simpa using a1) fun h => a2 ?_
  convert h using 2
  norm_num

theorem ramTransfer : ∀ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch), TupPins Tp → ∀ (μ : D.what₂.Tup) (v : HeightOneSpectrum (𝓞 D.host.F)) (w P : HeightOneSpectrum (𝓞 D.host.E)), w ∈ aboveF (L := D.host.E) D.host.F v → P ∈ aboveF (L := D.host.E) D.host.F v → ¬ (Tp.xi μ).UnrAt w → ¬ (Tp.xi μ).UnrAt P := GlobalTheory.T.tupleChar_ramified_at_all_primes_over_place

theorem finite_inQ (Tp : TupTied D C nch) (μ : D.what₂.Tup) :
    {v : HeightOneSpectrum (𝓞 D.host.F) | Tp.InQ' μ v}.Finite := by
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified (Tp.xi μ)).image fun w => w.under (𝓞 D.host.F)).subset ?_
  rintro v ⟨w, hw, hr⟩
  exact ⟨w, hr, mem_aboveF_iff.1 hw⟩

theorem prime_eq_of_overP {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h1 : OverP D.host p w) (h2 : OverP D.host q w) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  have h : ((a * p + b * q : ℤ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    push_cast
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ (by exact_mod_cast h1))
      (w.asIdeal.mul_mem_left _ (by exact_mod_cast h2))
  rw [hab, Int.cast_one] at h
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)

theorem finite_qp (Tp : TupTied D C nch) (μ : D.what₂.Tup) :
    {p : ℕ | p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w}.Finite := by
  have hs : ∀ w : HeightOneSpectrum (𝓞 D.host.E), Set.Subsingleton {p : ℕ | p.Prime ∧ OverP D.host p w} :=
    fun w p hp q hq => prime_eq_of_overP hp.1 hq.1 hp.2 hq.2
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified (Tp.xi μ)).biUnion fun w _ => (hs w).finite).subset ?_
  rintro p ⟨hp, w, hw, hr⟩
  exact Set.mem_biUnion hr ⟨hp, hw⟩

def qpSet (Tp : TupTied D C nch) (μ : D.what₂.Tup) : Finset ℕ := (finite_qp Tp μ).toFinset

theorem mem_qpSet (Tp : TupTied D C nch) (μ : D.what₂.Tup) (p : ℕ) :
    p ∈ qpSet Tp μ ↔ p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w := by
  rw [qpSet, Set.Finite.mem_toFinset]; rfl

theorem ramifiedRationalPrimesOfTuple_baseTuple_eq_empty (Tp : TupTied D C nch) : qpSet Tp D.what₂.mu0 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
  obtain ⟨-, w, -, hr⟩ := (mem_qpSet Tp _ p).1 hp
  exact hr fun x _ => by rw [Tp.trueColumnChoices_heckeChar_reference_eq_one]; rfl

theorem qpSet_muAt (Tp : TupTied D C nch) (hp : TupPins Tp) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w ∉ qpSet Tp (D.what₂.muAt w) := fun h => by
  obtain ⟨-, w', hw', hr⟩ := (mem_qpSet Tp _ _).1 h
  exact hr (hp.atl w w' hw')

theorem qpSet_g (Tp : TupTied D C nch) (hp : TupPins Tp) (μ : D.what₂.Tup) (i : Fin 2) :
    D.host.g i ∉ qpSet Tp μ := fun h => by
  obtain ⟨-, w, hw, hr⟩ := (mem_qpSet Tp _ _).1 h
  exact (hp.ram μ w hr).2.2.2 i hw

theorem one_lt_absNorm {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) :
    1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

variable (Tp : TupTied D C nch) (hp : TupPins Tp) (Pv : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
  (hPv : ∀ v, Pv v ∈ aboveF (L := D.host.E) D.host.F v)

include hp hPv in

theorem ram_Pv (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) :
    ¬ (Tp.xi μ).UnrAt (Pv v.1) := by
  obtain ⟨w, hw, hr⟩ := v.2
  exact ramTransfer D C nch Tp hp μ v.1 w (Pv v.1) hw (hPv v.1) hr

include hp hPv in
theorem chosenPrimeAbove_ramifiedPlace_degreeOne (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) : Deg1 (Pv v.1) :=
  degreeOne_of_prime_absNorm_not_mem_sq _ (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.1 (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.2.1

include hp hPv in
theorem offg_Pv (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) :
    ∀ k, ¬ OverP D.host (D.host.g k) (Pv v.1) :=
  (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.2.2

include hp hPv in
theorem absNorm_Pv (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) :
    Ideal.absNorm v.1.asIdeal = qP (Pv v.1) :=
  absNorm_eq_of_mem (hPv v.1) (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.1

theorem one_le_letterBlockLength : 1 ≤ D.R.t := by have := D.R.three_m_lt_t; omega

include hp hPv in

theorem stepEx (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) (j : ℕ) :
    (∃ n, TypeDimAt (Pv v.1) (delQ Tp μ (Pv v.1)) (nuP C (Pv v.1)) D.R.r D.R.t j n) ∧
      ∃ z, StepAt (Pv v.1) (delQ Tp μ (Pv v.1)) (nuP C (Pv v.1)) D.R.r D.R.t j z :=
  GlobalTheory.T.exists_type_dimension_and_local_integrals_degree_one D.host.E (Pv v.1) (chosenPrimeAbove_ramifiedPlace_degreeOne Tp hp Pv hPv μ v) _ _ (isDel_delQ Tp μ (ram_Pv Tp hp Pv hPv μ v))
    (isNu_nuP C (offg_Pv Tp hp Pv hPv μ v)) D.R.r D.R.t j one_le_letterBlockLength

def zq (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) : ℕ → ℂ
  | 0 => 0
  | j + 1 => (stepEx Tp hp Pv hPv μ v j).2.choose

end GlobalTheory.Mem.HD.ReQ

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}
variable (Tp : TupTied D C nch) (hp : TupPins Tp) (Pv : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
  (hPv : ∀ v, Pv v ∈ aboveF (L := D.host.E) D.host.F v)

def reQ (Z₀ : DivX D) : DivX D :=
  { Z₀ with
    Qp := qpSet Tp
    degreeZero_partial_set_empty := ramifiedRationalPrimesOfTuple_baseTuple_eq_empty Tp
    Qp_muAt := qpSet_muAt Tp hp
    Qp_g := fun μ _ i => qpSet_g Tp hp μ i
    QPl := fun μ => {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}
    finQ := fun μ => by
      haveI : Finite {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v} := (finite_inQ Tp μ).to_subtype
      exact Fintype.ofFinite _
    qv := fun _ v => Ideal.absNorm v.1.asIdeal
    qv_gt := fun _ v => one_lt_absNorm v.1
    qv_char := fun μ _ v => by
      obtain ⟨w, hw, hr⟩ := v.2
      have hpr := (hp.ram μ w hr).2.1
      refine ⟨Ideal.absNorm v.1.asIdeal, (mem_qpSet Tp μ _).2 ⟨?_, w, ?_, hr⟩, ?_, rfl⟩
      · rw [absNorm_eq_of_mem hw hpr]; exact hpr
      · rw [absNorm_eq_of_mem hw hpr]; exact Ideal.absNorm_mem _
      · rw [absNorm_eq_of_mem hw hpr]; exact hpr
    nu := fun _ v i => ((nuP C (Pv v.1) i (piP (Pv v.1)) : ℂˣ) : ℂ)
    nu_ne := fun _ _ _ => Units.ne_zero _
    nu_abs := fun μ v i => (isNu_nuP C (offg_Pv Tp hp Pv hPv μ v) i).unitary _
    ZQ := zq Tp hp Pv hPv
    quotientLocalValueFirst := fun _ v => (zVal1 (qP (Pv v.1)) D.R.r D.R.t : ℂ)
    typeDim := fun μ v j => (stepEx Tp hp Pv hPv μ v j).1.choose }

def reducedDivisorCharacter (Z₀ : DivX D) : DivisorCharacterCompatibility D C nch Tp (reQ Tp hp Pv hPv Z₀) where
  Qp_iff := mem_qpSet Tp
  eQPl := fun _ => Equiv.refl _
  qv_eq := fun _ _ => rfl

theorem reLoc (Z₀ : DivX D) : QLocTiedC (reducedDivisorCharacter Tp hp Pv hPv Z₀) Pv := by
  refine ⟨fun μ v => hPv _, ?_⟩
  refine
    { qv_eq := fun μ v => absNorm_Pv Tp hp Pv hPv μ v
      deg1 := fun μ v => chosenPrimeAbove_ramifiedPlace_degreeOne Tp hp Pv hPv μ v
      ram := fun μ v => ram_Pv Tp hp Pv hPv μ v
      off_g := fun μ v => offg_Pv Tp hp Pv hPv μ v
      nu_eq := fun μ v i => ?_
      typeDim_eq := fun μ v j _ => (stepEx Tp hp Pv hPv μ v j).1.choose_spec
      ZQ_eq := fun μ v j _ => (stepEx Tp hp Pv hPv μ v j).2.choose_spec
      quotientLocalValueFirst_eq := fun μ v j _ _ => GlobalTheory.T.singleBlock_doublingIntegral_value D.host.E (Pv v.1) (chosenPrimeAbove_ramifiedPlace_degreeOne Tp hp Pv hPv μ v) _ _
        (isDel_delQ Tp μ (ram_Pv Tp hp Pv hPv μ v)) (isNu_nuP C (offg_Pv Tp hp Pv hPv μ v) j) D.R.r D.R.t one_le_letterBlockLength }
  show ((nuP C (Pv v.1) (i.1 + 1) (piP (Pv v.1)) : ℂˣ) : ℂ) = _
  rw [nuP_succ]
  rfl

@[simp] theorem reQ_geo (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).geo = Z₀.geo := rfl

@[simp] theorem reQ_Lev (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).Lev = Z₀.Lev := rfl

@[simp] theorem reQ_levPr (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).levPr = Z₀.levPr := rfl

@[simp] theorem reQ_shv (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).shv = Z₀.shv := rfl

@[simp] theorem reQ_shv_N (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).shv_N = Z₀.shv_N := rfl

@[simp] theorem reQ_shv_lev (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).shv_lev = Z₀.shv_lev := rfl

@[simp] theorem reQ_PlP (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).PlP = Z₀.PlP := rfl

@[simp] theorem reQ_plpNe (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).plpNe = Z₀.plpNe := rfl

@[simp] theorem reQ_wtP (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).wtP = Z₀.wtP := rfl

@[simp] theorem reQ_wtP_nonneg (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).divisorWeight_nonneg = Z₀.divisorWeight_nonneg := rfl

@[simp] theorem reQ_wtP_sum (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).divisorWeight_sum = Z₀.divisorWeight_sum := rfl

@[simp] theorem reQ_plP (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).plP = Z₀.plP := rfl

@[simp] theorem reQ_wtP_def (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).divisorWeight_def = Z₀.divisorWeight_def := rfl

@[simp] theorem reQ_jC (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).jC = Z₀.jC := rfl

@[simp] theorem reQ_Mp (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).Mp = Z₀.Mp := rfl

@[simp] theorem reQ_vdd (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).vdd = Z₀.vdd := rfl

@[simp] theorem reQ_vdd_unram (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).vdd_unram = Z₀.vdd_unram := rfl

@[simp] theorem reQ_phiFr_unram (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).phiFr_unram = Z₀.phiFr_unram := rfl

@[simp] theorem reQ_vdd_nonneg (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).vdd_nonneg = Z₀.vdd_nonneg := rfl

@[simp] theorem reQ_CurveM (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).CurveM = Z₀.CurveM := rfl

@[simp] theorem reQ_degM (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).degM = Z₀.degM := rfl

@[simp] theorem reQ_htMdl (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).htMdl = Z₀.htMdl := rfl

@[simp] theorem reQ_htCurve (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).htCurve = Z₀.htCurve := rfl

@[simp] theorem reQ_htCurve_deg (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).htCurve_deg = Z₀.htCurve_deg := rfl

@[simp] theorem reQ_MjH (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).MjH = Z₀.MjH := rfl

@[simp] theorem reQ_MjH_good (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).MjH_good = Z₀.MjH_good := rfl

@[simp] theorem reQ_jM (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).jM = Z₀.jM := rfl

@[simp] theorem reQ_jM_basis (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).jM_basis = Z₀.jM_basis := rfl

@[simp] theorem reQ_jM_lat (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).jM_lat = Z₀.jM_lat := rfl

@[simp] theorem reQ_MjLat_sub (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).MjLat_sub = Z₀.MjLat_sub := rfl

@[simp] theorem reQ_jM_metric (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).jM_metric = Z₀.jM_metric := rfl

@[simp] theorem reQ_Comp (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).Comp = Z₀.Comp := rfl

@[simp] theorem reQ_degHH (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).degHH = Z₀.degHH := rfl

@[simp] theorem reQ_Yv (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).Yv = Z₀.Yv := rfl

@[simp] theorem reQ_Ybd (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).Ybd = Z₀.Ybd := rfl

@[simp] theorem reQ_Lw (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).Lw = Z₀.Lw := rfl

@[simp] theorem reQ_iMj (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).iMj = Z₀.iMj := rfl

@[simp] theorem reQ_iMj_mem (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).iMj_mem = Z₀.iMj_mem := rfl

@[simp] theorem reQ_logLam (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).logLam = Z₀.logLam := rfl

@[simp] theorem reQ_logLam_base (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).logLam_base = Z₀.logLam_base := rfl

@[simp] theorem reQ_kapR (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).kapR = Z₀.kapR := rfl

@[simp] theorem reQ_kapR_pos (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).kapR_pos = Z₀.kapR_pos := rfl

@[simp] theorem reQ_kapR_conj (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).kapR_conj = Z₀.kapR_conj := rfl

@[simp] theorem reQ_Surf (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).Surf = Z₀.Surf := rfl

@[simp] theorem reQ_surfCh2 (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).surfCh2 = Z₀.surfCh2 := rfl

@[simp] theorem reQ_surfDegOm (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).surfDegOm = Z₀.surfDegOm := rfl

@[simp] theorem reQ_SurfFp (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).SurfFp = Z₀.SurfFp := rfl

@[simp] theorem reQ_surfFpCh2 (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).surfFpCh2 = Z₀.surfFpCh2 := rfl

@[simp] theorem reQ_plpFin (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).plpFin = Z₀.plpFin := rfl

@[simp] theorem reQ_compFin (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).compFin = Z₀.compFin := rfl

@[simp] theorem reQ_Qp (Z₀ : DivX D) : (reQ Tp hp Pv hPv Z₀).Qp = qpSet Tp := rfl

@[simp] theorem reQ_QPl (Z₀ : DivX D) (μ : D.what₂.Tup) :
    (reQ Tp hp Pv hPv Z₀).QPl μ = {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v} := rfl

end GlobalTheory.Mem.HD.ReQ

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

end GlobalTheory.Mem.HD.ReQ
end
end
