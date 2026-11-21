import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLatticeBasis
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexDet
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIsLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexTrans
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexPi
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesStdIndexDet
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealIndexPos
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealLatticeFG
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGramPosDef
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesCoordDet
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesProjLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotIndexSplit
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLineDegree
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotGramLog

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem OrthogonalLines.proof (hQ : LinesQuotDegreeBound.Statement)
    (hL : LinesLineDegree.Statement) : OrthogonalLines.Statement := by
  intro K _ _ n a d ha hd _ μ hμ m k b c hbc hmk
  obtain ⟨τ, -, hτ⟩ := hQ K n a d ha hd m k b c hbc hmk
  have hf : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have key : ∀ j, (Module.finrank ℚ K : ℝ) * μ ≤
      Real.log (idealIndex (a (τ j))) - 1 / 2 * ∑ σ : K →+* ℂ, Real.log (d σ (τ j)) := by
    intro j
    have h := hμ (τ j)
    rw [hL K n a d (τ j), normalise, le_div_iff₀ hf] at h
    linarith
  have hsum : ∑ _j : Fin k, (Module.finrank ℚ K : ℝ) * μ ≤
      ∑ j, (Real.log (idealIndex (a (τ j))) - 1 / 2 * ∑ σ : K →+* ℂ, Real.log (d σ (τ j))) :=
    Finset.sum_le_sum fun j _ => key j
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [normalise, le_div_iff₀ hf]
  have e : (k : ℝ) * μ * (Module.finrank ℚ K : ℝ) = (k : ℝ) * ((Module.finrank ℚ K : ℝ) * μ) := by
    ring
  linarith

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesGenIndexMono

theorem genIndex_of_le {G : Type*} [AddCommGroup G] {A A' : AddSubgroup G} (h : A ≤ A') :
    genIndex A' A = (A.relIndex A' : ℝ) := by
  unfold genIndex
  rw [AddSubgroup.relIndex_eq_one.mpr h, Nat.cast_one, div_one]

theorem genIndex_nonneg {G : Type*} [AddCommGroup G] (A B : AddSubgroup G) : 0 ≤ genIndex A B := by
  unfold genIndex
  positivity

end KLinesGenIndexMono

open KLinesGenIndexMono in

theorem LinesGenIndexMono.proof (h1 : LinesGenIndexTrans.Statement) : LinesGenIndexMono.Statement := by
  intro V _ _ _ A A' B hA hA' hB hle
  obtain ⟨hpos, heq⟩ := h1 V A' A B hA' hA hB
  have hle' : A.toAddSubgroup ≤ A'.toAddSubgroup := hle
  rw [← heq]
  rw [genIndex_of_le hle'] at hpos ⊢
  have hone : (1 : ℝ) ≤ (A.toAddSubgroup.relIndex A'.toAddSubgroup : ℝ) := by
    have : 0 < A.toAddSubgroup.relIndex A'.toAddSubgroup := by exact_mod_cast hpos
    exact_mod_cast this
  exact le_mul_of_one_le_left (genIndex_nonneg _ _) hone

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

namespace KLinesStdPi

theorem eq_sum_smul_single {K : Type*} [Field K] {k : ℕ} (y : Fin k → 𝓞 K) :
    (fun i => algebraMap (𝓞 K) K (y i)) = ∑ j, y j • (Pi.single j 1 : Fin k → K) := by
  funext i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply, Algebra.smul_def, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

end KLinesStdPi

theorem LinesStdPi.proof : LinesStdPi.Statement := by
  intro K _ k
  ext v
  simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      dsimp only
      rw [Pi.single_apply]
      split_ifs
      · exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      · exact Submodule.zero_mem _
    | zero => intro i; exact Submodule.zero_mem _
    | add x y _ _ hx hy => intro i; exact Submodule.add_mem _ (hx i) (hy i)
    | smul a x _ hx => intro i; exact Submodule.smul_mem _ a (hx i)
  · intro hv
    choose y hy using fun i => Submodule.mem_one.mp (hv i)
    have hv' : v = fun i => algebraMap (𝓞 K) K (y i) := funext fun i => (hy i).symm
    rw [hv', KLinesStdPi.eq_sum_smul_single]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

namespace KLinesProductFormula

theorem prod_norm_embeddings (K : Type) [Field K] [NumberField K] (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  classical
  have h := congr_arg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
  rw [norm_prod, ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => ‖f x‖)
    (fun φ => ‖φ x‖) fun _ => by simp [RingHom.equivRatAlgHom_apply]] at h
  rw [← h, eq_ratCast, ← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_ratCast]

end KLinesProductFormula

theorem LinesProductFormula.proof : LinesProductFormula.Statement := by
  intro K _ _ x hx
  rw [← KLinesProductFormula.prod_norm_embeddings K x, Real.log_prod]
  intro σ _
  exact norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx)

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField
open scoped nonZeroDivisors

namespace KLinesIdealStdIndex

theorem idealLattice_toAddSubgroup {K : Type} [Field K] {k : ℕ}
    (a : Fin k → FractionalIdeal (𝓞 K)⁰ K) :
    (idealLattice a).toAddSubgroup =
      AddSubgroup.pi Set.univ fun j => (a j : Submodule (𝓞 K) K).toAddSubgroup := by
  ext x
  simp [idealLattice, Submodule.mem_pi, AddSubgroup.mem_pi]

end KLinesIdealStdIndex

open KLinesIdealStdIndex in

theorem LinesIdealStdIndex.proof (h1 : LinesGenIndexPi.Statement) (h2 : LinesStdPi.Statement) :
    LinesIdealStdIndex.Statement := by
  intro K _ _ k a
  rw [idealLattice_toAddSubgroup, h2 K k, h1 (Fin k) K]
  rfl

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace KLinesGramChange

noncomputable def colMatrix {K : Type*} [Field K] {n : ℕ} (σ : K →+* ℂ) {ι : Type*}
    (u : ι → Fin n → K) : Matrix (Fin n) ι ℂ :=
  Matrix.of fun j a => σ (u a j)

theorem gramAt_eq {K : Type*} [Field K] {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ)
    {ι : Type*} [Fintype ι] (u : ι → Fin n → K) :
    gramAt h σ u = (colMatrix σ u)ᴴ * h * colMatrix σ u := by
  ext a b
  simp only [gramAt, embVec, colMatrix, Matrix.mul_apply, dotProduct, mulVec,
    conjTranspose_apply, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem colMatrix_transform {K : Type*} [Field K] {n : ℕ} (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    (u : ι → Fin n → K) (P : Matrix ι ι K) :
    colMatrix σ (fun a => ∑ b, P b a • u b) = colMatrix σ u * P.map σ := by
  ext j a
  simp only [colMatrix, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

end KLinesGramChange

open KLinesGramChange in

theorem LinesGramChange.proof : LinesGramChange.Statement := by
  intro K _ n h σ ι _ u P
  rw [gramAt_eq, gramAt_eq, colMatrix_transform, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem LinesGramDetChange.proof (h1 : LinesGramChange.Statement) :
    LinesGramDetChange.Statement := by
  intro K _ n h σ ι _ _ B u
  have hu : u = fun a => ∑ b, B.toMatrix u b a • B b := by
    funext a
    exact (B.sum_toMatrix_smul_self u a).symm
  have hg := h1 K n h σ ι (⇑B) (B.toMatrix u)
  rw [← hu] at hg
  rw [hg, det_mul, det_mul, det_conjTranspose, RingHom.map_det]
  simp only [RingHom.mapMatrix_apply]
  ring

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix
open scoped ComplexOrder

namespace KLinesFischer

theorem toBlocks₂₁_eq {m k : Type*} {M : Matrix (m ⊕ k) (m ⊕ k) ℂ} (hM : M.IsHermitian) :
    M.toBlocks₂₁ = M.toBlocks₁₂ᴴ := by
  ext i j
  simp only [toBlocks₂₁, toBlocks₁₂, conjTranspose_apply, of_apply]
  exact (hM.apply (Sum.inr i) (Sum.inl j)).symm

end KLinesFischer

theorem LinesFischer.proof : LinesFischer.Statement := by
  intro m k _ _ _ _ M hM
  have hA : M.toBlocks₁₁.PosDef := hM.submatrix (e := (Sum.inl : m → m ⊕ k)) Sum.inl_injective
  have hApos : 0 < M.toBlocks₁₁.det.re := MCDet.re_det_pos hA
  have hdet0 : M.toBlocks₁₁.det ≠ 0 := fun h => by simp [h] at hApos
  let _ : Invertible M.toBlocks₁₁ := invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hdet0)
  have hMe : M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₁₂ᴴ M.toBlocks₂₂ := by
    rw [← KLinesFischer.toBlocks₂₁_eq hM.1]
    exact (fromBlocks_toBlocks M).symm
  have hS : (M.toBlocks₂₂ - M.toBlocks₁₂ᴴ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂).PosSemidef := by
    have h := hM.posSemidef
    rw [hMe] at h
    exact (PosDef.fromBlocks₁₁ _ _ hA).mp h
  have hdet : M.det = M.toBlocks₁₁.det *
      (M.toBlocks₂₂ - M.toBlocks₁₂ᴴ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂).det := by
    conv_lhs => rw [hMe]
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hmono : (M.toBlocks₂₂ - M.toBlocks₁₂ᴴ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂).det.re ≤
      M.toBlocks₂₂.det.re := by
    refine MCDet.re_det_mono hS ?_
    rw [sub_sub_cancel]
    exact hA.posSemidef.inv.conjTranspose_mul_mul_same _
  have him : M.toBlocks₁₁.det.im = 0 := by
    have h := congrArg Complex.im (MCDet.det_eq_ofReal_re hA.posSemidef)
    simpa using h
  rw [hdet, Complex.mul_re, him, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left hmono hApos.le

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesDiagGram

theorem embVec_single {K : Type*} [Field K] (σ : K →+* ℂ) {n : ℕ} (x : Fin n) :
    embVec σ (Pi.single x 1 : Fin n → K) = Pi.single x 1 := by
  funext y
  simp only [embVec, Pi.single_apply]
  split_ifs <;> simp

end KLinesDiagGram

open KLinesDiagGram in

theorem LinesDiagGram.proof : LinesDiagGram.Statement := by
  intro K _ n d σ k τ hτ
  ext j j'
  simp only [gramAt, embVec_single, Matrix.diagonal_apply]
  rw [show (star (Pi.single (τ j) (1 : ℂ)) : Fin n → ℂ) = Pi.single (τ j) 1 by
    funext y; simp only [Pi.star_apply, Pi.single_apply]; split_ifs <;> simp]
  rw [single_dotProduct, one_mul, Matrix.mulVec_diagonal]
  simp only [Pi.single_apply, hτ.eq_iff]
  split_ifs with h
  · subst h; simp
  · simp

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix
open scoped ComplexOrder

theorem LinesGramFischerBound.proof (h1 : LinesGramPosDef.Statement)
    (h2 : LinesFischer.Statement) (h3 : LinesDiagGram.Statement) :
    LinesGramFischerBound.Statement := by
  intro K _ n m k d σ b τ hd hτ hli
  set t : Fin k → Fin n → K := fun j => Pi.single (τ j) 1 with ht
  set h : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun x => (d x : ℂ) with hh
  have hpos : h.PosDef := Matrix.PosDef.diagonal fun x => Complex.zero_lt_real.mpr (hd x)
  have hG := h1 K n h σ (Fin m ⊕ Fin k) (Sum.elim b t) hpos hli
  have hF := h2 (Fin m) (Fin k) _ hG
  have hB1 : (gramAt h σ (Sum.elim b t)).toBlocks₁₁ = gramAt h σ b := by
    ext i j; rfl
  have hB2 : (gramAt h σ (Sum.elim b t)).toBlocks₂₂ = gramAt h σ t := by
    ext i j; rfl
  have hD : gramAt h σ t = Matrix.diagonal fun j => (d (τ j) : ℂ) := h3 K n d σ k τ hτ
  rw [hB1, hB2, hD, Matrix.det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re] at hF
  exact hF

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesExtendBasis

theorem span_single_eq_top (K : Type) [Field K] (n : ℕ) :
    Submodule.span K (Set.range fun x : Fin n => (Pi.single x 1 : Fin n → K)) = ⊤ := by
  have h : (fun x : Fin n => (Pi.single x 1 : Fin n → K)) = ⇑(Pi.basisFun K (Fin n)) := by
    funext x
    simp
  rw [h]
  exact (Pi.basisFun K (Fin n)).span_eq

end KLinesExtendBasis

open KLinesExtendBasis in

theorem LinesExtendBasis.proof : LinesExtendBasis.Statement := by
  intro K _ n m k b hb hn
  set W : Submodule K (Fin n → K) := Submodule.span K (Set.range b) with hW
  let e : Fin n → (Fin n → K) := fun x => Pi.single x 1
  have hspan : Submodule.span K (Set.range (W.mkQ ∘ e)) = ⊤ := by
    rw [Set.range_comp, ← Submodule.map_span, span_single_eq_top, Submodule.map_top,
      Submodule.range_mkQ]
  obtain ⟨κ, a, ha, hsp, hli⟩ : ∃ (κ : Type) (a : κ → Fin n), Function.Injective a ∧
      Submodule.span K (Set.range ((W.mkQ ∘ e) ∘ a)) = Submodule.span K (Set.range (W.mkQ ∘ e)) ∧
      LinearIndependent K ((W.mkQ ∘ e) ∘ a) := exists_linearIndependent' K (W.mkQ ∘ e)
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let B : Module.Basis κ K ((Fin n → K) ⧸ W) := Module.Basis.mk hli (by rw [hsp, hspan])
  have hcard : Fintype.card κ = k := by
    have h1 := W.finrank_quotient_add_finrank
    rw [Module.finrank_eq_card_basis B, hW, finrank_span_eq_card hb, Module.finrank_fin_fun,
      Fintype.card_fin] at h1
    omega
  let σ : Fin k ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ σ, ha.comp σ.injective, ?_⟩
  let f : Fin m → W := fun i => ⟨b i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hf : LinearIndependent K f := LinearIndependent.of_comp W.subtype hb
  have hg : LinearIndependent K (Submodule.Quotient.mk (p := W) ∘ fun j => e (a (σ j))) :=
    hli.comp σ σ.injective
  exact LinearIndependent.sumElim_of_quotient hf (fun j => e (a (σ j))) hg

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem LinesCoordImage.proof : LinesCoordImage.Statement := by
  intro K _ n m k B b c j
  funext l
  simp [coordProj, LinearMap.funLeft_apply, Module.Basis.equivFun_apply, Matrix.toBlocks₂₂,
    Module.Basis.toMatrix_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

namespace KLinesProjIndexLower

theorem stdLattice_fg (K : Type) [Field K] [NumberField K] (k : ℕ) :
    ((stdLattice K k).restrictScalars ℤ).FG :=
  (Submodule.fg_span (Set.finite_range _)).restrictScalars

theorem stdLattice_span (K : Type) [Field K] [NumberField K] (k : ℕ) :
    Submodule.span K ((stdLattice K k : Submodule (𝓞 K) (Fin k → K)) : Set (Fin k → K)) = ⊤ :=
  (HermLattice.standard K k).span_eq

end KLinesProjIndexLower

open KLinesProjIndexLower in

theorem LinesProjIndexLower.proof (h1 : LinesProjLattice.Statement)
    (h2 : LinesIdealLatticeFG.Statement) (h3 : LinesIsLattice.Statement)
    (h4 : LinesGenIndexMono.Statement) (h5 : LinesIdealStdIndex.Statement) :
    LinesProjIndexLower.Statement := by
  intro K _ _ n m k a B τ ha hB hτ
  obtain ⟨hPfg, hPspan, hle⟩ := h1 K n m k a B τ ha hB hτ
  obtain ⟨hAfg, hAspan⟩ := h2 K k (fun j => a (τ j)) (fun j => ha (τ j))
  have hA := h3 K (Fin k) _ hAfg.restrictScalars hAspan
  have hP := h3 K (Fin k) _ hPfg hPspan
  have hS := h3 K (Fin k) _ (stdLattice_fg K k) (stdLattice_span K k)
  have key := h4 (Fin k → K) _ _ _ hA hP hS (Submodule.restrictScalars_mono ℤ hle)
  rw [← h5 K k (fun j => a (τ j))]
  exact key

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

theorem LinesQuotIndexLog.proof (h1 : LinesQuotIndexSplit.Statement)
    (h2 : LinesProjIndexLower.Statement) (h3 : LinesIdealIndexPos.Statement)
    (h4 : LinesProductFormula.Statement) (h5 : LinesCoordDet.Statement) :
    LinesQuotIndexLog.Statement := by
  intro K _ _ n m k a B b c τ ha hBl hBr hτ hli
  have hsplit := h1 K n m k a B b c τ ha hBl hBr hτ hli
  have hlow := h2 K n m k a B τ ha hBr hτ
  have hpos : 0 < ∏ j, idealIndex (a (τ j)) :=
    Finset.prod_pos fun j _ => h3 K (a (τ j)) (ha (τ j))
  have hdet := (h5 K n m k B b c hBl hli).2
  have hN : Algebra.norm ℚ (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hdet
  have hpf := h4 K _ hdet
  have hGpos := lt_of_lt_of_le hpos hlow
  have hNabs : |((Algebra.norm ℚ (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det : ℚ) : ℝ)| ≠ 0 :=
    abs_ne_zero.mpr (Rat.cast_ne_zero.mpr hN)
  rw [hsplit, Real.log_mul hGpos.ne' hNabs, hpf,
    ← Real.log_prod fun j _ => (h3 K (a (τ j)) (ha (τ j))).ne']
  exact add_le_add (Real.log_le_log hpos hlow) le_rfl

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem LinesQuotDegreeBound.proof (h1 : LinesExtendBasis.Statement)
    (h2 : LinesQuotIndexLog.Statement) (h3 : LinesQuotGramLog.Statement) :
    LinesQuotDegreeBound.Statement := by
  intro K _ _ n a d ha hd m k b c hbc hmk
  have hb : LinearIndependent K b := hbc.comp Sum.inl Sum.inl_injective
  obtain ⟨τ, hτ, hbs⟩ := h1 K n m k b hb hmk
  have hcard : Fintype.card (Fin m ⊕ Fin k) = Module.finrank K (Fin n → K) := by
    simp [hmk]
  let B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K) :=
    basisOfLinearIndependentOfCardEqFinrank' _ hbs hcard
  have hBl : ∀ i, B (Sum.inl i) = b i := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank']
  have hBr : ∀ j, B (Sum.inr j) = Pi.single (τ j) 1 := fun j => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank']
  refine ⟨τ, hτ, ?_⟩
  set D := (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det with hD
  have hI := h2 K n m k a B b c τ ha hBl hBr hτ hbc
  have hG : ∀ σ : K →+* ℂ,
      Real.log (gramAt (diagMetric d σ) σ (Sum.elim b c)).det.re -
          Real.log (gramAt (diagMetric d σ) σ b).det.re ≤
        ∑ j, Real.log (d σ (τ j)) + 2 * Real.log ‖σ D‖ := fun σ =>
    h3 K n m k (d σ) σ B b c τ (hd σ) hBl hBr hτ hbc
  have hGs := Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => hG σ
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm] at hGs
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold quotDegree
  linarith

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem LinesLatticeBasis.full : LinesLatticeBasis.Statement :=
  LinesLatticeBasis.proof

theorem LinesGenIndexDet.full : LinesGenIndexDet.Statement :=
  LinesGenIndexDet.proof LinesLatticeBasis.full

theorem LinesIsLattice.full : LinesIsLattice.Statement :=
  LinesIsLattice.proof

theorem LinesGenIndexTrans.full : LinesGenIndexTrans.Statement :=
  LinesGenIndexTrans.proof LinesLatticeBasis.full LinesGenIndexDet.full

theorem LinesGenIndexMono.full : LinesGenIndexMono.Statement :=
  LinesGenIndexMono.proof LinesGenIndexTrans.full

theorem LinesGenIndexPi.full : LinesGenIndexPi.Statement :=
  LinesGenIndexPi.proof

theorem LinesStdPi.full : LinesStdPi.Statement :=
  LinesStdPi.proof

theorem LinesStdIndexDet.full : LinesStdIndexDet.Statement :=
  LinesStdIndexDet.proof LinesGenIndexDet.full

theorem LinesIdealIndexPos.full : LinesIdealIndexPos.Statement :=
  LinesIdealIndexPos.proof LinesIsLattice.full LinesGenIndexTrans.full

theorem LinesProductFormula.full : LinesProductFormula.Statement :=
  LinesProductFormula.proof

theorem LinesIdealLatticeFG.full : LinesIdealLatticeFG.Statement :=
  LinesIdealLatticeFG.proof

theorem LinesIdealStdIndex.full : LinesIdealStdIndex.Statement :=
  LinesIdealStdIndex.proof LinesGenIndexPi.full LinesStdPi.full

theorem LinesGramChange.full : LinesGramChange.Statement :=
  LinesGramChange.proof

theorem LinesGramPosDef.full : LinesGramPosDef.Statement :=
  LinesGramPosDef.proof

theorem LinesGramDetChange.full : LinesGramDetChange.Statement :=
  LinesGramDetChange.proof LinesGramChange.full

theorem LinesFischer.full : LinesFischer.Statement :=
  LinesFischer.proof

theorem LinesDiagGram.full : LinesDiagGram.Statement :=
  LinesDiagGram.proof

theorem LinesGramFischerBound.full : LinesGramFischerBound.Statement :=
  LinesGramFischerBound.proof LinesGramPosDef.full LinesFischer.full LinesDiagGram.full

theorem LinesExtendBasis.full : LinesExtendBasis.Statement :=
  LinesExtendBasis.proof

theorem LinesCoordDet.full : LinesCoordDet.Statement :=
  LinesCoordDet.proof

theorem LinesCoordImage.full : LinesCoordImage.Statement :=
  LinesCoordImage.proof

theorem LinesQuotIndex.full : LinesQuotIndex.Statement :=
  LinesQuotIndex.proof

theorem LinesProjLattice.full : LinesProjLattice.Statement :=
  LinesProjLattice.proof LinesIdealLatticeFG.full

theorem LinesQuotIndexSplit.full : LinesQuotIndexSplit.Statement :=
  LinesQuotIndexSplit.proof LinesQuotIndex.full LinesCoordImage.full LinesCoordDet.full LinesIsLattice.full LinesGenIndexTrans.full LinesStdIndexDet.full LinesProjLattice.full

theorem LinesProjIndexLower.full : LinesProjIndexLower.Statement :=
  LinesProjIndexLower.proof LinesProjLattice.full LinesIdealLatticeFG.full LinesIsLattice.full LinesGenIndexMono.full LinesIdealStdIndex.full

theorem LinesLineDegree.full : LinesLineDegree.Statement :=
  LinesLineDegree.proof

theorem LinesQuotIndexLog.full : LinesQuotIndexLog.Statement :=
  LinesQuotIndexLog.proof LinesQuotIndexSplit.full LinesProjIndexLower.full LinesIdealIndexPos.full LinesProductFormula.full LinesCoordDet.full

theorem LinesQuotGramLog.full : LinesQuotGramLog.Statement :=
  LinesQuotGramLog.proof LinesGramDetChange.full LinesCoordDet.full LinesGramFischerBound.full LinesGramPosDef.full

theorem LinesQuotDegreeBound.full : LinesQuotDegreeBound.Statement :=
  LinesQuotDegreeBound.proof LinesExtendBasis.full LinesQuotIndexLog.full LinesQuotGramLog.full

theorem OrthogonalLines.full : OrthogonalLines.Statement :=
  OrthogonalLines.proof LinesQuotDegreeBound.full LinesLineDegree.full

end GroundTheory.Heights₂.Heights
end
