import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassMapEstimateOfPartial
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ExistsOnOfPosDef
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NfAllSmulReB
import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClsCrdEqGlob

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField

theorem exists_map_of_ratSpan (D : D7) {n : ℕ} {lam : D.what₂.Tau → DomWeight n}
    {p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hp : p ∈ RatSpan D lam) :
    ∃ F : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL, MvPolynomial.map D.what₂.embLL F = p := by
  have hle : RatSpan D lam ≤ (MvPolynomial.map (σ := D.what₂.Tau × Fin n × Fin n) D.what₂.embLL).range.toAddSubgroup := by
    unfold RatSpan
    refine (AddSubgroup.closure_le _).2 ?_
    rintro q ⟨r, f, -, rfl⟩
    refine RingHom.mem_range.2
      ⟨MvPolynomial.C r * Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)), ?_⟩
    have hi : D.what₂.embLL.comp (Int.castRingHom D.what₂.LL) = Int.castRingHom ℂ := RingHom.ext_int _ _
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
    congr 1
    unfold Formalism.L2.Forms.ten
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [MvPolynomial.map_rename, MvPolynomial.map_map, hi]
  obtain ⟨F, hF⟩ := RingHom.mem_range.1 (hle hp)
  exact ⟨F, hF⟩

def FramesAt : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (_ : FormsTiedSym D u Ch chOf)
    (s : D.what₂.LL →+* ℂ),
    (∃ o : Frames (gramC (gramN D D.R.m le_rfl) (embS D s)), o.IsON) ∧ ∃ o : Frames (gramC (gramP D) (embS D s)), o.IsON

def NormClsAt : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
    Formalism.L2.Rows.LowerMapTieS Tf → Formalism.L2.Ker.BeOnTie D u →
    ∀ (h : (D.fm u).PRat) (s : D.what₂.LL →+* ℂ) (x : Vl D u D.R.m)
      (Pc : (D.mem u).C.cls D.R.m → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL),
      (∀ c z, (D.fm u).emb D.R.m x c z = fnOf _ (shiftOf (lamT u D.R.m)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
        ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z)) →
    ∀ (Qc : (D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL),
      (∀ c, Tf.valP.eW ((D.fm u).ptEmb ((D.fm u).PtL h x)) c =
        fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Qc c))) →
    ∀ (o : Frames (gramC (gramN D D.R.m le_rfl) (embS D s))), o.IsON →
    ∀ (o' : Frames (gramC (gramP D) (embS D s))), o'.IsON →
    ∀ c, (∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
        (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (MvPolynomial.map s (Qc c))) (subP o'.1 (MvPolynomial.map s (Qc c)))).re ≤
      ptB D u * ((∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)) *
        (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) (subP o.1 (MvPolynomial.map s (Pc ((D.fm u).til c))))
          (subP o.1 (MvPolynomial.map s (Pc ((D.fm u).til c))))).re)

theorem ptB_nonneg (D : D7) (u : D.what₂.Word) : 0 ≤ ptB D u :=
  Finset.prod_nonneg fun _ _ => mul_nonneg (zpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)

theorem wt_re_eq (D : D7) (u : D.what₂.Word) (i : ℕ) (c : (D.mem u).C.cls i) :
    ((D.mem u).C.wt i c).re = ((Nat.card ((D.mem u).C.stab i c) : ℕ) : ℝ)⁻¹ := by
  unfold ColumnChain.wt
  rw [show (((Nat.card ((D.mem u).C.stab i c) : ℕ) : ℂ))⁻¹ = ((((Nat.card ((D.mem u).C.stab i c) : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    Complex.ofReal_re]

theorem sum_le_of_inj {α β : Type} [Fintype α] [Fintype β] (f : α → β) (hf : Function.Injective f) (a : α → ℝ) (b : β → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ y, 0 ≤ b y) (hab : ∀ x, a x ≤ B * b (f x)) : ∑ x, a x ≤ B * ∑ y, b y := by
  classical
  calc ∑ x, a x ≤ ∑ x, B * b (f x) := Finset.sum_le_sum fun x _ => hab x
    _ = B * ∑ y ∈ Finset.univ.image f, b y := by
        rw [Finset.sum_image (fun x _ y _ h => hf h), Finset.mul_sum]
    _ ≤ B * ∑ y, b y := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun y _ _ => hb y) hB

theorem norm_bound_of_classes_frames (h1 : ClassMapInjective) (h2 : StabiliserMapBijective) (hF : FramesAt) (hC : NormClsAt) : NormBoundAtInfinity := by
  intro D u Ch chOf Tf hL hB h v x
  obtain ⟨s, rfl⟩ : ∃ s, InfinitePlace.mk s = v := ⟨v.embedding, v.mk_embedding⟩

  have hx := ((Tf.val D.R.m le_rfl (Or.inr rfl)).rat ((D.fm u).emb D.R.m x)).1 ⟨x, rfl⟩
  choose P hP hPz using hx.2
  choose Pc hPc using fun c => exists_map_of_ratSpan D (hP c)
  have hrep : ∀ c z, (D.fm u).emb D.R.m x c z = fnOf _ (shiftOf (lamT u D.R.m)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
      ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z) := fun c z => by rw [hPc c]; exact hPz c z

  have hy := (Tf.valP.rat ((D.fm u).ptEmb ((D.fm u).PtL h x))).1 ⟨_, rfl⟩
  choose Q hQ hQz using hy.2
  choose Qc hQc using fun c => exists_map_of_ratSpan D (hQ c)
  have hrepP : ∀ c, Tf.valP.eW ((D.fm u).ptEmb ((D.fm u).PtL h x)) c =
      fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Qc c)) := fun c => by rw [hQc c]; exact hQz c
  obtain ⟨⟨o, ho⟩, ⟨o', ho'⟩⟩ := hF D u Ch chOf Tf s
  rw [Tf.normP s _ Qc hrepP o' ho', Tf.norm D.R.m le_rfl (Or.inr rfl) s x Pc hrep o ho]
  refine sum_le_of_inj _ (h1 D u Ch chOf Tf) _ _ _ (ptB_nonneg D u) (fun c => ?_) (fun c => ?_)
  · refine mul_nonneg (mul_nonneg ?_ (Finset.prod_nonneg fun τ _ => zpow_nonneg (norm_nonneg _) _))
      (Formalism.L2.Ker.ta_nfAll_nonneg ((D.fm u).lam D.R.m) _)
    rw [wt_re_eq]; positivity
  · have hcard : Nat.card ((D.fm u).stabilizer₂ c) = Nat.card ((D.mem u).C.stab D.R.m ((D.fm u).til c)) :=
      Nat.card_congr (Equiv.ofBijective _ (h2 D u Ch chOf Tf c))
    have hk := hC D u Ch chOf Tf hL hB h s x Pc hrep Qc hrepP o ho o' ho' c
    rw [wt_re_eq, ← hcard]
    have hw : 0 ≤ ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ := by positivity
    calc ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ * (∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
          (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (MvPolynomial.map s (Qc c))) (subP o'.1 (MvPolynomial.map s (Qc c)))).re
        = ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ * ((∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
          (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (MvPolynomial.map s (Qc c))) (subP o'.1 (MvPolynomial.map s (Qc c)))).re) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hk hw
      _ = _ := by ring

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix
open scoped ComplexOrder

variable {D : D7}

theorem sig_at (ι : D.host.E →+* ℂ) (x : D.host.E) : ι (sigD D x) = starRingEnd ℂ (ι x) :=
  D.sp.cm.cmUnram.2.1 ι x

theorem map_cT_at {m n : Type} (ι : D.host.E →+* ℂ) (M : Matrix m n D.host.E) :
    ((M.map (sigD D : D.host.E →+* D.host.E))ᵀ).map ι = (M.map ι)ᴴ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, RingHom.coe_coe]
  rw [sig_at]
  rfl

theorem gramN_posDef_at {Ch : ℕ → Type} {u : D.what₂.Word} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf)
    (ι : D.host.E →+* ℂ) : ((gramN D D.R.m le_rfl).map ι).PosDef := by
  obtain ⟨C, hC, -, -⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).de
  have hC' : ((C.1.map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) = gramN D D.R.m le_rfl := hC
  set A : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ := C.1.map ι with hA
  have hG : (gramN D D.R.m le_rfl).map ι = Aᴴ * A := by
    rw [← hC', Matrix.map_mul, map_cT_at, hA]
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have hCi : IsUnit C.1.det := (Matrix.isUnit_iff_isUnit_det _).mp C.isUnit
    have h1 : (C.1⁻¹ * C.1).map ι = 1 := by
      rw [Matrix.nonsing_inv_mul _ hCi, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := congrArg (fun v => ((C.1⁻¹).map ι) *ᵥ v) hxy
    simp only [Matrix.mulVec_mulVec, hA, ← Matrix.map_mul, h1, Matrix.one_mulVec] at h2
    exact h2
  rw [hG]
  exact Matrix.PosDef.conjTranspose_mul_self A hinj

theorem gramP_posDef_at {Ch : ℕ → Type} {u : D.what₂.Word} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf)
    (ι : D.host.E →+* ℂ) : ((gramP D).map ι).PosDef := by
  obtain ⟨C, hC, -, -⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).de
  have hC' : ((C.1.map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) = gramN D D.R.m le_rfl := hC
  obtain ⟨L, hL⟩ := iXm_leftInv D
  set A : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m - 1)) ℂ := (C.1 * iXm D).map ι with hA
  have hG : (gramP D).map ι = Aᴴ * A := by
    have e1 : ((iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (((C.1).map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) * iXm D =
        ((C.1 * iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (C.1 * iXm D) := by
      rw [Matrix.map_mul, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [gramP_eq, ← hC', e1, Matrix.map_mul, map_cT_at, hA]
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have hCi : IsUnit C.1.det := (Matrix.isUnit_iff_isUnit_det _).mp C.isUnit
    have h1 : ((L * C.1⁻¹) * (C.1 * iXm D)).map ι = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc C.1⁻¹, Matrix.nonsing_inv_mul _ hCi, Matrix.one_mul, hL,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := congrArg (fun v => ((L * C.1⁻¹).map ι) *ᵥ v) hxy
    simp only [Matrix.mulVec_mulVec, hA, ← Matrix.map_mul, h1, Matrix.one_mulVec] at h2
    exact h2
  rw [hG]
  exact Matrix.PosDef.conjTranspose_mul_self A hinj

theorem framesAt : FramesAt := by
  intro D u Ch chOf Tf s
  constructor
  · have h := fun τ => exists_on_of_posDef (gramC (gramN D D.R.m le_rfl) (embS D s) τ) (gramN_posDef_at Tf (embS D s τ))
    choose o ho1 ho2 using h
    exact ⟨⟨o, ho1⟩, fun τ => Or.inl (ho2 τ)⟩
  · have h := fun τ => exists_on_of_posDef (gramC (gramP D) (embS D s) τ) (gramP_posDef_at Tf (embS D s τ))
    choose o ho1 ho2 using h
    exact ⟨⟨o, ho1⟩, fun τ => Or.inl (ho2 τ)⟩

theorem norm_bound_of_classes (h1 : ClassMapInjective) (h2 : StabiliserMapBijective) (hC : NormClsAt) : NormBoundAtInfinity :=
  norm_bound_of_classes_frames h1 h2 framesAt hC

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

def BlockFockBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (n n' : ℕ) (V : ι → Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ))
    (F : ι → MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ) (c : ι → ℝ),
    (∀ τ, ∀ f ∈ V τ, (Formalism.REAL.fockF (F τ f) (F τ f)).re ≤ c τ ^ 2 * (Formalism.REAL.fockF f f).re) →
    ∀ P ∈ Submodule.span ℂ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℂ, (∀ τ, f τ ∈ V τ) ∧ p = Formalism.MainNotions.product_first_zeroth_parts.ten f},
      (Formalism.REAL.fockF (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P) (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P)).re ≤
        (∏ τ, c τ ^ 2) * (Formalism.REAL.fockF P P).re

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def eX {k : ℕ} (l : DomWeight k) : ℝ := (Formalism.REAL.fockF (extremal ℂ k l) (extremal ℂ k l)).re

theorem eX_pos {k : ℕ} (l : DomWeight k) : 0 < eX l := by
  have h := (Formalism.GradedWeylDivisibility.fockPos _ _ (Formalism.L2.Ker.lm_extremal_ne (K := ℂ) l)).1
  rw [Formalism.L2.Ker.nm_fockF_self (extremal ℂ k l), Complex.ofReal_re] at h
  exact h

theorem normFock_re {k : ℕ} (l : DomWeight k) (f : MvPolynomial (Fin k × Fin k) ℂ) :
    (normFock l f f).re = (Formalism.REAL.fockF f f).re / eX l := by
  unfold normFock eX
  rw [Formalism.L2.Ker.nm_fockF_self (extremal ℂ k l), Complex.div_ofReal_re, Complex.ofReal_re]

def cF (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  (D.fm u).beOn τ * Real.sqrt (eX ((D.fm u).sg τ) / eX ((D.fm u).lam D.R.m τ))

theorem cF_sq (τ : D.what₂.Tau) :
    cF D u τ ^ 2 = (D.fm u).beOn τ ^ 2 * (eX ((D.fm u).sg τ) / eX ((D.fm u).lam D.R.m τ)) := by
  unfold cF
  rw [mul_pow, Real.sq_sqrt (div_nonneg (eX_pos _).le (eX_pos _).le)]

theorem factor_le (Tf : FormsTiedSym D u Ch chOf) (hB : Formalism.L2.Ker.BeOnTie D u) (τ : D.what₂.Tau)
    (f : MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) (hf : f ∈ delSq ℂ _ ((D.fm u).lam D.R.m τ)) :
    (Formalism.REAL.fockF (Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f)
      (Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f)).re ≤ cF D u τ ^ 2 * (Formalism.REAL.fockF f f).re := by
  have hI := interlaceTr D u (sg_interlace Tf.valP) τ
  have hI' := (Formalism.L2.Ker.interlace_iff _ _ (Nm_succ D.R)).1 hI
  have hS := Formalism.L2.Ker.sameShiftTr D u τ hI
  have hf' : f ∈ nablaSq ℂ _ (lamTr D u τ) := by
    rw [Formalism.L2.Col.nablaSq_eq_delSq]; unfold lamTr; rw [delSq_wSh]; exact hf
  have h := Formalism.L2.Ker.nm_le _ _ _ hI' hS f hf'
  have hb : (D.fm u).beOn τ ^ 2 = ((Formalism.L2.Col.Br.cBr (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) : ℤ) : ℝ) ^ 2 *
      Formalism.L2.Col.Br.kapBr ℝ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) := by
    rw [beOn_closedS Tf hB τ]
    unfold Formalism.L2.Ker.beOnVal
    rw [mul_pow, sq_abs, Real.sq_sqrt (Formalism.L2.Ker.nm_kapR_pos _ _ _ hI' hS).le]
  have eS : eX (sgTr D u τ) = eX ((D.fm u).sg τ) := by unfold eX sgTr; rw [extremal_wSh]
  have eL : eX (lamTr D u τ) = eX ((D.fm u).lam D.R.m τ) := by unfold eX lamTr; rw [extremal_wSh]
  rw [normFock_re, normFock_re, eS, eL, ← hb] at h
  have hs := eX_pos ((D.fm u).sg τ)
  have hl := eX_pos ((D.fm u).lam D.R.m τ)
  rw [div_le_iff₀ hs] at h
  rw [cF_sq]
  calc _ ≤ (D.fm u).beOn τ ^ 2 * ((Formalism.REAL.fockF f f).re / eX ((D.fm u).lam D.R.m τ)) * eX ((D.fm u).sg τ) := h
    _ = _ := by field_simp

theorem nfAll_brTen_le (hT : BlockFockBound) (Tf : FormsTiedSym D u Ch chOf) (hB : Formalism.L2.Ker.BeOnTie D u)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) (hP : P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m)) :
    (Formalism.L2.Forms.nfAll (D.fm u).sg (Formalism.L2.Ker.brTen D u P) (Formalism.L2.Ker.brTen D u P)).re ≤
      (∏ τ, (D.fm u).beOn τ ^ 2) * (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) P P).re := by
  have key := hT D.what₂.Tau (D.R.N D.R.m) (D.R.N D.R.m - 1) (fun τ => delSq ℂ _ ((D.fm u).lam D.R.m τ))
    (fun τ => Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) (cF D u)
    (fun τ f hf => factor_le Tf hB τ f hf) P hP
  have eprod : ∀ {k : ℕ} (l : D.what₂.Tau → DomWeight k),
      ∏ τ, Formalism.REAL.fockF (extremal ℂ k (l τ)) (extremal ℂ k (l τ)) = ((∏ τ, eX (l τ) : ℝ) : ℂ) := by
    intro k l
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun τ _ => Formalism.L2.Ker.nm_fockF_self _
  unfold Formalism.L2.Forms.nfAll
  rw [eprod, eprod, Complex.div_ofReal_re, Complex.div_ofReal_re]
  have hs : 0 < ∏ τ, eX ((D.fm u).sg τ) := Finset.prod_pos fun τ _ => eX_pos _
  have hl : 0 < ∏ τ, eX ((D.fm u).lam D.R.m τ) := Finset.prod_pos fun τ _ => eX_pos _
  have hc : ∏ τ, cF D u τ ^ 2 =
      (∏ τ, (D.fm u).beOn τ ^ 2) * ((∏ τ, eX ((D.fm u).sg τ)) / ∏ τ, eX ((D.fm u).lam D.R.m τ)) := by
    rw [← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => cF_sq τ
  rw [hc] at key
  rw [div_le_iff₀ hs]
  calc (Formalism.REAL.fockF (Formalism.L2.Ker.brTen D u P) (Formalism.L2.Ker.brTen D u P)).re
      ≤ (∏ τ, (D.fm u).beOn τ ^ 2) * ((∏ τ, eX ((D.fm u).sg τ)) / ∏ τ, eX ((D.fm u).lam D.R.m τ)) *
          (Formalism.REAL.fockF P P).re := key
    _ = _ := by field_simp

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Matrix
open scoped ComplexOrder

section Fock

variable {σ : Type}

theorem tf_eq_sum (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ)) (hS : f.support ⊆ S) :
    Formalism.REAL.fockF f g = ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [notMem_support_iff.mp hm]
  simp

theorem tf_add_left (f f' g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (f + f') g = Formalism.REAL.fockF f g + Formalism.REAL.fockF f' g := by
  classical
  rw [tf_eq_sum (f + f') g (f.support ∪ f'.support) support_add,
    tf_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
    tf_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_add]
  ring

theorem tf_smul_left (c : ℂ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (c • f) g = c * Formalism.REAL.fockF f g := by
  rw [tf_eq_sum (c • f) g f.support support_smul, tf_eq_sum f g f.support le_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring

theorem tf_add_right (f g g' : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f (g + g') = Formalism.REAL.fockF f g + Formalism.REAL.fockF f g' := by
  unfold Formalism.REAL.fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_add, star_add]
  ring

theorem tf_smul_right (c : ℂ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f (c • g) = star c * Formalism.REAL.fockF f g := by
  unfold Formalism.REAL.fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul, star_mul']
  ring

def tfB : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) Formalism.REAL.fockF tf_add_left tf_smul_left tf_add_right tf_smul_right

theorem tfB_apply (f g : MvPolynomial σ ℂ) : tfB f g = Formalism.REAL.fockF f g := rfl

theorem tf_eq_fockS (f g : MvPolynomial σ ℂ) : Formalism.REAL.fockF f g = Formalism.L2.DIV.fockS g f := by
  classical
  rw [tf_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold Formalism.L2.DIV.mfact
  ring

theorem tf_star (f g : MvPolynomial σ ℂ) : star (Formalism.REAL.fockF f g) = Formalism.REAL.fockF g f := by
  rw [tf_eq_fockS g f]
  unfold Formalism.REAL.fockF Formalism.L2.DIV.fockS
  rw [star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold Formalism.L2.DIV.mfact
  simp only [star_mul', star_star, star_natCast]

theorem tf_quad {k : ℕ} (w : Fin k → MvPolynomial σ ℂ) (x : Fin k → ℂ) :
    star x ⬝ᵥ (Matrix.of fun i j => Formalism.REAL.fockF (w j) (w i)) *ᵥ x =
      Formalism.REAL.fockF (∑ j, x j • w j) (∑ i, x i • w i) := by
  rw [← tfB_apply]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ, tfB_apply, smul_eq_mul,
    dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [starRingEnd_apply]
  ring

theorem tf_herm {σ' : Type} {k : ℕ} (w : Fin k → MvPolynomial σ ℂ) (v : Fin k → MvPolynomial σ' ℂ) (r : ℝ) :
    (((r : ℂ) • Matrix.of fun i j => Formalism.REAL.fockF (w j) (w i)) - Matrix.of fun i j => Formalism.REAL.fockF (v j) (v i)).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, star_sub, star_mul',
    tf_star]
  rw [Complex.star_def, Complex.conj_ofReal]

theorem tf_gram_psd {k : ℕ} (w : Fin k → MvPolynomial σ ℂ) :
    (Matrix.of fun i j => Formalism.REAL.fockF (w j) (w i)).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j; simp only [conjTranspose_apply, Matrix.of_apply, tf_star]
  · rw [tf_quad, Formalism.L2.Ker.nm_fockF_self]
    exact Complex.zero_le_real.2 (Formalism.L2.Ker.nm_fockF_nonneg _)

end Fock

section Had

variable {ι : Type} [Fintype ι] {k : ℕ}

theorem tf_ones_psd : (Matrix.of fun (_ _ : Fin k) => (1 : ℂ)).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j; simp
  · have : star x ⬝ᵥ (Matrix.of fun (_ _ : Fin k) => (1 : ℂ)) *ᵥ x = star (∑ i, x i) * ∑ i, x i := by
      simp only [dotProduct, mulVec, Matrix.of_apply, one_mul, star_sum, Finset.sum_mul, Pi.star_apply]
    rw [this]
    exact star_mul_self_nonneg _

theorem tf_had_sub (A B : ι → Matrix (Fin k) (Fin k) ℂ) (hB : ∀ τ, (B τ).PosSemidef) (hAB : ∀ τ, (A τ - B τ).PosSemidef) :
    ((Matrix.of fun i j => ∏ τ, A τ i j) - Matrix.of fun i j => ∏ τ, B τ i j).PosSemidef := by
  classical
  have hA : ∀ τ, (A τ).PosSemidef := fun τ => by simpa using (hAB τ).add (hB τ)
  suffices h : ∀ s : Finset ι, ((Matrix.of fun i j => ∏ τ ∈ s, A τ i j) - Matrix.of fun i j => ∏ τ ∈ s, B τ i j).PosSemidef ∧
      (Matrix.of fun i j => ∏ τ ∈ s, A τ i j).PosSemidef from (h Finset.univ).1
  intro s
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, sub_self]
    exact ⟨PosSemidef.zero, tf_ones_psd⟩
  | insert t s ht ih =>
    have eA : (Matrix.of fun i j => ∏ τ ∈ insert t s, A τ i j) = A t ⊙ Matrix.of fun i j => ∏ τ ∈ s, A τ i j := by
      ext i j; simp [Finset.prod_insert ht, hadamard]
    have eB : (Matrix.of fun i j => ∏ τ ∈ insert t s, B τ i j) = B t ⊙ Matrix.of fun i j => ∏ τ ∈ s, B τ i j := by
      ext i j; simp [Finset.prod_insert ht, hadamard]
    have e : A t ⊙ (Matrix.of fun i j => ∏ τ ∈ s, A τ i j) - B t ⊙ (Matrix.of fun i j => ∏ τ ∈ s, B τ i j) =
        (A t - B t) ⊙ (Matrix.of fun i j => ∏ τ ∈ s, A τ i j) +
          B t ⊙ ((Matrix.of fun i j => ∏ τ ∈ s, A τ i j) - Matrix.of fun i j => ∏ τ ∈ s, B τ i j) := by
      ext i j; simp [hadamard]; ring
    refine ⟨?_, ?_⟩
    · rw [eA, eB, e]
      exact ((hAB t).hadamard ih.2).add ((hB t).hadamard ih.1)
    · rw [eA]; exact (hA t).hadamard ih.2

end Had

theorem tf_ten {ι : Type} [Fintype ι] {n : ℕ} (f g : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.REAL.fockF (Formalism.MainNotions.product_first_zeroth_parts.ten f) (Formalism.MainNotions.product_first_zeroth_parts.ten g) = ∏ τ, Formalism.REAL.fockF (f τ) (g τ) := by
  rw [tf_eq_fockS]
  have h := Formalism.L2.DIV.fockSymTensor_holds ℂ ι n g f
  refine (h.trans ?_)
  exact Finset.prod_congr rfl fun τ _ => (tf_eq_fockS _ _).symm

theorem blkFockLe : BlockFockBound := by
  intro ι _ n n' V F c hF P hP
  classical
  obtain ⟨k, a, p, hsum⟩ := Submodule.mem_span_set'.1 hP
  choose f hfV hfeq using fun i => (p i).2
  have hs : ∀ (r : ℂ) (M : Matrix (Fin k) (Fin k) ℂ) (v : Fin k → ℂ), (r • M) *ᵥ v = r • (M *ᵥ v) := by
    intro r M v; ext i
    simp only [mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hd : ∀ (r : ℂ) (v w : Fin k → ℂ), v ⬝ᵥ (r • w) = r * (v ⬝ᵥ w) := by
    intro r v w
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hP' : P = ∑ i, a i • Formalism.MainNotions.product_first_zeroth_parts.ten (f i) := by
    rw [← hsum]; exact Finset.sum_congr rfl fun i _ => by rw [hfeq i]
  have hblk : Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P = ∑ i, a i • Formalism.MainNotions.product_first_zeroth_parts.ten (fun τ => F τ (f i τ)) := by
    rw [hP', map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, Formalism.MainNotions.product_first_zeroth_parts.blk_ten]
  set G : ι → Matrix (Fin k) (Fin k) ℂ := fun τ => Matrix.of fun i j => Formalism.REAL.fockF (f j τ) (f i τ) with hG
  set H : ι → Matrix (Fin k) (Fin k) ℂ := fun τ => Matrix.of fun i j => Formalism.REAL.fockF (F τ (f j τ)) (F τ (f i τ)) with hH
  have qP : Formalism.REAL.fockF P P = star a ⬝ᵥ (Matrix.of fun i j => ∏ τ, G τ i j) *ᵥ a := by
    have := tf_quad (fun i => Formalism.MainNotions.product_first_zeroth_parts.ten (f i)) a
    simp only [tf_ten] at this
    rw [hP', ← this]
    rfl
  have qB : Formalism.REAL.fockF (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P) (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P) =
      star a ⬝ᵥ (Matrix.of fun i j => ∏ τ, H τ i j) *ᵥ a := by
    have := tf_quad (fun i => Formalism.MainNotions.product_first_zeroth_parts.ten (fun τ => F τ (f i τ))) a
    simp only [tf_ten] at this
    rw [hblk, ← this]
    rfl
  have hBpsd : ∀ τ, (H τ).PosSemidef := fun τ => tf_gram_psd (fun i => F τ (f i τ))
  have hABpsd : ∀ τ, ((((c τ ^ 2 : ℝ) : ℂ) • G τ) - H τ).PosSemidef := by
    intro τ
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨tf_herm (fun i => f i τ) (fun i => F τ (f i τ)) (c τ ^ 2), fun x => ?_⟩
    rw [sub_mulVec, dotProduct_sub, hs, hd, tf_quad, tf_quad]
    have hlin : ∑ i, x i • F τ (f i τ) = F τ (∑ i, x i • f i τ) := by rw [map_sum]; simp [map_smul]
    have hmem : ∑ i, x i • f i τ ∈ V τ := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hfV i τ)
    rw [hlin, Formalism.L2.Ker.nm_fockF_self (∑ i, x i • f i τ), Formalism.L2.Ker.nm_fockF_self (F τ (∑ i, x i • f i τ)),
      ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    exact Complex.zero_le_real.2 (sub_nonneg.2 (hF τ _ hmem))
  have key := (tf_had_sub (fun τ => ((c τ ^ 2 : ℝ) : ℂ) • G τ) H hBpsd hABpsd).dotProduct_mulVec_nonneg a
  have eA : (Matrix.of fun i j => ∏ τ, (((c τ ^ 2 : ℝ) : ℂ) • G τ) i j) =
      (((∏ τ, c τ ^ 2 : ℝ) : ℂ)) • Matrix.of fun i j => ∏ τ, G τ i j := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Complex.ofReal_prod]
  rw [eA, sub_mulVec, dotProduct_sub, hs, hd, ← qP, ← qB,
    Formalism.L2.Ker.nm_fockF_self P, Formalism.L2.Ker.nm_fockF_self (Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => F τ) P), ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, Complex.zero_le_real] at key
  exact sub_nonneg.1 key

theorem nfAll_brTen_le' {D : Formalism.BasicNotions.D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (Tf : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) (hB : Formalism.L2.Ker.BeOnTie D u)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) (hP : P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m)) :
    (Formalism.L2.Forms.nfAll (D.fm u).sg (Formalism.L2.Ker.brTen D u P) (Formalism.L2.Ker.brTen D u P)).re ≤
      (∏ τ, (D.fm u).beOn τ ^ 2) * (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) P P).re :=
  nfAll_brTen_le blkFockLe Tf hB P hP

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms

section Gen

variable {ι : Type} [Fintype ι] {n : ℕ}

def rowSubK {R : Type} [CommRing R] (o : ι → Matrix (Fin n) (Fin n) R) :
    MvPolynomial (ι × Fin n × Fin n) R →ₐ[R] MvPolynomial (ι × Fin n × Fin n) R :=
  aeval fun x => ∑ a', C (o x.1 x.2.1 a') * X (x.1, a', x.2.2)

theorem rowSubK_eq_subP (o : ι → Matrix (Fin n) (Fin n) ℂ) : rowSubK o = subP o := rfl

theorem subP_eq_blkRow (o : ι → Matrix (Fin n) (Fin n) ℂ) : subP o = blkRow o := rfl

theorem map_rowSubK {R S : Type} [CommRing R] [CommRing S] (j : R →+* S) (o : ι → Matrix (Fin n) (Fin n) R)
    (P : MvPolynomial (ι × Fin n × Fin n) R) :
    map j (rowSubK o P) = rowSubK (fun τ => (o τ).map j) (map j P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowSubK, MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    simp [rowSubK, map_sum, Matrix.map_apply]

theorem blkRow_comp (K L : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    blkRow K (blkRow L P) = blkRow (fun τ => L τ * K τ) P := by
  have e : (blkRow K).comp (blkRow L) = blkRow (fun τ => L τ * K τ) := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply]
    simp only [blkRow, aeval_X, map_sum, map_mul, aeval_C, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← mul_assoc,
      MvPolynomial.algebraMap_eq]
    rw [Finset.sum_comm]
  rw [← e, AlgHom.comp_apply]

theorem norm_one_of_pow {K : Type} [Field K] (j s : K →+* ℂ) (a : K) (k : ℕ) (hk : 0 < k) (h : (j a) ^ k = 1) :
    ‖s a‖ = 1 := by
  have h1 : a ^ k = 1 := j.injective (by rw [map_pow, h, map_one])
  have h2 : (s a) ^ k = 1 := by rw [← map_pow, h1, map_one]
  have h3 := congrArg norm h2
  rw [norm_pow, norm_one] at h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 h3

end Gen

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix

section BC

variable {K K' : Type} [Field K] [Field K'] [CharZero K] [CharZero K'] (j : K →+* K') {ι : Type} [Fintype ι] {N n : ℕ}

theorem map_brStdP (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) (F : Formalism.L2.DIV.Pol K ι N) :
    map j (Formalism.L2.Col.Br.brStdP hN lam sg F : Formalism.L2.DIV.Pol K ι n) =
      (Formalism.L2.Col.Br.brStdP hN lam sg (map j F) : Formalism.L2.DIV.Pol K' ι n) := by
  simp only [Formalism.L2.Col.Br.brStdP, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul]
  rw [MvPolynomial.smul_eq_C_mul, map_mul, map_C, Formalism.L2.Ker.lb_map_projVV, Formalism.L2.Ker.lb_map_coefLast,
    Formalism.L2.Ker.lb_map_brConst, ← MvPolynomial.smul_eq_C_mul]

end BC

section Rec

variable {D : D7} {u : D.what₂.Word}

def brTenL (D : D7) (u : D.what₂.Word) (F : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL) :
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL :=
  (Formalism.L2.Col.Br.brStdP (Nm_succ D.R).symm (lamTr D u) (sgTr D u) F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (D.R.N D.R.m - 1))

theorem map_brTenL (j : D.what₂.LL →+* ℂ) (F : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL) :
    map j (brTenL D u F) = Formalism.L2.Ker.brTen D u (map j F) := by
  unfold brTenL Formalism.L2.Ker.brTen
  rw [map_brStdP, Formalism.L2.Ker.blk_brOne]

end Rec

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix

section Indep

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem blockAct_eq_blkRow (U : ι → Matrix (Fin n) (Fin n) ℂ) : Formalism.GradedWeylDivisibility.blockAct ℂ U = blkRow U := rfl

theorem isUnit_det_of_on (G o : Matrix (Fin n) (Fin n) ℂ) (h : oᴴ * G * o = 1) : IsUnit o.det := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h1
  have h2 : o.det * (oᴴ.det * G.det) = 1 := by rw [← h1]; ring
  exact ⟨Units.mkOfMulEqOne _ _ h2, rfl⟩

theorem unitary_of_two_on (G o1 o2 : Matrix (Fin n) (Fin n) ℂ) (h1 : o1ᴴ * G * o1 = 1) (h2 : o2ᴴ * G * o2 = 1) :
    (o1⁻¹ * o2) * (o1⁻¹ * o2)ᴴ = 1 ∧ ‖(o1⁻¹ * o2).det‖ = 1 ∧ o2 = o1 * (o1⁻¹ * o2) := by
  have hu1 := isUnit_det_of_on _ _ h1
  have hG : G = (o1ᴴ)⁻¹ * o1⁻¹ := Formalism.L2.Col.eq_of_frame _ _ h1
  have hUU : (o1⁻¹ * o2)ᴴ * (o1⁻¹ * o2) = 1 := by
    have e : (o1⁻¹ * o2)ᴴ * (o1⁻¹ * o2) = o2ᴴ * ((o1ᴴ)⁻¹ * o1⁻¹) * o2 := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
      simp only [Matrix.mul_assoc]
    rw [e, ← hG, h2]
  refine ⟨mul_eq_one_comm.1 hUU, ?_, ?_⟩
  · have h := congrArg Matrix.det hUU
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    have h' : ‖(o1⁻¹ * o2).det‖ ^ 2 = 1 := by
      have := congrArg (fun z : ℂ => ‖z‖) h
      simp only [norm_mul, norm_star, norm_one] at this
      rw [sq]; exact this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h'
  · rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.one_mul]

theorem term_frame_indep (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) ℂ) (k : ι → ℤ)
    (o1 o2 : ι → Matrix (Fin n) (Fin n) ℂ) (h1 : ∀ τ, (o1 τ)ᴴ * G τ * o1 τ = 1) (h2 : ∀ τ, (o2 τ)ᴴ * G τ * o2 τ = 1)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    (∏ τ, ‖(o1 τ).det‖ ^ (2 * k τ)) * (Formalism.L2.Forms.nfAll lam (subP o1 P) (subP o1 P)).re =
      (∏ τ, ‖(o2 τ).det‖ ^ (2 * k τ)) * (Formalism.L2.Forms.nfAll lam (subP o2 P) (subP o2 P)).re := by
  have hU := fun τ => unitary_of_two_on (G τ) (o1 τ) (o2 τ) (h1 τ) (h2 τ)
  have hc : blkRow (fun τ => (o1 τ)⁻¹ * o2 τ) (blkRow o1 P) = blkRow o2 P := by
    rw [blkRow_comp]
    have e : (fun τ => o1 τ * ((o1 τ)⁻¹ * o2 τ)) = o2 := funext fun τ => ((hU τ).2.2).symm
    rw [e]
  have hsub : subP o2 P = blkRow (fun τ => (o1 τ)⁻¹ * o2 τ) (subP o1 P) := hc.symm
  have hdet : ∀ τ, ‖(o2 τ).det‖ = ‖(o1 τ).det‖ := fun τ => by
    have e := congrArg Matrix.det (hU τ).2.2
    rw [Matrix.det_mul] at e
    rw [e, norm_mul, (hU τ).2.1, mul_one]
  have hn : Formalism.L2.Forms.nfAll lam (subP o2 P) (subP o2 P) = Formalism.L2.Forms.nfAll lam (subP o1 P) (subP o1 P) := by
    rw [hsub, ← blockAct_eq_blkRow]
    exact Formalism.L2.Col.nfAll_blockAct lam _ (fun τ => (hU τ).1) _ _
  rw [hn]
  congr 1
  exact Finset.prod_congr rfl (fun τ _ => by rw [hdet τ])

end Indep

section At

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem frame_on_at (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (ι : D.host.E →+* ℂ)
    (o' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) (ho : o'ᴴ * (gramP D).map ι * o' = 1) :
    (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E).map ι *
        (bZ u Tf.til.z0).map ι * dOT u o')ᴴ * (gramN D D.R.m le_rfl).map ι *
      (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E).map ι *
        (bZ u Tf.til.z0).map ι * dOT u o') = 1 := by
  have hga : (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E).map ι)ᴴ *
      (gramN D D.R.m le_rfl).map ι * ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E).map ι =
      (gramN D D.R.m le_rfl).map ι := by
    have h := ((Tf.til.ga c)⁻¹).2
    rw [InvMemClass.coe_inv] at h
    have h' : (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E).map
        (sigD D : D.host.E →+* D.host.E))ᵀ * gramN D D.R.m le_rfl *
        ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) = gramN D D.R.m le_rfl := h
    have h2 := congrArg (fun X => X.map ι) h'
    simp only [Matrix.map_mul] at h2
    rw [map_cT_at] at h2
    exact h2
  have hbZ : ((bZ u Tf.til.z0).map ι)ᴴ * (gramN D D.R.m le_rfl).map ι * (bZ u Tf.til.z0).map ι =
      Matrix.reindex (eN D) (eN D) (Matrix.fromBlocks ((gramP D).map ι) 0 0
        (Matrix.of fun _ _ => ((D.mem u).A.T : ℂ)⁻¹)) := by
    have h := gram_bZ (u := u) Tf.til.z0 Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    have h2 := congrArg (fun X => X.map ι) h
    simp only [Matrix.map_mul] at h2
    rw [map_cT_at] at h2
    rw [h2, Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
    congr 2
    ext i j
    simp [map_inv₀, map_natCast]
  have e : ∀ (X Y Z G : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ),
      (X * Y * Z)ᴴ * G * (X * Y * Z) = Zᴴ * (Yᴴ * (Xᴴ * G * X) * Y) * Z := by
    intro X Y Z G
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e, hga, hbZ, dOT_on _ _ ho]

end At

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix Formalism.UG

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}


theorem brOne_gFull (Tf : FormsTiedSym D u Ch chOf) (τ : D.what₂.Tau) (g : GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (f : MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) :
    Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) (sqAct ℂ _ (lamTr D u τ) (gFull D u g) f) =
      (((sqrtT D u) ^ ((D.fm u).deg τ) : ℂˣ) : ℂ) •
        sqAct ℂ _ (sgTr D u τ) g (Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f) := by
  have hI0 := interlaceTr D u (sg_interlace Tf.valP) τ
  have hS := Formalism.L2.Ker.sameShiftTr D u τ hI0
  have hI := (Formalism.L2.Ker.interlace_iff _ _ (Nm_succ D.R)).1 hI0
  unfold gFull
  rw [(factSqActMul ℂ _ _ _ _ f).1, Formalism.L2.Ker.brOne_sqAct _ _ _ hS g _, Formalism.L2.Ker.brOne_last _ _ _ hI _ f, deg_eq_degZ]
  unfold sqAct
  rw [map_smul, smul_comm]

theorem transpose_gFull_eq_dOT_of_eq_transpose (o' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) (g : GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (hg : (g : Matrix _ _ ℂ) = o'ᵀ) : ((gFull D u g : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix _ _ ℂ)ᵀ = dOT u o' := by
  have hl : ((Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ (D.R.N D.R.m) (sqrtT D u) : GL _ ℂ) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ)ᵀ =
      Matrix.reindex (eN D) (eN D) (Matrix.fromBlocks 1 0 0 (Matrix.of fun _ _ => ((sqrtT D u : ℂˣ) : ℂ))) := by
    rw [← lastGL_eq]
    show (Matrix.diagonal _)ᵀ = Matrix.diagonal _
    exact Matrix.diagonal_transpose _
  have he : ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) g : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ)ᵀ =
      Matrix.reindex (eN D) (eN D) (Matrix.fromBlocks o' 0 0 1) := by
    rw [embGL_val, Matrix.transpose_reindex, Matrix.fromBlocks_transpose, hg, Matrix.transpose_transpose,
      Matrix.transpose_zero, Matrix.transpose_zero, Matrix.transpose_one]
  unfold gFull dOT
  rw [Units.val_mul, Matrix.transpose_mul, hl, he, reindex_mulB, Matrix.fromBlocks_multiply]
  congr 1
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]

theorem det_dOT (o' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) :
    (dOT u o').det = o'.det * ((sqrtT D u : ℂˣ) : ℂ) := by
  unfold dOT
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  congr 1
  rw [Matrix.det_unique]
  rfl

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem brTen_blk_gFull (Tf : FormsTiedSym D u Ch chOf) (g : D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) :
    Formalism.L2.Ker.brTen D u (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (g τ))) Q) =
      (∏ τ, (((sqrtT D u) ^ ((D.fm u).deg τ) : ℂˣ) : ℂ)) •
        blk (fun τ => sqAct ℂ _ (sgTr D u τ) (g τ)) (Formalism.L2.Ker.brTen D u Q) := by
  have e1 : (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (g τ))) =
      fun τ => ⇑(Formalism.L2.Ker.ta_sqActL (lamTr D u τ) (gFull D u (g τ))) :=
    funext fun τ => (Formalism.L2.Ker.ta_sqActL_coe _ _).symm
  have e2 : (fun τ => sqAct ℂ _ (sgTr D u τ) (g τ)) = fun τ => ⇑(Formalism.L2.Ker.ta_sqActL (sgTr D u τ) (g τ)) :=
    funext fun τ => (Formalism.L2.Ker.ta_sqActL_coe _ _).symm
  unfold Formalism.L2.Ker.brTen
  rw [e1, e2, Formalism.L2.Ker.ta_blk_comp, Formalism.L2.Ker.ta_blk_comp]
  have e3 : (fun τ => ⇑(Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) ∘ₗ
      Formalism.L2.Ker.ta_sqActL (lamTr D u τ) (gFull D u (g τ)))) =
      fun τ => ⇑((((sqrtT D u) ^ ((D.fm u).deg τ) : ℂˣ) : ℂ) • (Formalism.L2.Ker.ta_sqActL (sgTr D u τ) (g τ) ∘ₗ
        Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ))) := by
    funext τ f
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Formalism.L2.Ker.ta_sqActL_coe]
    exact brOne_gFull Tf τ (g τ) f
  rw [e3, Formalism.L2.Ker.blk_smul]
  rfl

theorem blkRow_mem_CSpan {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ} (m : ι → DomWeight k)
    (M : ι → Matrix (Fin k) (Fin k) ℂ) (hM : ∀ τ, IsUnit (M τ).det) (p : MvPolynomial (ι × Fin k × Fin k) ℂ)
    (hp : p ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan m) : blkRow M p ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan m := by
  have hT : ∀ τ, IsUnit ((M τ)ᵀ).det := fun τ => by rw [Matrix.det_transpose]; exact hM τ
  let g : ι → GL (Fin k) ℂ := fun τ => ⟨(M τ)ᵀ, ((M τ)ᵀ)⁻¹, Matrix.mul_nonsing_inv _ (hT τ), Matrix.nonsing_inv_mul _ (hT τ)⟩
  have h := Formalism.L2.Ker.lc_blk_sqAct_mem m g p hp
  rw [blk_sqAct_eq] at h
  have hgT : (fun τ => ((g τ : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ)ᵀ) = M := funext fun τ => Matrix.transpose_transpose _
  rw [hgT] at h
  have hc : (∏ τ, detPow ℂ k (g τ) (m τ).detShift) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => Units.ne_zero _
  have h2 := Submodule.smul_mem _ (∏ τ, detPow ℂ k (g τ) (m τ).detShift)⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

theorem map_mem_CSpan_of_rat {n : ℕ} (lam : D.what₂.Tau → DomWeight n)
    (F : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL) (hF : map D.what₂.embLL F ∈ RatSpan D lam)
    (s : D.what₂.LL →+* ℂ) : map s F ∈ Formalism.L2.Forms.CSpan lam := by
  have hinj : Function.Injective (map (σ := D.what₂.Tau × Fin n × Fin n) D.what₂.embLL) :=
    MvPolynomial.map_injective _ D.what₂.embLL.injective
  have hten : ∀ (j : D.what₂.LL →+* ℂ) (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ),
      map j (Formalism.L2.Forms.ten (fun τ => map (Int.castRingHom D.what₂.LL) (f τ))) =
        Formalism.L2.Forms.ten (fun τ => map (Int.castRingHom ℂ) (f τ)) := by
    intro j f
    have hi : j.comp (Int.castRingHom D.what₂.LL) = Int.castRingHom ℂ := RingHom.ext_int _ _
    unfold Formalism.L2.Forms.ten
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [MvPolynomial.map_rename, MvPolynomial.map_map, hi]
  have key : ∀ p ∈ RatSpan D lam, ∀ F : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL,
      map D.what₂.embLL F = p → map s F ∈ Formalism.L2.Forms.CSpan lam := by
    intro p hp
    induction hp using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨r, f, hf, rfl⟩ := hx
      intro F hF
      have hFe : F = r • Formalism.L2.Forms.ten (fun τ => map (Int.castRingHom D.what₂.LL) (f τ)) := by
        apply hinj
        rw [hF, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, map_C, hten]
      rw [hFe, MvPolynomial.smul_eq_C_mul, map_mul, map_C, hten, ← MvPolynomial.smul_eq_C_mul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ), fun τ => ?_, rfl⟩)
      exact Formalism.L2.G.Model.sw_weyl_map (Int.castRingHom ℂ) le_rfl _ (f τ) (hf τ)
    | zero =>
      intro F hF
      have : F = 0 := hinj (by rw [hF, map_zero])
      rw [this, map_zero]; exact Submodule.zero_mem _
    | add x y hx' hy' hx hy =>
      intro F hF
      obtain ⟨Fx, hFx⟩ := exists_map_of_ratSpan D hx'
      obtain ⟨Fy, hFy⟩ := exists_map_of_ratSpan D hy'
      have : F = Fx + Fy := hinj (by rw [map_add, hFx, hFy, hF])
      rw [this, map_add]
      exact Submodule.add_mem _ (hx Fx hFx) (hy Fy hFy)
    | neg x hx' hx =>
      intro F hF
      obtain ⟨Fx, hFx⟩ := exists_map_of_ratSpan D hx'
      have : F = -Fx := hinj (by rw [map_neg, hFx, hF])
      rw [this, map_neg]
      exact Submodule.neg_mem _ (hx Fx hFx)
  exact key _ hF F rfl

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix

section Gen

theorem norm_detPow_sq {n : ℕ} (g : GL (Fin n) ℂ) (e : ℤ) :
    ‖detPow ℂ n g e‖ ^ 2 = ‖(g : Matrix (Fin n) (Fin n) ℂ).det‖ ^ (2 * e) := by
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, norm_zpow, ← zpow_natCast, ← _root_.zpow_mul,
    mul_comm e]
  norm_num

theorem desc_scalar {K σ : Type} [Field K] (j : K →+* ℂ) (Q F : MvPolynomial σ K) (χ : ℂ) (k : ℕ) (hk : 0 < k)
    (hχ : χ ^ k = 1) (h : map j Q = χ⁻¹ • map j F) : ∃ a : K, Q = a • F ∧ ∀ s : K →+* ℂ, ‖s a‖ ≤ 1 := by
  have hinj : Function.Injective (map (σ := σ) j) := MvPolynomial.map_injective _ j.injective
  by_cases hF : F = 0
  · refine ⟨0, ?_, fun s => by simp⟩
    apply hinj
    rw [h, hF]
    simp
  · obtain ⟨m, hm⟩ : ∃ m, F.coeff m ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hF (MvPolynomial.ext _ _ fun m => by rw [hc m, coeff_zero])
    have hc : j (Q.coeff m) = χ⁻¹ * j (F.coeff m) := by
      have := congrArg (coeff m) h
      rwa [coeff_map, coeff_smul, coeff_map, smul_eq_mul] at this
    have hjm : j (F.coeff m) ≠ 0 := (map_ne_zero j).2 hm
    have ha : j (Q.coeff m / F.coeff m) = χ⁻¹ := by
      rw [map_div₀, hc, mul_div_assoc, div_self hjm, mul_one]
    refine ⟨Q.coeff m / F.coeff m, ?_, fun s => ?_⟩
    · apply hinj
      rw [h, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul F (Q.coeff m / F.coeff m), map_mul, map_C, ha]
    · have := norm_one_of_pow j s _ k hk (by rw [ha, inv_pow, hχ, inv_one])
      rw [this]

end Gen

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem normal_form_agree {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (p : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    Formalism.MainNotions.product_first_zeroth_parts.nfAll lam p p = Formalism.L2.Forms.nfAll lam p p := rfl

theorem norm_sqrtT_sq (d : ℤ) : ‖(((sqrtT D u) ^ d : ℂˣ) : ℂ)‖ ^ 2 = ((D.mem u).A.T : ℝ) ^ d := by
  have hT : (0 : ℝ) ≤ ((D.mem u).A.T : ℝ) := Nat.cast_nonneg _
  rw [Units.val_zpow_eq_zpow_val, norm_zpow]
  have h1 : ‖((sqrtT D u : ℂˣ) : ℂ)‖ = Real.sqrt ((D.mem u).A.T : ℝ) := by
    simp only [sqrtT, Units.val_mk0, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [h1, ← zpow_natCast, ← _root_.zpow_mul, mul_comm d, _root_.zpow_mul, zpow_natCast, Real.sq_sqrt hT]

theorem chain_at (Tf : FormsTiedSym D u Ch chOf) (hBe : Formalism.L2.Ker.BeOnTie D u)
    (o' : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) (ho' : ∀ τ, IsUnit (o' τ).det)
    (Y : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)
    (hY : Y ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m)) :
    (∏ τ, ‖(o' τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
        (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o' (Formalism.L2.Ker.brTen D u Y)) (subP o' (Formalism.L2.Ker.brTen D u Y))).re ≤
      ptB D u * ((∏ τ, ‖(dOT u (o' τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)) *
        (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) (blkRow (fun τ => dOT u (o' τ)) Y)
          (blkRow (fun τ => dOT u (o' τ)) Y)).re) := by
  classical
  have hT : ∀ τ, IsUnit ((o' τ)ᵀ).det := fun τ => by rw [Matrix.det_transpose]; exact ho' τ
  let g : D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ := fun τ =>
    ⟨(o' τ)ᵀ, ((o' τ)ᵀ)⁻¹, Matrix.mul_nonsing_inv _ (hT τ), Matrix.nonsing_inv_mul _ (hT τ)⟩
  have hg : ∀ τ, ((g τ : GL _ ℂ) : Matrix _ _ ℂ) = (o' τ)ᵀ := fun τ => rfl
  have hL1 : blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (g τ))) Y =
      (∏ τ, detPow ℂ _ (gFull D u (g τ)) (lamTr D u τ).detShift) • blkRow (fun τ => dOT u (o' τ)) Y := by
    rw [blk_sqAct_eq]
    have e : (fun τ => ((gFull D u (g τ) : GL _ ℂ) : Matrix _ _ ℂ)ᵀ) = fun τ => dOT u (o' τ) :=
      funext fun τ => transpose_gFull_eq_dOT_of_eq_transpose (o' τ) (g τ) (hg τ)
    rw [e]
  have hR1 : blk (fun τ => sqAct ℂ _ (sgTr D u τ) (g τ)) (Formalism.L2.Ker.brTen D u Y) =
      (∏ τ, detPow ℂ _ (g τ) (sgTr D u τ).detShift) • subP o' (Formalism.L2.Ker.brTen D u Y) := by
    rw [blk_sqAct_eq]
    have e : (fun τ => ((g τ : GL _ ℂ) : Matrix _ _ ℂ)ᵀ) = o' := funext fun τ => by rw [hg, Matrix.transpose_transpose]
    rw [e]
    rfl
  have key := brTen_blk_gFull Tf g Y
  rw [hL1, hR1, map_smul, smul_smul] at key
  have hn := congrArg (fun p => (Formalism.L2.Forms.nfAll (D.fm u).sg p p).re) key
  simp only [nfAll_smul_reB, normal_form_agree] at hn
  have hdO : ∀ τ, IsUnit (dOT u (o' τ)).det := fun τ => by
    rw [det_dOT]
    exact (ho' τ).mul (Units.isUnit _)
  have hZ := blkRow_mem_CSpan ((D.fm u).lam D.R.m) (fun τ => dOT u (o' τ)) hdO Y hY
  have hle := nfAll_brTen_le' Tf hBe _ hZ

  have hshL : ∀ τ, (lamTr D u τ).detShift = shiftOf (lamT u D.R.m) τ := fun τ => by rw [shift_lamTr]
  have hshS : ∀ τ, (sgTr D u τ).detShift = shiftOf (sgT u) τ := fun τ => by
    have hI0 := interlaceTr D u (sg_interlace Tf.valP) τ
    have hS : (sgTr D u τ).detShift = (lamTr D u τ).detShift := Formalism.L2.Ker.sameShiftTr D u τ hI0
    rw [hS, hshL, shift_lamT_sgTS Tf τ]
  have hk1 : ‖∏ τ, detPow ℂ _ (gFull D u (g τ)) (lamTr D u τ).detShift‖ ^ 2 =
      ∏ τ, ‖(dOT u (o' τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ) := by
    rw [norm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [norm_detPow_sq, hshL, ← transpose_gFull_eq_dOT_of_eq_transpose (o' τ) (g τ) (hg τ), Matrix.det_transpose]
  have hk2 : ‖∏ τ, detPow ℂ _ (g τ) (sgTr D u τ).detShift‖ ^ 2 = ∏ τ, ‖(o' τ).det‖ ^ (2 * shiftOf (sgT u) τ) := by
    rw [norm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [norm_detPow_sq, hshS, hg, Matrix.det_transpose]
  have hcT : ‖∏ τ, (((sqrtT D u) ^ ((D.fm u).deg τ) : ℂˣ) : ℂ)‖ ^ 2 = ∏ τ, ((D.mem u).A.T : ℝ) ^ ((D.fm u).deg τ) := by
    rw [norm_prod, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun τ _ => norm_sqrtT_sq _
  have hTpos : (0 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hcpos : 0 < ∏ τ, ((D.mem u).A.T : ℝ) ^ ((D.fm u).deg τ) := Finset.prod_pos fun τ _ => zpow_pos hTpos _
  have hptB : ptB D u * ∏ τ, ((D.mem u).A.T : ℝ) ^ ((D.fm u).deg τ) = ∏ τ, (D.fm u).beOn τ ^ 2 := by
    unfold ptB
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [_root_.zpow_neg]
    field_simp
  rw [norm_mul, mul_pow, hk1, hk2, hcT] at hn
  set nW := (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o' (Formalism.L2.Ker.brTen D u Y)) (subP o' (Formalism.L2.Ker.brTen D u Y))).re
  set nBZ := (Formalism.L2.Forms.nfAll (D.fm u).sg (Formalism.L2.Ker.brTen D u (blkRow (fun τ => dOT u (o' τ)) Y))
    (Formalism.L2.Ker.brTen D u (blkRow (fun τ => dOT u (o' τ)) Y))).re
  set nZ := (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) (blkRow (fun τ => dOT u (o' τ)) Y) (blkRow (fun τ => dOT u (o' τ)) Y)).re
  set K1 := ∏ τ, ‖(dOT u (o' τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)
  set K2 := ∏ τ, ‖(o' τ).det‖ ^ (2 * shiftOf (sgT u) τ)
  set CT := ∏ τ, ((D.mem u).A.T : ℝ) ^ ((D.fm u).deg τ)
  set B := ∏ τ, (D.fm u).beOn τ ^ 2
  have hK1 : 0 ≤ K1 := Finset.prod_nonneg fun τ _ => zpow_nonneg (norm_nonneg _) _
  calc K2 * nW = (CT * K2 * nW) / CT := by field_simp
    _ = K1 * nBZ / CT := by rw [← hn]
    _ ≤ K1 * (B * nZ) / CT := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle hK1) hcpos.le
    _ = ptB D u * (K1 * nZ) := by rw [← hptB]; field_simp

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix NumberField

def ChiTors : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf)
    (c : (D.fm u).clsP), ∃ k : ℕ, 0 < k ∧
      ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c) : ℂˣ) : ℂ)) ^ k = 1

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def tauLE (D : D7) (τ : D.what₂.Tau) : D.host.E →+* D.what₂.LL :=
  D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)

def AL (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (τ : D.what₂.Tau) :
    Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.what₂.LL :=
  (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) * bZ u Tf.til.z0).map (tauLE D τ)

def PL (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP)
    (F : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL) :
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL :=
  C (∏ τ, (AL Tf c τ).det ^ shiftOf (lamT u D.R.m) τ) * rowSubK (AL Tf c) F

theorem AL_map (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (j : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) :
    (AL Tf c τ).map j = (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) *
      bZ u Tf.til.z0).map (embS D j τ) := by
  unfold AL
  rw [Matrix.map_map]
  rfl

theorem map_PL (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (j : D.what₂.LL →+* ℂ)
    (F : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL) :
    map j (PL Tf c F) = (∏ τ, ((AL Tf c τ).map j).det ^ shiftOf (lamT u D.R.m) τ) •
      blkRow (fun τ => (AL Tf c τ).map j) (map j F) := by
  unfold PL
  rw [map_mul, map_C, map_rowSubK, rowSubK_eq_subP, subP_eq_blkRow, MvPolynomial.smul_eq_C_mul, map_prod]
  congr 2
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_zpow₀, RingHom.map_det]
  rfl

theorem isUnit_AL_map (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (j : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) :
    IsUnit ((AL Tf c τ).map j).det := by
  rw [AL_map, Matrix.map_mul, Matrix.det_mul]
  refine IsUnit.mul ?_ ?_
  · exact isUnit_det_atInf (embS D j) (((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) τ
  · have := (bZ_isUnitS Tf).map (embS D j τ)
    rw [RingHom.map_det] at this
    exact this

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix NumberField

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem embS_embLLF : embS D D.what₂.embLL = Formalism.L2.Forms.embT D := by
  funext τ
  apply RingHom.ext
  intro x
  show D.what₂.embLL (D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) x)) =
    D.host.φ₀ (D.host.sigmaOf (D.eTau τ : D.R.GG) x)
  rw [← D.embE_φ₀]
  rfl

theorem pc_rat (Tf : FormsTiedSym D u Ch chOf) (x : Vl D u D.R.m)
    (Pc : (D.mem u).C.cls D.R.m → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL)
    (hPc : ∀ c z, (D.fm u).emb D.R.m x c z = fnOf _ (shiftOf (lamT u D.R.m)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
      ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z)) (c' : (D.mem u).C.cls D.R.m) :
    MvPolynomial.map D.what₂.embLL (Pc c') ∈ RatSpan D ((D.fm u).lam D.R.m) := by
  obtain ⟨⟨oN, -⟩, -⟩ := framesAt D u Ch chOf Tf D.what₂.embLL
  rw [embS_embLLF] at oN
  have hx := ((Tf.val D.R.m le_rfl (Or.inr rfl)).rat ((D.fm u).emb D.R.m x)).1 ⟨x, rfl⟩
  obtain ⟨P1, hP1, hP1z⟩ := hx.2 c'
  have hP1e : P1 = MvPolynomial.map D.what₂.embLL (Pc c') := by
    apply Formalism.L2.Col.fnOf_injective _ _ 1 (fun τ => by simp) oN
    funext y
    obtain ⟨z, rfl⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).eY.surjective y
    rw [← hP1z, hPc]
  rw [← hP1e]
  exact hP1

theorem isUnit_bZ_map (Tf : FormsTiedSym D u Ch chOf) (τ : D.what₂.Tau) :
    IsUnit ((bZ u Tf.til.z0).map (Formalism.L2.Forms.embT D τ)).det := by
  have := (bZ_isUnitS Tf).map (Formalism.L2.Forms.embT D τ)
  rw [RingHom.map_det] at this
  exact this

set_option maxHeartbeats 1000000 in

theorem base_eq (Tf : FormsTiedSym D u Ch chOf) (hL : Formalism.L2.Rows.LowerMapTieS Tf) (h : (D.fm u).PRat) (x : Vl D u D.R.m)
    (Pc : (D.mem u).C.cls D.R.m → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) D.what₂.LL)
    (hPc : ∀ c z, (D.fm u).emb D.R.m x c z = fnOf _ (shiftOf (lamT u D.R.m)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
      ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z))
    (Qc : (D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL)
    (hQc : ∀ c, Tf.valP.eW ((D.fm u).ptEmb ((D.fm u).PtL h x)) c =
      fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Qc c))) (c : (D.fm u).clsP) :
    MvPolynomial.map D.what₂.embLL (Qc c) =
      ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c) : ℂˣ) : ℂ))⁻¹ •
        MvPolynomial.map D.what₂.embLL (brTenL D u (PL Tf c (Pc ((D.fm u).til c)))) := by
  classical
  have hB := bZ_isUnitS Tf
  have hmZ := mZ_isUnit hB
  obtain ⟨-, ⟨oP, -⟩⟩ := framesAt D u Ch chOf Tf D.what₂.embLL
  rw [embS_embLLF] at oP
  have hP0 : MvPolynomial.map D.what₂.embLL (Pc ((D.fm u).til c)) ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) :=
    map_mem_CSpan_of_rat _ _ (pc_rat Tf x Pc hPc _) D.what₂.embLL
  let ginv : GL (Fin (D.R.N D.R.m)) D.host.E := ((Tf.til.ga c).1)⁻¹
  let M' : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ := atInf (Formalism.L2.Forms.embT D) (ginv : Matrix _ _ D.host.E)
  let A0 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ := fun τ => M' τ * (mZ u Tf.til.z0 τ)⁻¹
  have hA0 : ∀ τ, (AL Tf c τ).map D.what₂.embLL = A0 τ := by
    intro τ
    rw [AL_map, embS_embLLF]
    show ((ginv : Matrix _ _ D.host.E) * bZ u Tf.til.z0).map (Formalism.L2.Forms.embT D τ) =
      (ginv : Matrix _ _ D.host.E).map (Formalism.L2.Forms.embT D τ) * (((bZ u Tf.til.z0)⁻¹).map (Formalism.L2.Forms.embT D τ))⁻¹
    rw [Matrix.map_mul, Formalism.L2.Col.map_inv_matrix, Matrix.nonsing_inv_nonsing_inv _ (isUnit_bZ_map Tf τ)]
  have hA0u : ∀ τ, IsUnit (A0 τ).det := fun τ => by rw [← hA0]; exact isUnit_AL_map Tf c _ τ
  have hmapPL : MvPolynomial.map D.what₂.embLL (PL Tf c (Pc ((D.fm u).til c))) =
      (∏ τ, (A0 τ).det ^ shiftOf (lamT u D.R.m) τ) • blkRow A0 (MvPolynomial.map D.what₂.embLL (Pc ((D.fm u).til c))) := by
    rw [map_PL]
    simp only [hA0]
  set χ : ℂ := ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c) : ℂˣ) : ℂ)) with hχ
  have hPbmem : χ⁻¹ • MvPolynomial.map D.what₂.embLL (PL Tf c (Pc ((D.fm u).til c))) ∈
      Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) := by
    rw [hmapPL]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (blkRow_mem_CSpan _ A0 hA0u _ hP0))
  have hPb : ∀ s, Tf.eWz ((D.mem u).P.evz ((D.fm u).emb D.R.m x)) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) (χ⁻¹ • MvPolynomial.map D.what₂.embLL (PL Tf c (Pc ((D.fm u).til c))))
        ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s) := by
    intro s
    rw [Tf.evz ((D.fm u).emb D.R.m x) c s ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY.symm
      (((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s).tr M' (isUnit_det_atInf (Formalism.L2.Forms.embT D) ginv)))]
    · rw [hPc, Equiv.apply_symm_apply, fnOf_trG]
      have e1 : (fun τ => (1 : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ) τ * M' τ) = M' :=
        funext fun τ => by simp
      rw [e1, fnOf_change _ _ (mZ u Tf.til.z0) M' hmZ, hmapPL]
      simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, Units.val_inv_eq_inv_val]
      rfl
    · intro τ
      simp only [Equiv.apply_symm_apply]
      show ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s).1 τ =
        atInf (Formalism.L2.Forms.embT D) (Tf.til.ga c).1.1 τ * (M' τ * ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s).1 τ)
      rw [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul]
  have h3 := hL hB ((D.mem u).P.evz ((D.fm u).emb D.R.m x)) c _ hPbmem hPb
  have h4 : fnOf (gramC (gramP D) (Formalism.L2.Forms.embT D)) (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Qc c)) =
      fnOf (gramC (gramP D) (Formalism.L2.Forms.embT D)) (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u (χ⁻¹ • MvPolynomial.map D.what₂.embLL (PL Tf c (Pc ((D.fm u).til c))))) := by
    rw [← hQc c, (D.fm u).PtL_spec h x, h3]
  have h5 := Formalism.L2.Col.fnOf_injective _ _ 1 (fun τ => by simp) oP h4
  rw [h5, map_smul, map_brTenL]

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix NumberField
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in

theorem normClsAt_of_tors (hT : ChiTors) : NormClsAt := by
  intro D u Ch chOf Tf hL hBe h s x Pc hPc Qc hQc o ho o' ho' c
  classical
  have hbase := base_eq Tf hL h x Pc hPc Qc hQc c
  obtain ⟨k, hk, hχ⟩ := hT D u Ch chOf Tf c
  obtain ⟨a, ha, has⟩ := desc_scalar D.what₂.embLL (Qc c) (brTenL D u (PL Tf c (Pc ((D.fm u).til c)))) _ k hk hχ hbase
  have hAsu : ∀ τ, IsUnit ((AL Tf c τ).map s).det := fun τ => isUnit_AL_map Tf c s τ
  have hR : MvPolynomial.map s (Pc ((D.fm u).til c)) ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) :=
    map_mem_CSpan_of_rat _ _ (pc_rat Tf x Pc hPc _) s
  have hY := blkRow_mem_CSpan _ (fun τ => (AL Tf c τ).map s) hAsu _ hR
  have hQs : MvPolynomial.map s (Qc c) = (s a * ∏ τ, ((AL Tf c τ).map s).det ^ shiftOf (lamT u D.R.m) τ) •
      Formalism.L2.Ker.brTen D u (blkRow (fun τ => (AL Tf c τ).map s) (MvPolynomial.map s (Pc ((D.fm u).til c)))) := by
    rw [ha, MvPolynomial.smul_eq_C_mul, map_mul, map_C, map_brTenL, map_PL, map_smul, ← MvPolynomial.smul_eq_C_mul,
      smul_smul]
  have hoN : ∀ τ, (o.1 τ)ᴴ * gramC (gramN D D.R.m le_rfl) (embS D s) τ * o.1 τ = 1 := fun τ =>
    Formalism.L2.Col.frame_pos o ho τ (gramN_posDef_at Tf (embS D s τ)).posSemidef
  have hoP : ∀ τ, (o'.1 τ)ᴴ * gramC (gramP D) (embS D s) τ * o'.1 τ = 1 := fun τ =>
    Formalism.L2.Col.frame_pos o' ho' τ (gramP_posDef_at Tf (embS D s τ)).posSemidef
  have hon : ∀ τ, ((AL Tf c τ).map s * dOT u (o'.1 τ))ᴴ * gramC (gramN D D.R.m le_rfl) (embS D s) τ *
      ((AL Tf c τ).map s * dOT u (o'.1 τ)) = 1 := by
    intro τ
    rw [AL_map, Matrix.map_mul]
    exact frame_on_at Tf c (embS D s τ) (o'.1 τ) (hoP τ)
  have hind := term_frame_indep ((D.fm u).lam D.R.m) (gramC (gramN D D.R.m le_rfl) (embS D s)) (shiftOf (lamT u D.R.m)) o.1
    (fun τ => (AL Tf c τ).map s * dOT u (o'.1 τ)) hoN hon (MvPolynomial.map s (Pc ((D.fm u).til c)))
  have hchain := chain_at Tf hBe o'.1 o'.2 _ hY
  have hcomp : blkRow (fun τ => dOT u (o'.1 τ)) (blkRow (fun τ => (AL Tf c τ).map s) (MvPolynomial.map s (Pc ((D.fm u).til c)))) =
      subP (fun τ => (AL Tf c τ).map s * dOT u (o'.1 τ)) (MvPolynomial.map s (Pc ((D.fm u).til c))) := blkRow_comp _ _ _
  rw [hcomp] at hchain
  rw [hQs, map_smul, nfAll_smul_reB, normal_form_agree, hind]
  have hdet : ∏ τ, ‖((AL Tf c τ).map s * dOT u (o'.1 τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ) =
      (∏ τ, ‖((AL Tf c τ).map s).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)) *
        ∏ τ, ‖(dOT u (o'.1 τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_mul, norm_mul, mul_zpow]
  have hκ : ‖s a * ∏ τ, ((AL Tf c τ).map s).det ^ shiftOf (lamT u D.R.m) τ‖ ^ 2 =
      ‖s a‖ ^ 2 * ∏ τ, ‖((AL Tf c τ).map s).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ) := by
    rw [norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [norm_zpow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm (shiftOf (lamT u D.R.m) τ)]
    norm_num
  rw [hdet, hκ]
  have hsa : ‖s a‖ ^ 2 ≤ 1 := by
    have h1 := has s
    have h0 := norm_nonneg (s a)
    nlinarith
  set nW := (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (Formalism.L2.Ker.brTen D u (blkRow (fun τ => (AL Tf c τ).map s)
    (MvPolynomial.map s (Pc ((D.fm u).til c)))))) (subP o'.1 (Formalism.L2.Ker.brTen D u (blkRow (fun τ => (AL Tf c τ).map s)
    (MvPolynomial.map s (Pc ((D.fm u).til c))))))).re with hnW
  set K2 := ∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)
  set KA := ∏ τ, ‖((AL Tf c τ).map s).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)
  have hKA : 0 ≤ KA := Finset.prod_nonneg fun τ _ => zpow_nonneg (norm_nonneg _) _
  have hK2 : 0 ≤ K2 := Finset.prod_nonneg fun τ _ => zpow_nonneg (norm_nonneg _) _
  have hnW : 0 ≤ nW := Formalism.L2.Ker.ta_nfAll_nonneg _ _
  calc K2 * (‖s a‖ ^ 2 * KA * nW) = ‖s a‖ ^ 2 * (KA * (K2 * nW)) := by ring
    _ ≤ 1 * (KA * (ptB D u * ((∏ τ, ‖(dOT u (o'.1 τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)) *
          (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) (subP (fun τ => (AL Tf c τ).map s * dOT u (o'.1 τ)) (MvPolynomial.map s (Pc ((D.fm u).til c))))
            (subP (fun τ => (AL Tf c τ).map s * dOT u (o'.1 τ)) (MvPolynomial.map s (Pc ((D.fm u).til c))))).re))) :=
        mul_le_mul hsa (mul_le_mul_of_nonneg_left hchain hKA) (mul_nonneg hKA (mul_nonneg hK2 hnW)) zero_le_one
    _ = _ := by ring


end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

theorem chiTors : ChiTors := by
  intro D u Ch chOf Tf c
  classical
  let P : ℂ → Prop := fun z => ∃ k : ℕ, 0 < k ∧ z ^ k = 1
  have h1 : P 1 := ⟨1, one_pos, one_pow _⟩
  have hmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y ⟨k, hk, hx⟩ ⟨l, hl, hy⟩
    refine ⟨k * l, Nat.mul_pos hk hl, ?_⟩
    rw [mul_pow, pow_mul, hx, one_pow, one_mul, mul_comm k l, pow_mul, hy, one_pow]
  have hfac : ∀ a v h, P (((Tf.lamM a v h ((Tf.glevM).red a v h (Tf.tilAd.ka c)) : ℂˣ) : ℂ))⁻¹ := by
    intro a v h
    haveI : Finite (Formalism.L2.Forms.kv D.host.F v) := Formalism.UG.P.glint_finite_residueField v
    refine ⟨orderOf ((Tf.glevM).red a v h (Tf.tilAd.ka c)), orderOf_pos _, ?_⟩
    rw [inv_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one, inv_one]
  show P _
  rw [(Tf.glevM).chi_eq]
  refine Finset.prod_induction _ P hmul h1 fun a _ => ?_
  refine finprod_induction P h1 hmul fun v => ?_
  exact finprod_induction P h1 hmul fun h => hfac a v h

theorem normClsAt_holds : NormClsAt := normClsAt_of_tors chiTors

theorem norm_bound_of_injective_stable (h1 : ClassMapInjective) (h2 : StabiliserMapBijective) : NormBoundAtInfinity :=
  norm_bound_of_classes h1 h2 normClsAt_holds

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

set_option maxHeartbeats 1000000 in

theorem fvStab_holds {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (Tf : FormsTiedSym D u Ch chOf) : FvStab Tf := by
  intro c γ hγ v x hx
  have hF := Tf.fv D.R.m le_rfl (Or.inr rfl)
  have hγ' := ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI_range _ γ).1 hγ
  obtain ⟨κ, hκ, hκe⟩ := Subgroup.mem_map.mp hγ'
  have hbc : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 =
      ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1 * κ *
        ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1⁻¹ := by
    rw [← hκe]; rfl
  have hκv := ((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U_eq κ).1 hκ |>.2 (Tf.atT.eV v).1
  rw [(Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.UlocAlt (Tf.atT.eV v).1 (Tf.atT.eV v).2] at hκv
  obtain ⟨_, hfix⟩ := (Subgroup.mem_inf.mp hκv).2
  have hzx := dualLoc_of (Tf.cls D.R.m le_rfl (Or.inr rfl)) (Tf.atT.eV v).1 ((D.fm u).til c) x.1 x.2
  have hzg := dualLoc_of (Tf.cls D.R.m le_rfl (Or.inr rfl)) (Tf.atT.eV v).1 ((D.fm u).til c) _ hx
  have key := conj_stepA (Tf.atT.eV v).1 _ κ γ.1 hbc x.1
  exact (hF v ((D.fm u).til c) ⟨_, hx⟩ hzg).trans ((congrArg _ ((congrArg _ (Subtype.ext key)).trans (hfix ⟨_, hzx⟩))).trans
    (hF v ((D.fm u).til c) x hzx).symm)

theorem class_injective_holds : ClassMapInjective :=
  class_injective_of_self_dual (fun _ _ _ _ Tf => selfDualP_of_formsTiedSym Tf)

theorem stabiliser_bijective_holds : StabiliserMapBijective :=
  stabiliser_bijective_self_dual (fun _ _ _ _ Tf => selfDualP_of_formsTiedSym Tf) (fun _ _ _ _ Tf => fvStab_holds Tf)

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section
namespace Formalism.L2.GlobalTheoryTheory.Br

theorem norm_bound_holds : NormBoundAtInfinity := norm_bound_of_injective_stable class_injective_holds stabiliser_bijective_holds

end Formalism.L2.GlobalTheoryTheory.Br
end
