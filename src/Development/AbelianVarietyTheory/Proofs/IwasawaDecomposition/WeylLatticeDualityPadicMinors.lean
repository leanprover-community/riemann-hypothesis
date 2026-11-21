import Mathlib
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramInjectivity.InstFintypeColChoice
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwCauchyBinet
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwInjective
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQHW
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowAct
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CBinet
import BuildAid.ForwardExisting

section
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylReproducingSym

open Formalism.GradedWeylDivisibility GlobalTheory.WeylMinorDual

def oeEquivCard (h n : ℕ) : {S : Finset (Fin n) // S.card = h} ≃ (Fin h ↪o Fin n) where
  toFun S := S.1.orderEmbOfFin S.2
  invFun I := ⟨Finset.univ.map I.toEmbedding, by simp⟩
  left_inv S := by
    apply Subtype.ext
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact Finset.orderEmbOfFin_mem _ _ i
    · intro hx
      have : x ∈ Set.range (S.1.orderEmbOfFin S.2) := by rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨i, hi⟩ := this
      exact ⟨i, hi⟩
  right_inv I := by
    apply OrderEmbedding.range_inj.mp
    rw [Finset.range_orderEmbOfFin]
    ext x
    simp

private theorem det_mul_eq_sum_det_submatrix_mul_prod {R : Type} [CommRing R] {h n : ℕ}
    (A : Matrix (Fin h) (Fin n) R) (B : Matrix (Fin n) (Fin h) R) :
    (A * B).det = ∑ p : Fin h → Fin n, (A.submatrix id p).det * ∏ i, B (p i) i := by
  simp_rw [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.submatrix_apply, id, Finset.prod_mul_distrib]
  ring

private theorem sum_perm_det_submatrix_mul_prod_eq_det_mul_det {R : Type} [CommRing R] {h n : ℕ}
    (A : Matrix (Fin h) (Fin n) R) (B : Matrix (Fin n) (Fin h) R) (e : Fin h ↪o Fin n) :
    ∑ τ : Equiv.Perm (Fin h), (A.submatrix id (⇑e ∘ ⇑τ)).det * ∏ i, B (e (τ i)) i =
      (A.submatrix id e).det * (B.submatrix e id).det := by
  have hA : ∀ τ : Equiv.Perm (Fin h), (A.submatrix id (⇑e ∘ ⇑τ)).det =
      Equiv.Perm.sign τ * (A.submatrix id e).det := fun τ => by
    rw [← Matrix.det_permute' τ (A.submatrix id e), Matrix.submatrix_submatrix]
    rfl
  simp_rw [hA, Matrix.det_apply' (B.submatrix e id), Finset.mul_sum, Matrix.submatrix_apply, id]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring

theorem cauchyBinet_oe {R : Type} [CommRing R] {h n : ℕ}
    (A : Matrix (Fin h) (Fin n) R) (B : Matrix (Fin n) (Fin h) R) :
    (A * B).det = ∑ I : Fin h ↪o Fin n, (A.submatrix id I).det * (B.submatrix I id).det := by
  rw [det_mul_eq_sum_det_submatrix_mul_prod]
  simp_rw [← sum_perm_det_submatrix_mul_prod_eq_det_mul_det A B]
  rw [← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => ⇑x.1 ∘ ⇑x.2) (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · rintro ⟨e, τ⟩ _ _ ⟨e', τ'⟩ _ _ hx
    have hr : Set.range ⇑e = Set.range ⇑e' := by
      have h1 : Set.range (⇑e ∘ ⇑τ) = Set.range (⇑e' ∘ ⇑τ') := congrArg Set.range hx
      rwa [τ.surjective.range_comp, τ'.surjective.range_comp] at h1
    obtain rfl : e = e' := OrderEmbedding.range_inj.mp hr
    obtain rfl : τ = τ' := Equiv.ext fun i => e.injective (congrFun hx i)
    rfl
  · intro p _ hp
    have hinj : Function.Injective p := by
      intro i j hij
      by_contra hne
      apply hp
      rw [Matrix.det_zero_of_column_eq hne (fun k => by simp only [Matrix.submatrix_apply, id, hij]),
        zero_mul]
    have hc : (Finset.univ.image p).card = h := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have hmem : ∀ i, ∃ j, (Finset.univ.image p).orderEmbOfFin hc j = p i := by
      intro i
      have : p i ∈ Set.range ((Finset.univ.image p).orderEmbOfFin hc) := by
        rw [Finset.range_orderEmbOfFin]
        simp
      exact this
    choose t ht using hmem
    have tinj : Function.Injective t := by
      intro i j hij
      apply hinj
      rw [← ht i, ← ht j, hij]
    have tbij : Function.Bijective t := Finite.injective_iff_bijective.mp tinj
    have hp' : ⇑((Finset.univ.image p).orderEmbOfFin hc) ∘ ⇑(Equiv.ofBijective t tbij) = p :=
      funext ht
    refine ⟨((Finset.univ.image p).orderEmbOfFin hc, Equiv.ofBijective t tbij), Finset.mem_univ _, ?_, hp'⟩
    show (A.submatrix id (⇑((Finset.univ.image p).orderEmbOfFin hc) ∘ ⇑(Equiv.ofBijective t tbij))).det *
      ∏ i, B ((⇑((Finset.univ.image p).orderEmbOfFin hc) ∘ ⇑(Equiv.ofBijective t tbij)) i) i ≠ 0
    rw [hp']
    exact hp
  · intro x _ _
    rfl

theorem rowAct_leadMinor (N h : ℕ) (hh : h ≤ N) (x : Fin N × Fin N → ℚ) :
    rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose (initMinor ℚ (r := N) (n := N) (Fin.castLE hh) hh) =
      ∑ K : Fin h ↪o Fin N, C (eval x (initMinor ℚ (r := N) (n := N) (⇑K) hh)) *
        initMinor ℚ (r := N) (n := N) (⇑K) hh := by
  have h1 : rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose
      (initMinor ℚ (r := N) (n := N) (Fin.castLE hh) hh) =
      ((Matrix.of fun (p : Fin h) (b : Fin N) => (C (x (b, Fin.castLE hh p)) : MvPolynomial (Fin N × Fin N) ℚ)) *
        Matrix.of fun (b : Fin N) (q : Fin h) => (X (b, Fin.castLE hh q) : MvPolynomial (Fin N × Fin N) ℚ)).det := by
    rw [initMinor, AlgHom.map_det]
    congr 1
    ext p q
    simp [rowAct, Matrix.mul_apply, aeval_X]
  rw [h1, cauchyBinet_oe]
  refine Finset.sum_congr rfl fun K _ => ?_
  congr 1
  rw [initMinor, RingHom.map_det, RingHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext p q
  simp

theorem rowAct_hw_expand (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (x : Fin N × Fin N → ℚ) :
    rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose (hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) =
      ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        C (eval x (colProd ℚ N Y hY J)) * colProd ℚ N Y hY J := by
  have hb := bidet_lead ℚ N (fun c : Fin (Y.rowLen 0) => Y.colLen c) (colLen_le hY)
    (fun c => Fin.castLE (colLen_le hY c)) (fun _ _ => rfl)
  rw [shapeDeg_colLen] at hb
  rw [← hb, bideterminant, map_prod]
  simp only [rowAct_leadMinor]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  simp only [colProd, bideterminant, map_prod, Finset.prod_mul_distrib]

theorem reproducing_left : ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (f : MvPolynomial (Fin N × Fin N) ℚ),
    f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r) →
    ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f := by
  intro N Y hY f hf
  have hsum : ∀ {ι : Type} (s : Finset ι) (F : ι → MvPolynomial (Fin N × Fin N) ℚ)
      (g : MvPolynomial (Fin N × Fin N) ℚ), fockQ (∑ i ∈ s, F i) g = ∑ i ∈ s, fockQ (F i) g :=
    fun s F g => map_sum (AddMonoidHom.mk' (fun p => fockQ p g)
      (fun a b => (Formalism.GradedWeylDivisibility.fockQBilin _ a b g 0).1)) F s
  have hsmul : ∀ (c : ℚ) (p g : MvPolynomial (Fin N × Fin N) ℚ), fockQ (c • p) g = c * fockQ p g :=
    fun c p g => (Formalism.GradedWeylDivisibility.fockQBilin _ p p g c).2
  have hanti : Antitone (fun r : Fin N => Y.rowLen r) := fun a b hab => Y.rowLen_anti _ _ hab
  apply MvPolynomial.funext
  intro x
  have hev : eval (idFrame ℚ N N) (rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)) f) = eval x f := by
    have hcomp : (aeval (idFrame ℚ N N)).comp (rowAct ℚ (n := N) (Matrix.of fun a s : Fin N => x (a, s))) =
        aeval x := by
      apply MvPolynomial.algHom_ext
      intro v
      simp [rowAct, idFrame, aeval_X, Fin.val_inj]
    have h3 := congrArg (fun φ => φ f) hcomp
    simpa [MvPolynomial.coe_aeval_eq_eval] using h3
  have hmem := Formalism.GradedWeylDivisibility.dualWeylRowStable ℚ N N _ (Matrix.of fun a s : Fin N => x (a, s)) f hf
  have h1 := Formalism.GradedWeylDivisibility.fock_space_highest_weight N N le_rfl (fun r : Fin N => Y.rowLen r) hanti _ hmem
  have h2 := Formalism.GradedWeylDivisibility.fock_space_row_action N N (Matrix.of fun a s : Fin N => x (a, s)).transpose
    (hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) f
  rw [Matrix.transpose_transpose, h1, hev, rowAct_hw_expand N Y hY x, hsum] at h2
  simp only [MvPolynomial.C_mul', hsmul] at h2
  simp only [map_sum, MvPolynomial.smul_eval]
  rw [mul_comm (fockQ _ _) (eval x f), ← h2]
  exact Finset.sum_congr rfl fun J _ => mul_comm _ _

end GlobalTheory.WeylReproducingSym
end
end

open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnMinorProducts_fock_reproducing_dualWeyl : ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (f : MvPolynomial (Fin N × Fin N) ℚ),
    f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r) →
    ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f := by
  atlas_forward_decl GlobalTheory.WeylReproducingSym.reproducing_left
end

section
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylDualData

open Formalism.BasicNotions Formalism.L2.DIV

theorem fockQ_sum_zsmul {σ κ : Type} [Fintype κ] (c : κ → ℤ) (f : κ → MvPolynomial σ ℚ)
    (g : MvPolynomial σ ℚ) :
    Formalism.GradedWeylDivisibility.fockQ (∑ i, c i • f i) g = ∑ i, (c i : ℚ) * Formalism.GradedWeylDivisibility.fockQ (f i) g := by
  rw [← ps_fockL_rat, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Int.cast_smul_eq_zsmul ℚ, LinearMap.map_smulₛₗ, LinearMap.smul_apply, ps_fockL_rat, smul_eq_mul]
  simp

theorem dual_data : ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N),
    (∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r),
      ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f) →
    ∃ (ι : Type) (_ : Fintype ι) (b d : ι → MvPolynomial (Fin N × Fin N) ℤ)
      (B : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ι → ℤ)
      (Cm : ι → (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ℤ),
      (∀ J, GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = ∑ i, B J i • b i) ∧
      (∀ i, b i = ∑ J, Cm i J • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J) ∧
      (∀ i, ∑ J, B J i • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = d i) ∧
      (∀ i, d i ∈ Formalism.GradedWeylDivisibility.weyl ℤ N N (le_refl N) (fun r : Fin N => Y.rowLen r)) := by
  classical
  intro N Y hY H
  have hanti : Antitone (fun r : Fin N => Y.rowLen r) := fun a b hab => Y.rowLen_anti _ _ hab
  letI : Fintype (Formalism.GradedWeylDivisibility.ssIdx N N (fun r : Fin N => Y.rowLen r)) :=
    (Formalism.GradedWeylDivisibility.sSIdxFinite N N _).fintype
  obtain ⟨b, d, hb, hd, hbd⟩ := GlobalTheory.StdDual.exists_dual_bases N (fun r : Fin N => Y.rowLen r) hanti
  have hN0 : Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
      (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) ≠ 0 :=
    ((Formalism.GradedWeylDivisibility.fockQPos _ _ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))).2 (Formalism.GradedWeylDivisibility.hwNe ℚ N N le_rfl _)).ne'
  have hcol : ∀ J, Formalism.GradedWeylDivisibility.intQ N N (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J) =
      GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J := fun J => fk_map_bidet (Int.castRingHom ℚ) _ _ _
  have hinj : Function.Injective (Formalism.GradedWeylDivisibility.intQ N N) :=
    MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  have hspan : Submodule.span ℤ (Set.range b) =
      Submodule.span ℤ (Set.range (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY)) := by
    rw [hb, ← GlobalTheory.StdDual.dualWeyl_intQ, GlobalTheory.WeylMinorDual.dualWeyl_eq_span_colProd ℤ N Y hY,
      Submodule.map_span, ← Set.range_comp]
    congr 2
    funext J
    exact hcol J
  have hBex : ∀ J, ∃ c : Formalism.GradedWeylDivisibility.ssIdx N N (fun r : Fin N => Y.rowLen r) → ℤ,
      ∑ i, c i • b i = GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J := fun J =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hspan ▸ Submodule.subset_span ⟨J, rfl⟩)
  choose B hB using hBex
  have hCex : ∀ i, ∃ c : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ℤ,
      ∑ J, c J • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J = b i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)
  choose Cm hCm using hCex
  have hdW : ∀ k, d k ∈ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl (fun r : Fin N => Y.rowLen r)).map (Formalism.GradedWeylDivisibility.intQ N N) := by
    intro k
    rw [GlobalTheory.StdDual.weyl_intQ, ← hd]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hdD : ∀ k, d k ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r) := by
    intro k
    have h := hdW k
    rw [GlobalTheory.StdDual.weylEqDualNabla N N le_rfl _ hanti] at h
    exact h.1
  have hkey : ∀ k, ∑ J, B J k • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J = d k := by
    intro k
    have h := H (d k) (hdD k)
    have e : ∀ J, Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) (d k) =
        (B J k : ℚ) * Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
          (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) := by
      intro J
      rw [← hB J, fockQ_sum_zsmul]
      simp only [hbd, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [e] at h
    apply smul_right_injective _ hN0
    simp only
    rw [← h, Finset.smul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, mul_comm]
  refine ⟨Formalism.GradedWeylDivisibility.ssIdx N N (fun r : Fin N => Y.rowLen r), inferInstance,
    fun i => ∑ J, Cm i J • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J,
    fun k => ∑ J, B J k • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J, B, Cm, ?_, fun _ => rfl, fun _ => rfl, ?_⟩
  · have hbZ : ∀ i, Formalism.GradedWeylDivisibility.intQ N N (∑ J, Cm i J • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J) = b i := by
      intro i
      rw [map_sum, ← hCm i]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [map_zsmul, hcol]
    intro J
    apply hinj
    rw [hcol, map_sum, ← hB J]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hbZ]
  · intro k
    obtain ⟨w, hw, hwe⟩ := hdW k
    have : (∑ J, B J k • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J) = w := by
      apply hinj
      rw [hwe, ← hkey k, map_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [map_zsmul, hcol]
    show (∑ J, B J k • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J) ∈ _
    rw [this]
    exact hw

end GlobalTheory.WeylDualData
end
end

open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_dual_bases_columnMinors_weylLattice : ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N), (∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r),
      ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f) →
    ∃ (ι : Type) (_ : Fintype ι) (b d : ι → MvPolynomial (Fin N × Fin N) ℤ)
      (B : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ι → ℤ)
      (Cm : ι → (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ℤ),
      (∀ J, GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = ∑ i, B J i • b i) ∧
      (∀ i, b i = ∑ J, Cm i J • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J) ∧
      (∀ i, ∑ J, B J i • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = d i) ∧
      (∀ i, d i ∈ Formalism.GradedWeylDivisibility.weyl ℤ N N (le_refl N) (fun r : Fin N => Y.rowLen r)) := by
  atlas_forward_decl GlobalTheory.WeylDualData.dual_data
end

section
section
open MvPolynomial

namespace GlobalTheory.WeylIntExpansion

theorem weyl_int_expansion : ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N), (∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r),
      ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f) →
    ∀ f : MvPolynomial (Fin N × Fin N) ℤ, f ∈ Formalism.GradedWeylDivisibility.weyl ℤ N N (le_refl N) (fun r : Fin N => Y.rowLen r) →
    ∃ z : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ℤ,
      (∀ J, Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J)) =
        (z J : ℚ) * Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
          (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))) ∧
      ∑ J, z J • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = f := by
  intro N Y hY hrep f hf
  set μ : Fin N → ℕ := fun r => Y.rowLen r with hμ
  set N0 := Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) μ) (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) μ) with hN0
  have hN0ne : N0 ≠ 0 :=
    ((Formalism.GradedWeylDivisibility.fockQPos _ _ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) μ)).2 (Formalism.GradedWeylDivisibility.hwNe ℚ N N le_rfl _)).ne'
  have hanti : Antitone μ := fun a b hab => Y.rowLen_anti _ _ hab
  have hfQ : Formalism.GradedWeylDivisibility.intQ N N f ∈ Formalism.GradedWeylDivisibility.bDual N N le_rfl μ ((Formalism.GradedWeylDivisibility.dualWeyl ℤ N N μ).map (Formalism.GradedWeylDivisibility.intQ N N)) := by
    rw [← GlobalTheory.StdDual.weylEqDualNabla N N le_rfl μ hanti]
    exact ⟨f, hf, rfl⟩
  have hmem : ∀ J, GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ N N μ := by
    intro J
    rw [hμ, GlobalTheory.WeylMinorDual.dualWeyl_eq_span_colProd ℤ N Y hY]
    exact Submodule.subset_span ⟨J, rfl⟩
  have hz : ∀ J, ∃ z : ℤ, Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) f)
      (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J)) = z * N0 :=
    fun J => hfQ.2 _ ⟨_, hmem J, rfl⟩
  choose z hz using hz
  refine ⟨z, hz, ?_⟩
  have hmap : ∀ J, map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J) =
      GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J := fun J => by
    unfold GlobalTheory.WeylMinorDual.colProd
    exact Formalism.L2.DIV.fk_map_bidet _ _ _ _
  have h := hrep (map (Int.castRingHom ℚ) f) hfQ.1
  have hc : ∀ J, Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) (map (Int.castRingHom ℚ) f) = z J * N0 :=
    fun J => by rw [(Formalism.GradedWeylDivisibility.fockQPos _ _ _).1, ← hmap, hz]
  simp only [hc] at h
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  apply smul_right_injective _ hN0ne
  simp only
  rw [← h, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [map_zsmul, hmap, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, mul_comm]

end GlobalTheory.WeylIntExpansion
end

open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylLattice_integral_columnMinor_expansion : ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N), (∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r),
      ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f) →
    ∀ f : MvPolynomial (Fin N × Fin N) ℤ, f ∈ Formalism.GradedWeylDivisibility.weyl ℤ N N (le_refl N) (fun r : Fin N => Y.rowLen r) →
    ∃ z : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ℤ,
      (∀ J, Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J)) =
        (z J : ℚ) * Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
          (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))) ∧
      ∑ J, z J • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = f := by
  atlas_forward_decl GlobalTheory.WeylIntExpansion.weyl_int_expansion
end

section
section
open MvPolynomial

noncomputable section
namespace GlobalTheory.FockMinorFunctional
open Formalism.L2.DIV

theorem map_int_eq_map_rat {σ K : Type} [Field K] [CharZero K] (f : MvPolynomial σ ℤ) :
    map (Int.castRingHom K) f = map (algebraMap ℚ K) (map (Int.castRingHom ℚ) f) := by
  have e : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K := RingHom.ext_int _ _
  rw [map_map, e]

theorem nablaX_eq {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (J : ∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N) :
    WeylLatticeDuality.nablaX N nu J = Formalism.BasicNotions.KM.nablaX N nu J := by
  unfold WeylLatticeDuality.nablaX Formalism.BasicNotions.KM.nablaX
  rfl

theorem colProd_map {K : Type} [Field K] [CharZero K] (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N)
    (J : ∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) :
    GlobalTheory.WeylMinorDual.colProd K N Y hY J =
      map (algebraMap ℚ K) (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J)) := by
  rw [← map_int_eq_map_rat]
  unfold GlobalTheory.WeylMinorDual.colProd
  rw [fk_map_bidet]

theorem aeval_map_nablaX {K Lt : Type} [Field K] [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (J : ∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N) :
    aeval (R := K) (fun v : Lt × ℕ × Fin N =>
        if h : v.2.1 < N then (X (v.1, v.2.2, (⟨v.2.1, h⟩ : Fin N)) : Pol K Lt N) else 0)
      (map (Int.castRingHom K) (WeylLatticeDuality.nablaX N nu J)) =
      ten fun s => GlobalTheory.WeylMinorDual.colProd K N (nu s) (hY s) (J s) := by
  rw [← algebraMap_int_eq, aeval_map_algebraMap, nablaX_eq]
  exact GlobalTheory.WeylMinorDual.aeval_nablaX N nu hY J

theorem fock_functional_nablaX : ∀ (p : ℕ) [Fact p.Prime] {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (g : Lt → MvPolynomial (Fin N × Fin N) ℤ),
    ∃ Ψ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
      ∀ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
        Ψ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) =
          ∏ s, ((Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) (g s))
            (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) (J s))) : ℚ) : ℂ_[p]) := by
  intro p _ Lt _ _ N nu hY g
  let ρ : Lt × ℕ × Fin N → Pol ℂ_[p] Lt N := fun v =>
    if h : v.2.1 < N then X (v.1, v.2.2, (⟨v.2.1, h⟩ : Fin N)) else 0
  let G : Pol ℂ_[p] Lt N := ten fun s => map (Int.castRingHom ℂ_[p]) (g s)
  refine ⟨(fockBL G).comp (aeval ρ).toLinearMap, fun J => ?_⟩
  have h1 : aeval ρ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) =
      ten fun s => GlobalTheory.WeylMinorDual.colProd ℂ_[p] N (nu s) (hY s) (J s) := by
    exact aeval_map_nablaX N nu hY J
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, h1, fockBL_apply, GlobalTheory.WeylMinorDual.fockB_ten]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_int_eq_map_rat, colProd_map, GlobalTheory.WeylMinorDual.fockB_map]
end GlobalTheory.FockMinorFunctional
end
end

open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fock_functional_on_nablaX_products : ∀ (p : ℕ) [Fact p.Prime] {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (g : Lt → MvPolynomial (Fin N × Fin N) ℤ),
    ∃ Ψ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
      ∀ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
        Ψ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) =
          ∏ s, ((Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) (g s))
            (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) (J s))) : ℚ) : ℂ_[p]) := by
  atlas_forward_decl GlobalTheory.FockMinorFunctional.fock_functional_nablaX
end

section
section
open MvPolynomial

attribute [local instance 2000] RelEmbedding.instFintype

noncomputable section

namespace GlobalTheory.WeylLatDualPf

theorem fock_reproducing_formula (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (f : MvPolynomial (Fin N × Fin N) ℚ)
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r)) :
    ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f :=
  GlobalTheory.T.columnMinorProducts_fock_reproducing_dualWeyl N Y hY f hf

theorem dualData (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N)
    (hrep : ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r),
      ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f) :
    ∃ (ι : Type) (_ : Fintype ι) (b d : ι → MvPolynomial (Fin N × Fin N) ℤ)
      (B : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ι → ℤ)
      (Cm : ι → (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ℤ),
      (∀ J, GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = ∑ i, B J i • b i) ∧
      (∀ i, b i = ∑ J, Cm i J • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J) ∧
      (∀ i, ∑ J, B J i • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = d i) ∧
      (∀ i, d i ∈ Formalism.GradedWeylDivisibility.weyl ℤ N N (le_refl N) (fun r : Fin N => Y.rowLen r)) :=
  GlobalTheory.T.exists_integral_dual_bases_columnMinors_weylLattice N Y hY hrep

theorem weylExpand (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N)
    (hrep : ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r),
      ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f)
    (f : MvPolynomial (Fin N × Fin N) ℤ) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl ℤ N N (le_refl N) (fun r : Fin N => Y.rowLen r)) :
    ∃ z : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ℤ,
      (∀ J, Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J)) =
        (z J : ℚ) * Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
          (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))) ∧
      ∑ J, z J • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = f :=
  GlobalTheory.T.weylLattice_integral_columnMinor_expansion N Y hY hrep f hf

theorem fockFunctional (p : ℕ) [Fact p.Prime] {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (g : Lt → MvPolynomial (Fin N × Fin N) ℤ) :
    ∃ Ψ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
      ∀ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
        Ψ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) =
          ∏ s, ((Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) (g s))
            (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) (J s))) : ℚ) : ℂ_[p]) :=
  GlobalTheory.T.exists_fock_functional_on_nablaX_products p N nu hY g

def rho (p : ℕ) [Fact p.Prime] {Lt : Type} (N : ℕ) (s : Lt) :
    MvPolynomial (Fin N × Fin N) ℤ →+* MvPolynomial (Lt × ℕ × Fin N) ℂ_[p] :=
  (rename (fun v : Fin N × Fin N => (s, (v.2 : ℕ), v.1))).toRingHom.comp (map (Int.castRingHom ℂ_[p]))

theorem nablaX_eq_prod (p : ℕ) [Fact p.Prime] {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (J : ∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N) :
    map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) =
      ∏ s, rho p N s (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) (J s)) := by
  unfold WeylLatticeDuality.nablaX
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  unfold GlobalTheory.WeylMinorDual.colProd Formalism.GradedWeylDivisibility.bideterminant
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext i k
  simp [rho, RingHom.mapMatrix_apply]

theorem deX_trunc {Lt T : Type} [Fintype Lt] {k : Type} [CommRing k] (e : Lt → T) (he : Function.Bijective e) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (y' : Lt → Fin N → ℕ → k) :
    ∃ y : T → Matrix (Fin N) (Fin N) k,
      WeylLatticeDuality.DeX N nu y' = WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s)) := by
  set E := Equiv.ofBijective e he
  refine ⟨fun τ => Matrix.of fun a b => y' (E.symm τ) a b, ?_⟩
  unfold WeylLatticeDuality.DeX
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  congr 1
  ext i j
  have hj : (j : ℕ) < N := lt_of_lt_of_le j.2 ((GlobalTheory.WeylMinorDual.colLen_le (hY s) c))
  have hs : E.symm (e s) = s := E.symm_apply_apply s
  simp only [Matrix.of_apply, WeylLatticeDuality.colsOf, dif_pos hj, hs]

theorem canExpand (p : ℕ) [Fact p.Prime] {Lt T : Type} [Fintype Lt] [DecidableEq Lt] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N)
    (φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p])) (y : T → Matrix (Fin N) (Fin N) ℂ_[p]) :
    φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) =
      ∑ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
        φ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) *
          ∏ s, eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (map (Int.castRingHom ℂ_[p]) (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) (J s))) := by
  have h := PI.WwInjectiveWork.deX_eq_sum N nu cauchy_binet_minors (K := ℂ_[p])
    (fun s => WeylLatticeDuality.colsOf (y (e s)))
  change φ (PI.WwInjective.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) = _
  rw [h, map_sum]
  let eqv : PI.WwInjective.KM.ColChoice N nu ≃ (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N) :=
    ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  refine Fintype.sum_equiv eqv _ _ fun J => ?_
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul, mul_comm]
  congr 1
  unfold PI.WwInjective.minY
  refine Finset.prod_congr rfl fun s _ => ?_
  unfold GlobalTheory.WeylMinorDual.colProd Formalism.GradedWeylDivisibility.bideterminant
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  have hj : (j : ℕ) < N := lt_of_lt_of_le j.2 ((GlobalTheory.WeylMinorDual.colLen_le (hY s) c))
  simp [WeylLatticeDuality.colsOf, dif_pos hj, RingHom.mapMatrix_apply]
  rfl

theorem nsum {p : ℕ} [Fact p.Prime] {α : Type} (s : Finset α) (f : α → ℂ_[p]) (h : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖∑ i ∈ s, f i‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one h

theorem nprod {p : ℕ} [Fact p.Prime] {α : Type} (s : Finset α) (f : α → ℂ_[p]) (h : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖∏ i ∈ s, f i‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one (fun i _ => norm_nonneg _) h

theorem nint {p : ℕ} [Fact p.Prime] (z : ℤ) : ‖(z : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ z

theorem sum_prod_eq {Lt : Type} [Fintype Lt] [DecidableEq Lt] {κ : Lt → Type} [∀ s, Fintype (κ s)] {R : Type} [CommRing R]
    (f : ∀ s, κ s → R) : ∑ J : (∀ s, κ s), ∏ s, f s (J s) = ∏ s, ∑ j, f s j :=
  (Finset.prod_univ_sum (fun s => (Finset.univ : Finset (κ s))) f).symm.trans (by simp [Fintype.piFinset_univ])

theorem colLen_le {N : ℕ} (Y : YoungDiagram) (h0 : ∀ r, N ≤ r → Y.rowLen r = 0) : Y.colLen 0 ≤ N := by
  by_contra h
  push_neg at h
  have hm : (N, 0) ∈ Y := YoungDiagram.mem_iff_lt_colLen.mpr h
  have := YoungDiagram.mem_iff_lt_rowLen.mp hm
  rw [h0 N le_rfl] at this
  exact Nat.not_lt_zero _ this

theorem rho_zsmul (p : ℕ) [Fact p.Prime] {Lt : Type} (N : ℕ) (s : Lt) (z : ℤ) (P : MvPolynomial (Fin N × Fin N) ℤ) :
    rho p N s (z • P) = C (z : ℂ_[p]) * rho p N s P := by
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ_[p], smul_eq_C_mul]

theorem expand_prod (p : ℕ) [Fact p.Prime] {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) {κ κ' : Lt → Type}
    [∀ s, Fintype (κ s)] [∀ s, Fintype (κ' s)] (u : ∀ s, κ s → MvPolynomial (Fin N × Fin N) ℤ)
    (v : ∀ s, κ' s → MvPolynomial (Fin N × Fin N) ℤ) (M : ∀ s, κ s → κ' s → ℤ)
    (h : ∀ s j, u s j = ∑ k, M s j k • v s k) (i : ∀ s, κ s) :
    ∏ s, rho p N s (u s (i s)) = ∑ k : (∀ s, κ' s), C (∏ s, (M s (i s) (k s) : ℂ_[p])) * ∏ s, rho p N s (v s (k s)) := by
  rw [show (∑ k : (∀ s, κ' s), C (∏ s, (M s (i s) (k s) : ℂ_[p])) * ∏ s, rho p N s (v s (k s))) =
      ∑ k : (∀ s, κ' s), ∏ s, (C (M s (i s) (k s) : ℂ_[p]) * rho p N s (v s (k s))) from
    Finset.sum_congr rfl fun k _ => by rw [map_prod, ← Finset.prod_mul_distrib]]
  rw [sum_prod_eq (fun s k => C (M s (i s) k : ℂ_[p]) * rho p N s (v s k))]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [h s (i s), map_sum]
  exact Finset.sum_congr rfl fun k _ => rho_zsmul p N s _ _

theorem stmt_holds : WeylLatticeDuality.Stmt := by
  intro p _ Lt T _ _ e he N nu ν hν h0 φ
  classical
  have hY : ∀ s, (nu s).colLen 0 ≤ N := fun s => colLen_le (nu s) (h0 s)
  set E := Equiv.ofBijective e he with hE
  have hμ : ∀ s, (fun r : Fin N => (nu s).rowLen r) = ν (e s) := fun s => funext fun r => hν s r
  have hrep := fun s => fock_reproducing_formula N (nu s) (hY s)
  have hnab := nablaX_eq_prod p N nu hY
  constructor
  · intro hφ
    choose ι hιF b d B Cm hB hCm hd hdW using fun s => dualData N (nu s) (hY s) (hrep s)
    set β : (∀ s, ι s) → MvPolynomial (Lt × ℕ × Fin N) ℂ_[p] := fun i => ∏ s, rho p N s (b s (i s)) with hβdef
    have hβ : ∀ i, φ (β i) = ∑ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
        (∏ s, (Cm s (i s) (J s) : ℂ_[p])) * φ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) := by
      intro i
      simp only [hβdef]
      rw [expand_prod p N b _ Cm hCm i, map_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [← smul_eq_C_mul, map_smul, smul_eq_mul, hnab]
    have hnabβ : ∀ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
        φ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) =
          ∑ i : (∀ s, ι s), (∏ s, (B s (J s) (i s) : ℂ_[p])) * φ (β i) := by
      intro J
      rw [hnab, expand_prod p N _ b B hB J, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

    have hcan : ∀ y : T → Matrix (Fin N) (Fin N) ℂ_[p],
        φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) =
          ∑ i : (∀ s, ι s), φ (β i) * ∏ s, eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (map (Int.castRingHom ℂ_[p]) (d s (i s))) := by
      intro y
      set ev : Lt → MvPolynomial (Fin N × Fin N) ℤ →+* ℂ_[p] := fun s =>
        (eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)).comp (map (Int.castRingHom ℂ_[p])) with hev
      have hev' : ∀ s P, eval (fun k : Fin N × Fin N => y (e s) k.1 k.2) (map (Int.castRingHom ℂ_[p]) P) = ev s P :=
        fun s P => rfl
      simp only [hev']
      rw [canExpand p e N nu hY φ y]
      simp only [hev', hnabβ, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hds : ∀ s, ev s (d s (i s)) =
          ∑ j, (B s j (i s) : ℂ_[p]) * ev s (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) j) := by
        intro s
        rw [← hd s (i s), map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [map_zsmul, zsmul_eq_mul]
      simp only [hds]
      rw [← sum_prod_eq (fun s j => (B s j (i s) : ℂ_[p]) * ev s (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) j)),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [Finset.prod_mul_distrib]
      ring
    have hfun : (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] =>
        φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s)))) =
        ∑ i : (∀ s, ι s), fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => φ (β i) * ∏ s,
          eval (fun k : Fin N × Fin N => y (e s) k.1 k.2) (map (Int.castRingHom ℂ_[p]) (d s (i s))) := by
      funext y
      rw [hcan, Finset.sum_apply]
    rw [hfun]
    refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_
    have key : ∀ s' s, s' = s → d s' (i s') = d s (i s) := by rintro _ _ rfl; rfl
    refine ⟨φ (β i), fun τ => d (E.symm τ) (i (E.symm τ)), ?_, fun τ => ?_, ?_⟩
    · rw [hβ i]
      refine nsum _ _ fun J _ => ?_
      rw [norm_mul]
      exact mul_le_one₀ (nprod _ _ fun s _ => nint _) (norm_nonneg _) (hφ J)
    · have h1 := hdW (E.symm τ) (i (E.symm τ))
      rw [hμ, show e (E.symm τ) = τ from E.apply_symm_apply τ] at h1
      exact h1
    · funext y
      congr 1
      refine Fintype.prod_equiv E _ _ fun s => ?_
      show _ = (eval fun k : Fin N × Fin N => y (E s) k.1 k.2) ((map (Int.castRingHom ℂ_[p])) (d (E.symm (E s)) (i (E.symm (E s)))))
      rw [key _ s (E.symm_apply_apply s)]
      rfl

  · intro hF J
    have key : ∀ F ∈ WeylLatticeDuality.DelW p T N ν, ∃ ψ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
        (∀ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
          ‖ψ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J))‖ ≤ 1) ∧
        ∀ y : T → Matrix (Fin N) (Fin N) ℂ_[p],
          ψ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) = F y := by
      intro F hF
      induction hF using AddSubgroup.closure_induction with
      | mem F hF =>
        obtain ⟨r, f, hr, hf, rfl⟩ := hF
        have hg : ∀ s, f (e s) ∈ Formalism.GradedWeylDivisibility.weyl ℤ N N (le_refl N) (fun r : Fin N => (nu s).rowLen r) := fun s => by
          rw [hμ s]; exact hf (e s)
        choose z hz1 hz2 using fun s => weylExpand N (nu s) (hY s) (hrep s) (f (e s)) (hg s)
        obtain ⟨Ψ, hΨ⟩ := fockFunctional p N nu hY (fun s => f (e s))
        set N0 : Lt → ℚ := fun s => Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => (nu s).rowLen r))
          (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => (nu s).rowLen r)) with hN0
        have hN0ne : ∀ s, ((N0 s : ℚ) : ℂ_[p]) ≠ 0 := fun s => by
          have := ((Formalism.GradedWeylDivisibility.fockQPos _ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => (nu s).rowLen r))
            (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => (nu s).rowLen r))).2 (Formalism.GradedWeylDivisibility.hwNe ℚ N N le_rfl _)).ne'
          exact_mod_cast this
        have hP0 : (∏ s, ((N0 s : ℚ) : ℂ_[p])) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun s _ => hN0ne s
        have hψJ : ∀ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
            Ψ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) =
              (∏ s, (z s (J s) : ℂ_[p])) * ∏ s, ((N0 s : ℚ) : ℂ_[p]) := by
          intro J
          rw [hΨ J, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun s _ => ?_
          rw [hz1 s (J s)]
          push_cast
          rfl
        refine ⟨(r * (∏ s, ((N0 s : ℚ) : ℂ_[p]))⁻¹) • Ψ, fun J => ?_, fun y => ?_⟩
        · rw [LinearMap.smul_apply, hψJ, smul_eq_mul]
          have : r * (∏ s, ((N0 s : ℚ) : ℂ_[p]))⁻¹ * ((∏ s, (z s (J s) : ℂ_[p])) * ∏ s, ((N0 s : ℚ) : ℂ_[p])) =
              r * ∏ s, (z s (J s) : ℂ_[p]) := by
            field_simp
          rw [this, norm_mul]
          exact mul_le_one₀ hr (norm_nonneg _) (nprod _ _ fun s _ => nint _)
        · set ev : Lt → MvPolynomial (Fin N × Fin N) ℤ →+* ℂ_[p] := fun s =>
            (eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)).comp (map (Int.castRingHom ℂ_[p])) with hev
          have hev' : ∀ s P, eval (fun k : Fin N × Fin N => y (e s) k.1 k.2) (map (Int.castRingHom ℂ_[p]) P) = ev s P :=
            fun s P => rfl
          have hfs : ∀ s, ev s (f (e s)) = ∑ j, (z s j : ℂ_[p]) * ev s (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) j) := by
            intro s
            conv_lhs => rw [← hz2 s]
            rw [map_sum]
            exact Finset.sum_congr rfl fun j _ => by rw [map_zsmul, zsmul_eq_mul]
          rw [LinearMap.smul_apply, canExpand p e N nu hY Ψ y, smul_eq_mul]
          simp only [hev', hψJ]
          have h1 : ∀ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
              r * (∏ s, ((N0 s : ℚ) : ℂ_[p]))⁻¹ * (((∏ s, (z s (J s) : ℂ_[p])) * (∏ s, ((N0 s : ℚ) : ℂ_[p]))) *
                ∏ s, ev s (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) (J s))) =
              r * ∏ s, ((z s (J s) : ℂ_[p]) * ev s (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) (J s))) := by
            intro J
            rw [Finset.prod_mul_distrib]
            field_simp
          rw [Finset.mul_sum, Finset.sum_congr rfl fun J _ => h1 J, ← Finset.mul_sum,
            sum_prod_eq (fun s j => (z s j : ℂ_[p]) * ev s (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) j)),
            Finset.prod_congr rfl fun s _ => (hfs s).symm]
          congr 1
          refine Fintype.prod_equiv E _ _ fun s => ?_
          show _ = (eval fun k : Fin N × Fin N => y (E s) k.1 k.2) ((map (Int.castRingHom ℂ_[p])) (f (E s)))
          rfl
      | zero => exact ⟨0, fun J => by simp, fun y => by simp⟩
      | add F G _ _ ihF ihG =>
        obtain ⟨ψ, h1, h2⟩ := ihF
        obtain ⟨ψ', h1', h2'⟩ := ihG
        exact ⟨ψ + ψ', fun J => by
          rw [LinearMap.add_apply]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1 J) (h1' J)),
          fun y => by rw [LinearMap.add_apply, h2, h2', Pi.add_apply]⟩
      | neg F _ ihF =>
        obtain ⟨ψ, h1, h2⟩ := ihF
        exact ⟨-ψ, fun J => by rw [LinearMap.neg_apply, norm_neg]; exact h1 J,
          fun y => by rw [LinearMap.neg_apply, h2, Pi.neg_apply]⟩
    obtain ⟨ψ, hψ1, hψ2⟩ := key _ hF
    have hzero : ∀ y' : Lt → Fin N → ℕ → ℂ_[p], (φ - ψ) (PI.WwInjective.DeX N nu y') = 0 := by
      intro y'
      obtain ⟨y, hy⟩ := deX_trunc e he N nu hY y'
      change (φ - ψ) (WeylLatticeDuality.DeX N nu y') = 0
      rw [hy, LinearMap.sub_apply, hψ2 y, sub_eq_zero]
    have h3 := PI.WwInjectiveWork.wwInjective_of cauchy_binet_minors Lt p N nu (φ - ψ) hzero J
    rw [LinearMap.sub_apply, sub_eq_zero] at h3
    change ‖φ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J))‖ ≤ 1
    rw [show φ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) =
      ψ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) from h3]
    exact hψ1 J

end GlobalTheory.WeylLatDualPf
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_lattice_duality_padic_minors : WeylLatticeDuality.Stmt := by
  atlas_forward_decl GlobalTheory.WeylLatDualPf.stmt_holds
end
