import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainFrameSignatureDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsLeSpanProdMaximalMinors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSFockColumnSubstitutionUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalBasePtTopMinors
import Formalism.LocalToGlobal.Columns.PolyFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionRenaming
import ReciprocityTheory.DualLattices.FischerSelfNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluckerMinorsProportional

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.MinorFrame

open MvPolynomial

theorem colSub_totalDegree_le {ι : Type} [Fintype ι] {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    (colSub g P).totalDegree ≤ P.totalDegree := by
  classical
  unfold colSub
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add]
  refine le_trans ?_ (le_totalDegree hs)
  unfold Finsupp.prod Finsupp.sum
  refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (totalDegree_pow _ _).trans ?_
  have h1 : (∑ j' : Fin a, C (g i.1 j' i.2.2) * (X (i.1, i.2.1, j') : Pol ι d a)).totalDegree ≤ 1 :=
    totalDegree_finsetSum_le fun j _ => (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])
  calc s i * _ ≤ s i * 1 := Nat.mul_le_mul_left _ h1
    _ = s i := mul_one _

theorem star_detChar_mul_detChar {ι : Type} [Fintype ι] {a : ℕ} (n : ι → ℕ) (g : ι → Matrix.unitaryGroup (Fin a) ℂ) :
    starRingEnd ℂ (detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ))) *
      detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) = 1 := by
  unfold detChar
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [map_pow, ← mul_pow]
  have h : starRingEnd ℂ (g τ : Matrix (Fin a) (Fin a) ℂ).det * (g τ : Matrix (Fin a) (Fin a) ℂ).det = 1 := by
    rw [starRingEnd_apply, ← Matrix.det_conjTranspose, ← Matrix.det_mul, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.1 (g τ).2,
      Matrix.det_one]
  rw [h, one_pow]

@[reducible] def fockCore {σ : Type} (S : Submodule ℂ (MvPolynomial σ ℂ)) : InnerProductSpace.Core ℂ S where
  inner x y := Formalism.L2.DIV.fockS x.1 y.1
  conj_inner_symm x y := (fockS_conj x.1 y.1).symm
  re_inner_nonneg x := by
    by_cases hx : x.1 = 0
    · simp [hx, Formalism.L2.DIV.fockS]
    · exact (fockS_self_re_pos hx).le
  add_left x y z := by
    show Formalism.L2.DIV.fockS (x.1 + y.1) z.1 = _
    rw [← Formalism.L2.DIV.fockL_apply, LinearMap.map_add₂]
    rfl
  smul_left x y r := by
    show Formalism.L2.DIV.fockS (r • x.1) y.1 = _
    rw [← Formalism.L2.DIV.fockL_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul]
    rfl
  definite x hx := by
    by_contra h
    have h' : x.1 ≠ 0 := fun e => h (Subtype.ext e)
    have := fockS_self_re_pos h'
    rw [show Formalism.L2.DIV.fockS x.1 x.1 = 0 from hx] at this
    simp at this

theorem exists_mem_inv_eq_of_twisted : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] Pr),
    (∀ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P) →
    ∀ P : GlobalTheory.MinorFrame.Pol ι d a, ∃ P₀ ∈ GlobalTheory.MinorFrame.inv (ι := ι) a d n, q P = q P₀ := by
  intro ι _ a d n Pr _ _ q hq P
  classical
  let S : Submodule ℂ (Pol ι d a) := restrictTotalDegree (Var ι d a) ℂ P.totalDegree
  haveI : FiniteDimensional ℂ S :=
    inferInstanceAs (Module.Finite ℂ (restrictTotalDegree (Var ι d a) ℂ P.totalDegree))
  letI : InnerProductSpace.Core ℂ S := fockCore S
  letI : NormedAddCommGroup S := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore _
  have hmemS : ∀ (g : ι → Matrix (Fin a) (Fin a) ℂ) (x : Pol ι d a), x ∈ S → colSub g x ∈ S := fun g x hx =>
    (mem_restrictTotalDegree _ _ _).2 ((colSub_totalDegree_le g x).trans ((mem_restrictTotalDegree _ _ _).1 hx))
  let gen : Set S := {w | ∃ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (x : S),
      (w : Pol ι d a) = colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) x.1 -
        detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • x.1}
  let K : Submodule ℂ S := Submodule.span ℂ gen
  have hK : ∀ w ∈ K, q (w : Pol ι d a) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, y, hy⟩ := hx
      rw [hy, map_sub, map_smul, hq, sub_self]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  have hPS : P ∈ S := (mem_restrictTotalDegree _ _ _).2 le_rfl
  obtain ⟨y, hy, z, hz, hyz⟩ := K.exists_add_mem_mem_orthogonal (⟨P, hPS⟩ : S)
  refine ⟨z.1, ?_, ?_⟩
  · intro g
    set G := colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) z.1 with hG
    set c := detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) with hc
    let w : S := ⟨G - c • z.1, S.sub_mem (hmemS _ _ z.2) (S.smul_mem c z.2)⟩
    have hw : w ∈ K := Submodule.subset_span ⟨g, z, rfl⟩
    have h1 : Formalism.L2.DIV.fockL z.1 (G - c • z.1) = 0 := Submodule.inner_left_of_mem_orthogonal hw hz
    have h2 : Formalism.L2.DIV.fockL (G - c • z.1) z.1 = 0 := Submodule.inner_right_of_mem_orthogonal hw hz
    have hinv : Formalism.L2.DIV.fockL G G = Formalism.L2.DIV.fockL z.1 z.1 := by
      rw [Formalism.L2.DIV.fockL_apply, Formalism.L2.DIV.fockL_apply, hG, fockS_colSub_unitary]
    have hcc := star_detChar_mul_detChar n g
    rw [← hc] at hcc
    have e1 : Formalism.L2.DIV.fockL (G - c • z.1) (G - c • z.1) =
        Formalism.L2.DIV.fockL (G - c • z.1) G - c * Formalism.L2.DIV.fockL (G - c • z.1) z.1 := by
      rw [map_sub, map_smul, smul_eq_mul]
    have e2 : Formalism.L2.DIV.fockL (G - c • z.1) G =
        Formalism.L2.DIV.fockL G G - starRingEnd ℂ c * Formalism.L2.DIV.fockL z.1 G := by
      rw [LinearMap.map_sub₂, LinearMap.map_smulₛₗ₂, smul_eq_mul]
    have h1' : Formalism.L2.DIV.fockL z.1 G - c * Formalism.L2.DIV.fockL z.1 z.1 = 0 := by
      rw [← h1, map_sub, map_smul, smul_eq_mul]
    have hWW : Formalism.L2.DIV.fockL (G - c • z.1) (G - c • z.1) = 0 := by
      linear_combination e1 + e2 - c * h2 + hinv - starRingEnd ℂ c * h1' - Formalism.L2.DIV.fockL z.1 z.1 * hcc
    by_contra hne
    have hne' : G - c • z.1 ≠ 0 := sub_ne_zero.2 hne
    have := fockS_self_re_pos hne'
    rw [← Formalism.L2.DIV.fockL_apply, hWW] at this
    simp at this
  · have hP : P = y.1 + z.1 := congrArg Subtype.val hyz
    rw [hP, map_add, hK y hy, zero_add]

end GlobalTheory.MinorFrame
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_detCharInvariant_same_value_twisted : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] Pr),
    (∀ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P) →
    ∀ P : GlobalTheory.MinorFrame.Pol ι d a, ∃ P₀ ∈ GlobalTheory.MinorFrame.inv (ι := ι) a d n, q P = q P₀ := by
  atlas_forward_decl GlobalTheory.MinorFrame.exists_mem_inv_eq_of_twisted
end

section
open Classical

noncomputable section

namespace GlobalTheory.MinorFrame

open MvPolynomial

variable {ι : Type} [Fintype ι]

def genColSub (d a : ℕ) : Pol ι d a →ₐ[ℂ] MvPolynomial (Var ι d a) (MvPolynomial (ι × Fin a × Fin a) ℂ) :=
  aeval fun y => ∑ j' : Fin a, C (X (y.1, j', y.2.2)) * X (y.1, y.2.1, j')

theorem map_eval_genColSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    map (eval fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2) (genColSub d a P) = colSub g P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [genColSub, colSub, algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p y hp =>
    simp only [map_mul, hp]
    simp [genColSub, colSub, map_sum]

def genDetChar (a : ℕ) (n : ι → ℕ) : MvPolynomial (ι × Fin a × Fin a) ℂ :=
  ∏ τ, (Matrix.of fun i j => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)).det ^ n τ

theorem eval_genDetChar {a : ℕ} (n : ι → ℕ) (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    eval (fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2) (genDetChar a n) = detChar n g := by
  rw [genDetChar, map_prod, detChar]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext i j
  simp

theorem colSub_eq_detChar_smul_of_mem_inv {a d : ℕ} (n : ι → ℕ) (P : Pol ι d a) (hP : P ∈ inv a d n)
    (g : ι → Matrix (Fin a) (Fin a) ℂ) : colSub g P = detChar n g • P := by
  set D : MvPolynomial (Var ι d a) (MvPolynomial (ι × Fin a × Fin a) ℂ) :=
    genColSub d a P - C (genDetChar a n) * map C P with hDdef
  have hD : ∀ g : ι → Matrix (Fin a) (Fin a) ℂ,
      map (eval fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2) D = colSub g P - detChar n g • P := by
    intro g
    rw [hDdef, map_sub, map_mul, map_C, map_eval_genColSub, eval_genDetChar, map_map, smul_eq_C_mul]
    congr 2
    have : (eval fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2).comp (C : ℂ →+* MvPolynomial (ι × Fin a × Fin a) ℂ) =
        RingHom.id ℂ := by ext; simp
    rw [this, map_id]
  have hD0 : D = 0 := by
    refine MvPolynomial.ext _ _ fun m => ?_
    rw [coeff_zero]
    refine Formalism.L2.Col.eq_zero_of_forall_unitary (ι := ι) (n := a) (fun _ => 1) (fun _ => by simp) _ fun u hu => ?_
    simp only [Matrix.one_mul]
    rw [← coeff_map, hD u]
    have hu' : ∀ τ, u τ ∈ Matrix.unitaryGroup (Fin a) ℂ := fun τ =>
      Matrix.mem_unitaryGroup_iff'.mpr (by simpa [Matrix.star_eq_conjTranspose] using hu τ)
    have := hP (fun τ => ⟨u τ, hu' τ⟩)
    simp only at this
    rw [this, sub_self, coeff_zero]
  have := hD g
  rw [hD0, _root_.map_zero] at this
  exact (sub_eq_zero.mp this.symm)

end GlobalTheory.MinorFrame
end
end

section
open Classical

noncomputable section

open MvPolynomial Matrix

namespace GlobalTheory.MinorFrame.FockRowSub

variable {ι : Type} [Fintype ι] {a d : ℕ}

def rowEquiv (ι : Type) [Fintype ι] (d : ℕ) : Fin d × ι ≃ Fin (Fintype.card (Fin d × ι)) :=
  Fintype.equivFin _

def varFlat (ι : Type) [Fintype ι] (d a : ℕ) : Var ι d a → Fin (Fintype.card (Fin d × ι)) × Fin a :=
  fun y => (rowEquiv ι d (y.2.1, y.1), y.2.2)

theorem varFlat_injective : Function.Injective (varFlat ι d a) := by
  intro y z h
  simp only [varFlat, Prod.mk.injEq] at h
  have h1 := (rowEquiv ι d).injective h.1
  simp only [Prod.mk.injEq] at h1
  exact Prod.ext h1.2 (Prod.ext h1.1 h.2)

def bigMat (κ : ι → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (Fintype.card (Fin d × ι))) (Fin (Fintype.card (Fin d × ι))) ℂ :=
  (blockDiagonal κ).submatrix (rowEquiv ι d).symm (rowEquiv ι d).symm

theorem rename_rowSub (κ : ι → Matrix (Fin d) (Fin d) ℂ) (P : Pol ι d a) :
    rename (varFlat ι d a) (rowSub κ P) = ReciprocityTheory.PGsh.rowSubst (bigMat κ) (rename (varFlat ι d a) P) := by
  have key : (rename (varFlat ι d a)).comp (rowSub κ) =
      (ReciprocityTheory.PGsh.rowSubst (bigMat κ)).comp (rename (varFlat ι d a)) := by
    refine MvPolynomial.algHom_ext fun y => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, rowSub, aeval_X, rename_X, ReciprocityTheory.PGsh.rowSubst_X,
      ← (rowEquiv ι d).sum_comp, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single y.1]
    · simp only [map_sum, map_mul, rename_C, rename_X, bigMat, submatrix_apply, varFlat, Equiv.symm_apply_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [blockDiagonal_apply_eq]
    · intro τ _ hτ
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [bigMat, varFlat, blockDiagonal_apply_ne _ _ _ hτ]
    · simp
  exact congrArg (fun f => f P) key

theorem bigMat_conjTranspose_mul (κ : ι → Matrix.unitaryGroup (Fin d) ℂ) :
    (bigMat fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ))ᴴ * bigMat (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) = 1 := by
  rw [bigMat, conjTranspose_submatrix, submatrix_mul_equiv, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
  have h : ∀ τ, (κ τ : Matrix (Fin d) (Fin d) ℂ)ᴴ * (κ τ : Matrix (Fin d) (Fin d) ℂ) = 1 := fun τ => by
    have := (κ τ).2
    rw [Matrix.mem_unitaryGroup_iff'] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  simp only [h]
  rw [show (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) = (1 : ι → Matrix (Fin d) (Fin d) ℂ) from rfl,
    blockDiagonal_one, submatrix_one_equiv]

theorem fockS_eq_fischer {ν : ℕ} {κ : Type} (f g : MvPolynomial (Fin ν × κ) ℂ) :
    Formalism.L2.DIV.fockS f g = ReciprocityTheory.PGsh.fischer g f := by
  rw [Formalism.L2.DIV.fockS_eq_sum f g (g.support ∪ f.support) Finset.subset_union_right, ReciprocityTheory.PGsh.fischer]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Formalism.L2.DIV.mfact, Finsupp.prod, RCLike.star_def]
  ring

end GlobalTheory.MinorFrame.FockRowSub

namespace GlobalTheory.MinorFrame

open FockRowSub

theorem fockS_rowSub_unitary {ι : Type} [Fintype ι] (a d : ℕ) (κ : ι → Matrix.unitaryGroup (Fin d) ℂ)
    (P Q : Pol ι d a) :
    Formalism.L2.DIV.fockS (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P)
      (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) Q) = Formalism.L2.DIV.fockS P Q := by
  rw [← GlobalTheory.Proof.ColumnInclusionRenaming.fockS_rename varFlat_injective, rename_rowSub, rename_rowSub, fockS_eq_fischer,
    ReciprocityTheory.PGsh.fischer_rowSubst, ReciprocityTheory.PGsh.rowSubst_mul, bigMat_conjTranspose_mul, ReciprocityTheory.PGsh.rowSubst_one,
    ← fockS_eq_fischer, GlobalTheory.Proof.ColumnInclusionRenaming.fockS_rename varFlat_injective]

end GlobalTheory.MinorFrame
end
end

section
section
noncomputable section
open MvPolynomial
namespace GlobalTheory.MinorFrame.RowIrr
open GlobalTheory.MinorFrame
variable {ι : Type} [Fintype ι]

theorem exists_unitary_eval_ne {a d : ℕ} (h : a ≤ d) (P : Pol ι d a) (hP : P ≠ 0) :
    ∃ κ : ι → Matrix.unitaryGroup (Fin d) ℂ,
      eval (basePt ι d a) (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P) ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hP
  let f : Var ι d a → MvPolynomial (ι × Fin d × Fin d) ℂ := fun y => X (y.1, Fin.castLE h y.2.2, y.2.1)
  have key : ∀ (Q : Pol ι d a) (w : ι × Fin d × Fin d → ℂ),
      eval w (aeval f Q) = eval (fun y => eval w (f y)) Q := by
    intro Q w
    induction Q using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p y hp => simp only [map_mul, hp, aeval_X, eval_X]
  have hF0 : aeval f P = 0 := by
    refine Formalism.L2.Col.eq_zero_of_forall_unitary (ι := ι) (n := d) (fun _ => 1) (fun _ => by simp) _ fun u hu => ?_
    simp only [Matrix.one_mul]
    rw [key]
    have hu' : ∀ τ, u τ ∈ Matrix.unitaryGroup (Fin d) ℂ := fun τ =>
      Matrix.mem_unitaryGroup_iff'.mpr (by simpa [Matrix.star_eq_conjTranspose] using hu τ)
    have := hall (fun τ => ⟨u τ, hu' τ⟩)
    rw [eval_rowSub] at this
    refine (congrArg (fun F => eval F P) (funext fun y => ?_)).trans this
    simp only [f, eval_X]
    rw [Finset.sum_eq_single (Fin.castLE h y.2.2)]
    · simp [basePt]
    · intro b _ hb
      have : (b : ℕ) ≠ (y.2.2 : ℕ) := fun e => hb (Fin.ext (by simpa using e))
      simp [basePt, this]
    · simp
  refine MvPolynomial.funext fun z => ?_
  let w : ι × Fin d × Fin d → ℂ := fun x => if hr : (x.2.1 : ℕ) < a then z (x.1, x.2.2, ⟨x.2.1, hr⟩) else 0
  have := key P w
  rw [hF0, map_zero] at this
  rw [map_zero, this]
  exact congrArg (fun F => eval F P) (funext fun y => by simp [f, w])

theorem rowSub_lowScal_X {d a : ℕ} (t : ℂ) (y : Var ι d a) :
    (∑ i' : Fin d, C (lowScal d a t i' y.2.1) * (X (y.1, i', y.2.2) : Pol ι d a)) =
      C (if (y.2.1 : ℕ) < a then 1 else t) * X y := by
  obtain ⟨τ, i, j⟩ := y
  rw [Finset.sum_eq_single i]
  · simp [lowScal]
  · intro b _ hb
    simp [lowScal, Matrix.diagonal_apply_ne _ hb]
  · simp

def lowDeg {d a : ℕ} (s : Var ι d a →₀ ℕ) : ℕ := s.sum fun y e => if (y.2.1 : ℕ) < a then 0 else e

theorem rowSub_lowScal_monomial {d a : ℕ} (t : ℂ) (s : Var ι d a →₀ ℕ) (c : ℂ) :
    rowSub (fun _ => lowScal d a t) (monomial s c : Pol ι d a) = monomial s (c * t ^ lowDeg s) := by
  unfold rowSub
  rw [aeval_monomial]
  simp only [rowSub_lowScal_X, mul_pow, Finsupp.prod_mul]
  have h1 : (s.prod fun y k => (C (if (y.2.1 : ℕ) < a then 1 else t) : Pol ι d a) ^ k) = C (t ^ lowDeg s) := by
    unfold Finsupp.prod lowDeg Finsupp.sum
    rw [← Finset.prod_pow_eq_pow_sum, map_prod]
    refine Finset.prod_congr rfl fun y _ => ?_
    beta_reduce
    split_ifs <;> simp
  rw [h1, ← monomial_eq, algebraMap_eq, C_mul_monomial]

theorem lowDeg_le {d a : ℕ} (s : Var ι d a →₀ ℕ) : lowDeg s ≤ s.sum fun _ e => e := by
  unfold lowDeg Finsupp.sum
  exact Finset.sum_le_sum fun y _ => by beta_reduce; split_ifs <;> omega

theorem lowScal_mem_unitary {d a : ℕ} {t : ℂ} (ht : ‖t‖ = 1) : lowScal d a t ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [lowScal, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [Pi.mul_apply, Pi.star_apply]
  by_cases hi : (i : ℕ) < a
  · simp [hi]
  · simp only [hi, if_false, RCLike.star_def]
    rw [Complex.conj_mul', ht]; simp

theorem rowSub_lowScal_zero_mem {a d : ℕ} (S : Submodule ℂ (Pol ι d a))
    (hS : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ S, rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P ∈ S)
    (P : Pol ι d a) (hP : P ∈ S) : rowSub (fun _ => lowScal d a 0) P ∈ S := by
  set M := P.totalDegree + 1 with hMdef
  have hM : M ≠ 0 := by omega
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / M)
  have hω : IsPrimitiveRoot ω M := Complex.isPrimitiveRoot_exp M hM
  have hωn : ∀ k : ℕ, ‖ω ^ k‖ = 1 := fun k => by rw [norm_pow, hω.norm'_eq_one hM, one_pow]
  have heq : rowSub (fun _ => lowScal d a 0) P =
      ∑ k ∈ Finset.range M, (M : ℂ)⁻¹ • rowSub (fun _ => lowScal d a (ω ^ k)) P := by
    conv_lhs => rw [as_sum P]
    conv_rhs => rw [as_sum P]
    simp only [map_sum, rowSub_lowScal_monomial, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.sum_congr rfl (fun x _ => by rw [smul_monomial]), ← map_sum]
    congr 1
    have hb : lowDeg s < M := lt_of_le_of_lt (lowDeg_le s) (by have := le_totalDegree hs; omega)
    have hx : ∀ x : ℕ, (ω ^ x) ^ lowDeg s = (ω ^ lowDeg s) ^ x := fun x => by rw [← pow_mul, ← pow_mul, mul_comm]
    simp_rw [hx, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM
    by_cases hb0 : lowDeg s = 0
    · simp only [hb0, pow_zero, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      field_simp
    · have hne : ω ^ lowDeg s ≠ 1 := hω.pow_ne_one_of_pos_of_lt hb0 hb
      rw [geom_sum_eq hne, show (ω ^ lowDeg s) ^ M = 1 by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow],
        sub_self, zero_div, zero_pow hb0]
      simp
  rw [heq]
  refine S.sum_mem fun k _ => S.smul_mem _ ?_
  exact hS (fun _ => ⟨lowScal d a (ω ^ k), lowScal_mem_unitary (hωn k)⟩) P hP

theorem rowSub_lowScal_zero_of_mem_inv {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) (P : Pol ι d a) (hP : P ∈ inv a d n) :
    rowSub (fun _ => lowScal d a 0) P = eval (basePt ι d a) P • topMinors h n := by
  refine MvPolynomial.funext fun z => ?_
  let g : ι → Matrix (Fin a) (Fin a) ℂ := fun τ => Matrix.of fun i j => z (τ, Fin.castLE h i, j)
  have hc := congrArg (eval (basePt ι d a)) (colSub_eq_detChar_smul_of_mem_inv n P hP g)
  rw [eval_colSub, smul_eq_C_mul, map_mul, eval_C] at hc
  have hv : eval z (topMinors h n) = detChar n g := by
    have hm : ∀ τ, (RingHom.mapMatrix (eval z))
        (Matrix.of fun i i' : Fin a => (X (τ, (topRows h).1 i, i') : Pol ι d a)) = g τ := fun τ => by
      ext i j; simp [g, topRows]
    simp only [topMinors, prodMinors, minorAt, map_prod, map_pow, RingHom.map_det, hm, detChar, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hpt : (fun y : Var ι d a => ∑ i' : Fin d, lowScal d a 0 i' y.2.1 * z (y.1, i', y.2.2)) =
      fun y => ∑ j' : Fin a, g y.1 j' y.2.2 * basePt ι d a (y.1, y.2.1, j') := by
    funext y
    rw [Finset.sum_eq_single y.2.1 (fun b _ hb => by simp [lowScal, Matrix.diagonal_apply_ne _ hb]) (by simp)]
    by_cases hy : (y.2.1 : ℕ) < a
    · rw [Finset.sum_eq_single ⟨y.2.1, hy⟩]
      · simp [lowScal, hy, g, basePt]
      · intro b _ hb
        have : (y.2.1 : ℕ) ≠ (b : ℕ) := fun e => hb (Fin.ext e.symm)
        simp [basePt, this]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [lowScal, hy]
      · intro b _
        have : (y.2.1 : ℕ) ≠ (b : ℕ) := fun e => hy (e ▸ b.2)
        simp [basePt, this]
  rw [eval_rowSub, hpt, hc, smul_eq_C_mul, map_mul, eval_C, hv, mul_comm]

theorem exists_fockS_orth {σ : Type} (V N : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ V] (hNV : N < V) :
    ∃ Q ∈ V, Q ≠ 0 ∧ ∀ P ∈ N, Formalism.L2.DIV.fockS P Q = 0 := by
  classical
  haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le hNV.le
  have hlt : Module.finrank ℂ N < Module.finrank ℂ V := Submodule.finrank_lt_finrank_of_lt hNV
  let b := Module.finBasis ℂ N
  let L : V →ₗ[ℂ] (Fin (Module.finrank ℂ N) → ℂ) :=
    LinearMap.pi fun i => (Formalism.L2.DIV.fockL ((b i : N) : MvPolynomial σ ℂ)).comp V.subtype
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hlt)
  obtain ⟨Q, hQ, hQ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨Q, Q.2, fun h => hQ0 (Subtype.ext h), fun P hP => ?_⟩
  have hQi : ∀ i, Formalism.L2.DIV.fockS ((b i : N) : MvPolynomial σ ℂ) Q = 0 := fun i => by
    have := congrFun (LinearMap.mem_ker.mp hQ) i
    simpa [L, Formalism.L2.DIV.fockL_apply] using this
  have hsum := b.sum_repr ⟨P, hP⟩
  have hPe : P = ∑ i, (b.repr ⟨P, hP⟩ i) • ((b i : N) : MvPolynomial σ ℂ) := by
    have := congrArg Subtype.val hsum
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    exact this.symm
  rw [hPe, ← Formalism.L2.DIV.fockL_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, Formalism.L2.DIV.fockL_apply, hQi i, smul_zero]

theorem inv_finiteDimensional (a d : ℕ) (n : ι → ℕ) : FiniteDimensional ℂ (inv (ι := ι) a d n) := by
  classical
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (prodMinors (ι := ι) (a := a) (d := d) (n := n)))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact Submodule.finiteDimensional_of_le (inv_le_span_prodMinors a d n)

theorem topMinors_mem {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) (S : Submodule ℂ (Pol ι d a)) (hSI : S ≤ inv a d n)
    (hS : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ S, rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P ∈ S)
    (hS0 : S ≠ ⊥) : topMinors h n ∈ S := by
  obtain ⟨P, hPS, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  obtain ⟨κ, hκ⟩ := exists_unitary_eval_ne h P hP0
  set P' := rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P
  have h1 : rowSub (fun _ => lowScal d a 0) P' ∈ S := rowSub_lowScal_zero_mem S hS P' (hS κ P hPS)
  rw [rowSub_lowScal_zero_of_mem_inv h n P' (hSI (hS κ P hPS))] at h1
  have := S.smul_mem (eval (basePt ι d a) P')⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hκ, one_smul] at this

end GlobalTheory.MinorFrame.RowIrr

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.MinorFrame.RowIrr

theorem inv_irreducible : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), a ≤ d →
    ∀ N : Submodule ℂ (GlobalTheory.MinorFrame.Pol ι d a), N ≤ GlobalTheory.MinorFrame.inv (ι := ι) a d n →
    (∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ N, GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P ∈ N) →
    N = ⊥ ∨ N = GlobalTheory.MinorFrame.inv (ι := ι) a d n := by
  intro ι _ a d n h N hNI hN
  by_cases hN0 : N = ⊥
  · exact Or.inl hN0
  refine Or.inr ?_
  by_contra hne
  haveI := inv_finiteDimensional (ι := ι) a d n
  obtain ⟨Q, hQI, hQ0, hQN⟩ := exists_fockS_orth (inv a d n) N (lt_of_le_of_ne hNI hne)
  let M : Submodule ℂ (GlobalTheory.MinorFrame.Pol ι d a) :=
    { carrier := {R | R ∈ GlobalTheory.MinorFrame.inv a d n ∧ ∀ P ∈ N, Formalism.L2.DIV.fockS P R = 0}
      add_mem' := fun {R R'} hR hR' => ⟨(GlobalTheory.MinorFrame.inv a d n).add_mem hR.1 hR'.1, fun P hP => by
        rw [← Formalism.L2.DIV.fockL_apply, map_add, Formalism.L2.DIV.fockL_apply, Formalism.L2.DIV.fockL_apply, hR.2 P hP, hR'.2 P hP,
          add_zero]⟩
      zero_mem' := ⟨(GlobalTheory.MinorFrame.inv a d n).zero_mem, fun P _ => by
        rw [← Formalism.L2.DIV.fockL_apply, map_zero]⟩
      smul_mem' := fun c {R} hR => ⟨(GlobalTheory.MinorFrame.inv a d n).smul_mem c hR.1, fun P hP => by
        rw [← Formalism.L2.DIV.fockL_apply, map_smul, Formalism.L2.DIV.fockL_apply, hR.2 P hP, smul_zero]⟩ }
  have hMI : M ≤ GlobalTheory.MinorFrame.inv a d n := fun R hR => hR.1
  have hMs : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ R ∈ M,
      GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) R ∈ M := by
    intro κ R hR
    refine ⟨GlobalTheory.MinorFrame.rowSub_mem_inv _ hR.1, fun P hP => ?_⟩
    have hP' : P = GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ))
        (GlobalTheory.MinorFrame.rowSub (fun τ => ((star (κ τ) : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)) P) := by
      rw [rowSub_rowSub]
      have : (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ) * ((star (κ τ) : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)) =
          fun _ => 1 := by
        funext τ
        exact Unitary.mul_star_self_of_mem (κ τ).2
      rw [this, rowSub_one]
    rw [hP', GlobalTheory.MinorFrame.fockS_rowSub_unitary]
    exact hR.2 _ (hN (fun τ => star (κ τ)) P hP)
  have hM0 : M ≠ ⊥ := by
    intro hM
    apply hQ0
    have : Q ∈ M := ⟨hQI, hQN⟩
    rw [hM] at this
    exact (Submodule.mem_bot ℂ).1 this
  have h1 := topMinors_mem h n N hNI hN hN0
  have h2 := topMinors_mem h n M hMI hMs hM0
  have h3 := h2.2 _ h1
  have := GlobalTheory.MinorFrame.fockS_self_re_pos (topMinors_ne_zero (ι := ι) h n)
  rw [h3] at this
  simp at this

end GlobalTheory.MinorFrame.RowIrr
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockDetCharInvariants_rowSubstitution_irreducible : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), a ≤ d →
    ∀ N : Submodule ℂ (GlobalTheory.MinorFrame.Pol ι d a), N ≤ GlobalTheory.MinorFrame.inv (ι := ι) a d n →
    (∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ N, GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P ∈ N) →
    N = ⊥ ∨ N = GlobalTheory.MinorFrame.inv (ι := ι) a d n := by
  atlas_forward_decl GlobalTheory.MinorFrame.RowIrr.inv_irreducible
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PluckerStar

open MvPolynomial Matrix

variable {a a' : ℕ}

def joinFun (h : a + a' = a + a') (s : {s : Fin a → Fin (a + a') // StrictMono s}) : Fin (a + a') → Fin (a + a') :=
  Fin.addCases (fun i => s.1 i) (fun j => (GlobalTheory.BotMatch.complSub h s).1 j)

theorem joinFun_injective (h : a + a' = a + a') (s : {s : Fin a → Fin (a + a') // StrictMono s}) :
    Function.Injective (joinFun h s) := by
  have hr := GlobalTheory.BotMatch.range_complSub h s
  have hc : ∀ j i, (GlobalTheory.BotMatch.complSub h s).1 j ≠ s.1 i := by
    intro j i e
    have : (GlobalTheory.BotMatch.complSub h s).1 j ∈ Set.range (GlobalTheory.BotMatch.complSub h s).1 := ⟨j, rfl⟩
    rw [hr, e] at this
    exact this ⟨i, rfl⟩
  intro k₁ k₂
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k₁ <;> refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k₂ <;>
    simp only [joinFun, Fin.addCases_left, Fin.addCases_right] <;> intro e
  · rw [s.2.injective e]
  · exact absurd e.symm (hc j' i)
  · exact absurd e (hc j i')
  · rw [(GlobalTheory.BotMatch.complSub h s).2.injective e]

def joinPerm (h : a + a' = a + a') (s : {s : Fin a → Fin (a + a') // StrictMono s}) : Equiv.Perm (Fin (a + a')) :=
  Equiv.ofBijective (joinFun h s) (Finite.injective_iff_bijective.mp (joinFun_injective h s))

theorem joinPerm_castAdd (h : a + a' = a + a') (s : {s : Fin a → Fin (a + a') // StrictMono s}) (i : Fin a) :
    joinPerm h s (Fin.castAdd a' i) = s.1 i := by
  simp [joinPerm, joinFun]

theorem joinPerm_natAdd (h : a + a' = a + a') (s : {s : Fin a → Fin (a + a') // StrictMono s}) (j : Fin a') :
    joinPerm h s (Fin.natAdd a j) = (GlobalTheory.BotMatch.complSub h s).1 j := by
  simp [joinPerm, joinFun]

theorem jacobi (N : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) (hN : N.det ≠ 0) (π : Equiv.Perm (Fin (a + a'))) :
    (Matrix.of fun i i' : Fin a => N⁻¹ (Fin.castAdd a' i') (π (Fin.castAdd a' i))).det =
      ((Equiv.Perm.sign π : ℤ) : ℂ) * (N.det)⁻¹ *
        (Matrix.of fun j j' : Fin a' => N (π (Fin.natAdd a j)) (Fin.natAdd a j')).det := by
  have hU : IsUnit N.det := isUnit_iff_ne_zero.mpr hN
  have h1 : N⁻¹.submatrix id π * N.submatrix π id = 1 := by
    rw [Matrix.submatrix_mul_equiv (e₂ := π) (e₃ := id)]
    simp [Matrix.nonsing_inv_mul _ hU]
  set e := (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a'))
  have h2 : (N⁻¹.submatrix id π).submatrix e e * (N.submatrix π id).submatrix e e = 1 := by
    rw [Matrix.submatrix_mul_equiv (e₂ := e), h1, Matrix.submatrix_one_equiv]
  have h3 := GlobalTheory.det_mul_det_toBlocks₂₂_of_mul_eq_one _ _ h2
  have hd : ((N⁻¹.submatrix id π).submatrix e e).det = ((Equiv.Perm.sign π : ℤ) : ℂ) * (N.det)⁻¹ := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_permute', Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rw [hd] at h3
  have hA : (Matrix.of fun i i' : Fin a => N⁻¹ (Fin.castAdd a' i') (π (Fin.castAdd a' i))) =
      ((N⁻¹.submatrix id π).submatrix e e).toBlocks₁₁.transpose := by
    ext i i'; simp [Matrix.toBlocks₁₁, e]
  have hB : (Matrix.of fun j j' : Fin a' => N (π (Fin.natAdd a j)) (Fin.natAdd a j')) =
      ((N.submatrix π id).submatrix e e).toBlocks₂₂ := by
    ext j j'; simp [Matrix.toBlocks₂₂, e]
  rw [hA, hB, Matrix.det_transpose, ← h3]

variable {ι : Type} [Fintype ι]

theorem eq_zero_of_eval {σ : Type} (Q S : MvPolynomial σ ℂ) (hS : ∃ x, eval x S ≠ 0)
    (h : ∀ x, eval x S ≠ 0 → eval x Q = 0) : Q = 0 := by
  have hQS : Q * S = 0 := MvPolynomial.funext fun x => by
    by_cases hx : eval x S = 0
    · simp [hx]
    · simp [h x hx]
  have hS0 : S ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hS
    simp at hx
  exact (mul_eq_zero.mp hQS).resolve_right hS0

theorem eval_rowSub {d b : ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) (x : ι × Fin d × Fin b → ℂ)
    (P : GlobalTheory.MinorFrame.Pol ι d b) :
    eval x (GlobalTheory.MinorFrame.rowSub κ P) = eval (fun y => ∑ i', κ y.1 i' y.2.1 * x (y.1, i', y.2.2)) P := by
  have : (eval x).comp (GlobalTheory.MinorFrame.rowSub κ : GlobalTheory.MinorFrame.Pol ι d b →ₐ[ℂ] GlobalTheory.MinorFrame.Pol ι d b).toRingHom =
      eval (fun y => ∑ i', κ y.1 i' y.2.1 * x (y.1, i', y.2.2)) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [GlobalTheory.MinorFrame.rowSub]
    · intro y; simp [GlobalTheory.MinorFrame.rowSub]
  exact RingHom.congr_fun this P

def xPt (N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ) : ι × Fin (a + a') × Fin a → ℂ :=
  fun y => (N y.1)⁻¹ (Fin.castAdd a' y.2.2) y.2.1

def yPt (N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ) : ι × Fin (a + a') × Fin a' → ℂ :=
  fun y => N y.1 y.2.1 (Fin.natAdd a y.2.2)

theorem eval_minorAt {d b : ℕ} (x : ι × Fin d × Fin b → ℂ) (τ : ι) (s : Fin b → Fin d) :
    eval x (GlobalTheory.MinorFrame.minorAt τ s) = (Matrix.of fun i i' : Fin b => x (τ, s i, i')).det := by
  rw [GlobalTheory.MinorFrame.minorAt, RingHom.map_det]
  congr 1
  ext i i'
  simp

theorem eval_xPt_minorAt (h : a + a' = a + a') (N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ) (τ : ι)
    (hN : (N τ).det ≠ 0) (s : {s : Fin a → Fin (a + a') // StrictMono s}) :
    eval (xPt N) (GlobalTheory.MinorFrame.minorAt τ s.1) =
      ((Equiv.Perm.sign (joinPerm h s) : ℤ) : ℂ) * ((N τ).det)⁻¹ *
        eval (yPt N) (GlobalTheory.MinorFrame.minorAt τ (GlobalTheory.BotMatch.complSub h s).1) := by
  rw [eval_minorAt, eval_minorAt]
  have := jacobi (N τ) hN (joinPerm h s)
  simp only [joinPerm_castAdd, joinPerm_natAdd] at this
  exact this

def sgn {n : ι → ℕ} (h : a + a' = a + a') (T : GlobalTheory.MinorFrame.Tup ι a (a + a') n) : ℤˣ :=
  ∏ τ, ∏ j, Equiv.Perm.sign (joinPerm h (T τ j))

def cTup {n : ι → ℕ} (h : a + a' = a + a') (T : GlobalTheory.MinorFrame.Tup ι a (a + a') n) : GlobalTheory.MinorFrame.Tup ι a' (a + a') n :=
  fun τ k => GlobalTheory.BotMatch.complSub h (T τ k)

def lam (n : ι → ℕ) (N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ) : ℂ := ∏ τ, ((N τ).det)⁻¹ ^ n τ

theorem eval_xPt_prodMinors {n : ι → ℕ} (h : a + a' = a + a') (N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ)
    (hN : ∀ τ, (N τ).det ≠ 0) (T : GlobalTheory.MinorFrame.Tup ι a (a + a') n) :
    eval (xPt N) (GlobalTheory.MinorFrame.prodMinors T) =
      lam n N * (((sgn h T : ℤˣ) : ℤ) : ℂ) * eval (yPt N) (GlobalTheory.MinorFrame.prodMinors (cTup h T)) := by
  simp only [GlobalTheory.MinorFrame.prodMinors, map_prod, eval_xPt_minorAt h N _ (hN _), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, lam, sgn, cTup, Units.coe_prod, Int.cast_prod]
  ring

def bottomMinors : GlobalTheory.MinorFrame.Pol ι (a + a') a' := ∏ τ, GlobalTheory.MinorFrame.minorAt τ (fun j : Fin a' => Fin.natAdd a j)

theorem eval_bottomMinors (y : ι × Fin (a + a') × Fin a' → ℂ) :
    eval y (bottomMinors (a := a)) = ∏ τ, (Matrix.of fun j j' : Fin a' => y (τ, Fin.natAdd a j, j')).det := by
  simp only [bottomMinors, map_prod, eval_minorAt]

theorem exists_eval_bottomMinors_ne_zero : ∃ y : ι × Fin (a + a') × Fin a' → ℂ, eval y (bottomMinors (a := a)) ≠ 0 := by
  refine ⟨yPt (fun _ => 1), ?_⟩
  rw [eval_bottomMinors, Finset.prod_ne_zero_iff]
  intro τ _
  have : (Matrix.of fun j j' : Fin a' => yPt (a := a) (ι := ι) (fun _ => 1) (τ, Fin.natAdd a j, j')) = 1 := by
    ext j j'
    simp [yPt, Matrix.one_apply]
  rw [this, Matrix.det_one]
  exact one_ne_zero

theorem exists_frame (y : ι × Fin (a + a') × Fin a' → ℂ) (hy : eval y (bottomMinors (a := a)) ≠ 0) :
    ∃ N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ, (∀ τ, (N τ).det ≠ 0) ∧ yPt N = y := by
  rw [eval_bottomMinors, Finset.prod_ne_zero_iff] at hy
  refine ⟨fun τ => (Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) ℂ) (Matrix.of fun i j => y (τ, Fin.castAdd a' i, j)) 0
    (Matrix.of fun i j => y (τ, Fin.natAdd a i, j))).reindex finSumFinEquiv finSumFinEquiv, fun τ => ?_, ?_⟩
  · rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
    exact hy τ (Finset.mem_univ _)
  · funext ⟨τ, k, j⟩
    simp only [yPt, Matrix.reindex_apply, Matrix.submatrix_apply]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp

theorem exists_star (n : ι → ℕ) (h : a + a' = a + a') :
    ∃ Pl : GlobalTheory.MinorFrame.Pol ι (a + a') a →ₗ[ℂ] GlobalTheory.MinorFrame.Pol ι (a + a') a',
      (∀ T : GlobalTheory.MinorFrame.Tup ι a (a + a') n,
        Pl (GlobalTheory.MinorFrame.prodMinors T) = (((sgn h T : ℤˣ) : ℤ) : ℂ) • GlobalTheory.MinorFrame.prodMinors (cTup h T)) ∧
      ∀ (κ : ι → Matrix.unitaryGroup (Fin (a + a')) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := ι) a (a + a') n,
        Pl (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ)) P) =
          (GlobalTheory.MinorFrame.detChar n (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)))⁻¹ •
            GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)) (Pl P) := by
  classical
  let A : (GlobalTheory.MinorFrame.Tup ι a (a + a') n → ℂ) →ₗ[ℂ] GlobalTheory.MinorFrame.Pol ι (a + a') a :=
    Fintype.linearCombination ℂ (fun T => GlobalTheory.MinorFrame.prodMinors T)
  let B : (GlobalTheory.MinorFrame.Tup ι a (a + a') n → ℂ) →ₗ[ℂ] GlobalTheory.MinorFrame.Pol ι (a + a') a' :=
    Fintype.linearCombination ℂ (fun T => (((sgn h T : ℤˣ) : ℤ) : ℂ) • GlobalTheory.MinorFrame.prodMinors (cTup h T))
  have key : ∀ c N, (∀ τ, (N τ).det ≠ 0) → eval (xPt N) (A c) = lam n N * eval (yPt N) (B c) := by
    intro c N hN
    simp only [A, B, Fintype.linearCombination_apply, map_sum, smul_eq_C_mul, eval_mul, eval_C, Finset.mul_sum,
      eval_xPt_prodMinors h N hN]
    refine Finset.sum_congr rfl fun T _ => ?_
    ring
  have hlam : ∀ N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ, (∀ τ, (N τ).det ≠ 0) → lam n N ≠ 0 := by
    intro N hN
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ (inv_ne_zero (hN τ))
  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    apply eq_zero_of_eval _ (bottomMinors (a := a)) exists_eval_bottomMinors_ne_zero
    intro y hy
    obtain ⟨N, hN, rfl⟩ := exists_frame y hy
    have := key c N hN
    rw [hc, map_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (hlam N hN)
  let f : LinearMap.range A →ₗ[ℂ] GlobalTheory.MinorFrame.Pol ι (a + a') a' :=
    ((LinearMap.ker A).liftQ B hker).comp A.quotKerEquivRange.symm.toLinearMap
  obtain ⟨Pl, hPl⟩ := LinearMap.exists_extend f
  have hPlA : ∀ c, Pl (A c) = B c := by
    intro c
    have := LinearMap.congr_fun hPl ⟨A c, LinearMap.mem_range_self A c⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image,
      Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hsingle : ∀ T, A (Pi.single T 1) = GlobalTheory.MinorFrame.prodMinors T := by
    intro T
    simp [A, Fintype.linearCombination_apply_single]
  have hrange : ∀ Q ∈ GlobalTheory.MinorFrame.inv (ι := ι) a (a + a') n, ∃ c, A c = Q := by
    intro Q hQ
    have hle : Submodule.span ℂ (Set.range (GlobalTheory.MinorFrame.prodMinors (ι := ι) (a := a) (d := a + a') (n := n))) ≤
        LinearMap.range A := by
      rw [Submodule.span_le]
      rintro _ ⟨T, rfl⟩
      exact ⟨Pi.single T 1, hsingle T⟩
    exact hle (GlobalTheory.MinorFrame.inv_le_span_prodMinors a (a + a') n hQ)
  refine ⟨Pl, fun T => ?_, fun κ P hP => ?_⟩
  · rw [← hsingle T, hPlA]
    simp [B, Fintype.linearCombination_apply_single]
  · obtain ⟨c, rfl⟩ := hrange P hP
    obtain ⟨c', hc'⟩ := hrange _ (GlobalTheory.MinorFrame.rowSub_mem_inv
      (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ)) hP)
    rw [← hc', hPlA, hPlA, ← sub_eq_zero]
    apply eq_zero_of_eval _ (bottomMinors (a := a)) exists_eval_bottomMinors_ne_zero
    intro y hy
    obtain ⟨N, hN, rfl⟩ := exists_frame y hy
    have hu : ∀ τ, (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)ᵀ *
        (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ) = 1 := by
      intro τ
      have h0 : star (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) * (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) = 1 := (κ τ).2.1
      ext i j
      have := congrArg (fun M : Matrix (Fin (a + a')) (Fin (a + a')) ℂ => M j i) h0
      simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, eq_comm, mul_comm] using this
    have hκ : ∀ τ, (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).det ≠ 0 := by
      intro τ hz
      have := congrArg Matrix.det (hu τ)
      rw [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    let N' : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ :=
      fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)ᵀ * N τ
    have hN' : ∀ τ, (N' τ).det ≠ 0 := by
      intro τ
      simp only [N', Matrix.det_mul, Matrix.det_transpose]
      exact mul_ne_zero (hκ τ) (hN τ)
    have hX : xPt N' = fun y => ∑ i', (κ y.1 : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ) i' y.2.1 *
        xPt N (y.1, i', y.2.2) := by
      funext ⟨τ, k, i⟩
      have hinv : (N' τ)⁻¹ = (N τ)⁻¹ * (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ) := by
        simp only [N']
        rw [Matrix.mul_inv_rev, Matrix.inv_eq_right_inv (hu τ)]
      simp only [xPt, hinv, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun _ _ => ?_
      ring
    have hY : yPt N' = fun y => ∑ i', (κ y.1 : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) i' y.2.1 * yPt N (y.1, i', y.2.2) := by
      funext ⟨τ, k, j⟩
      simp [yPt, N', Matrix.mul_apply]
    have hlam' : lam n N' = lam n N * (GlobalTheory.MinorFrame.detChar n (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)))⁻¹ := by
      simp only [lam, N', GlobalTheory.MinorFrame.detChar, Matrix.det_mul, Matrix.det_transpose, mul_inv, mul_pow,
        Finset.prod_mul_distrib, inv_pow, Finset.prod_inv_distrib]
      ring
    have hX' : ∀ Q, eval (xPt N) (GlobalTheory.MinorFrame.rowSub
        (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ)) Q) = eval (xPt N') Q := by
      intro Q
      rw [eval_rowSub, hX]
    have hY' : ∀ Q, eval (yPt N') Q =
        eval (yPt N) (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)) Q) := by
      intro Q
      rw [eval_rowSub, hY]
    have e1 := key c' N hN
    have e2 := key c N' hN'
    rw [hc', hX', e2, hY', hlam'] at e1
    rw [map_sub, smul_eq_C_mul, eval_mul, eval_C, sub_eq_zero]
    apply mul_left_cancel₀ (hlam N hN)
    rw [← e1]
    ring

end GlobalTheory.PluckerStar

namespace GlobalTheory.BotMatch

theorem minorF_rfl_eq_prodMinors {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : GlobalTheory.NormSum.Tup D a d n) :
    GlobalTheory.BotFormula.minorF rfl rfl T = GlobalTheory.MinorFrame.prodMinors (ι := D.what₂.Tau) T := by
  unfold GlobalTheory.BotFormula.minorF
  have : (fun k : D.what₂.Tau × Fin d × Fin a => (k.1, Fin.cast (rfl : d = d) k.2.1, Fin.cast (rfl : a = a) k.2.2)) = id := by
    funext k
    simp
  rw [this, MvPolynomial.rename_id]
  rfl

theorem complementary_minor_map : ∀ (D : D7) {a a' d : ℕ} (had : a + a' = d) (n : D.what₂.Tau → ℕ),
    ∃ (Pl : PolF D d a →ₗ[ℂ] PolF D d a') (ε : Tup D a d n → ℤˣ),
      (∀ T : Tup D a d n, Pl (GlobalTheory.BotFormula.minorF rfl rfl T) =
        ((ε T : ℤ) : ℂ) • GlobalTheory.BotFormula.minorF rfl rfl (GlobalTheory.BotMatch.complTup D had T)) ∧
      ∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a d n,
        Pl (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) =
          (GlobalTheory.MinorFrame.detChar n (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)))⁻¹ • GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (Pl P) := by
  intro D a a' d had n
  subst had
  obtain ⟨Pl, h1, h2⟩ := GlobalTheory.PluckerStar.exists_star (ι := D.what₂.Tau) n (rfl : a + a' = a + a')
  refine ⟨Pl, fun T => GlobalTheory.PluckerStar.sgn rfl T, fun T => ?_, h2⟩
  rw [minorF_rfl_eq_prodMinors, minorF_rfl_eq_prodMinors]
  exact h1 T

end GlobalTheory.BotMatch
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complementaryMinor_map_realPlaces : ∀ (D : D7) {a a' d : ℕ} (had : a + a' = d) (n : D.what₂.Tau → ℕ),
    ∃ (Pl : PolF D d a →ₗ[ℂ] PolF D d a') (ε : Tup D a d n → ℤˣ),
      (∀ T : Tup D a d n, Pl (GlobalTheory.BotFormula.minorF rfl rfl T) =
        ((ε T : ℤ) : ℂ) • GlobalTheory.BotFormula.minorF rfl rfl (GlobalTheory.BotMatch.complTup D had T)) ∧
      ∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a d n,
        Pl (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) =
          (GlobalTheory.MinorFrame.detChar n (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)))⁻¹ • GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (Pl P) := by
  atlas_forward_decl GlobalTheory.BotMatch.complementary_minor_map
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

theorem GlobalTheory.MinorFrame.exists_unitary_detChar_ne : ∀ {ι : Type} [Fintype ι] (a : ℕ), 0 < a → ∀ n n₀ : ι → ℕ, n ≠ n₀ →
    ∃ g : ι → Matrix.unitaryGroup (Fin a) ℂ, GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) ≠ GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) := by
  intro ι _ a ha n n₀ hne
  classical
  obtain ⟨τ₀, hτ⟩ := Function.ne_iff.mp hne
  have hN : n τ₀ + n₀ τ₀ + 1 ≠ 0 := by omega
  have hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / ((n τ₀ + n₀ τ₀ + 1 : ℕ) : ℂ))) (n τ₀ + n₀ τ₀ + 1) :=
    Complex.isPrimitiveRoot_exp _ hN
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((n τ₀ + n₀ τ₀ + 1 : ℕ) : ℂ)) with hzdef
  have hzn : ‖z‖ = 1 := hz.norm'_eq_one hN
  have hzz : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hzn]; simp
  let d : Fin a → ℂ := Function.update 1 ⟨0, ha⟩ z
  have hU : Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [d, Function.update_apply, Pi.star_apply]
    split_ifs
    · exact hzz
    · simp
  let g : ι → Matrix.unitaryGroup (Fin a) ℂ := fun τ => if τ = τ₀ then ⟨_, hU⟩ else 1
  refine ⟨g, ?_⟩
  have key : ∀ m : ι → ℕ, GlobalTheory.MinorFrame.detChar m (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) = z ^ m τ₀ := by
    intro m
    unfold GlobalTheory.MinorFrame.detChar
    rw [Finset.prod_eq_single τ₀]
    · simp only [g, if_pos rfl, Matrix.det_diagonal, d]
      rw [Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp
    · intro b _ hb
      simp [g, hb]
    · simp
  rw [key, key]
  intro h
  exact hτ (hz.pow_inj (by omega) (by omega) h)
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_detPowCharacter_separates_weights : ∀ {ι : Type} [Fintype ι] (a : ℕ), 0 < a → ∀ n n₀ : ι → ℕ, n ≠ n₀ →
    ∃ g : ι → Matrix.unitaryGroup (Fin a) ℂ, GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) ≠ GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) := by
  atlas_forward_decl GlobalTheory.MinorFrame.exists_unitary_detChar_ne
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SchurQuot

open GlobalTheory.MinorFrame

theorem map_conj_mem_unitaryGroup {d : ℕ} (A : Matrix.unitaryGroup (Fin d) ℂ) :
    (A : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h := Matrix.mem_unitaryGroup_iff.1 A.2
  calc (A : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ) * star ((A : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ))
        = ((A : Matrix (Fin d) (Fin d) ℂ) * star (A : Matrix (Fin d) (Fin d) ℂ)).transpose := by
          ext i j
          simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.star_apply, Matrix.map_apply, RCLike.star_def,
            Complex.conj_conj]
          exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ = 1 := by rw [h, Matrix.transpose_one]

variable {ι : Type} [Fintype ι]

def conjFam {d : ℕ} (κ : ι → Matrix.unitaryGroup (Fin d) ℂ) : ι → Matrix.unitaryGroup (Fin d) ℂ :=
  fun τ => ⟨(κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ), map_conj_mem_unitaryGroup (κ τ)⟩

theorem conjFam_map {d : ℕ} (κ : ι → Matrix.unitaryGroup (Fin d) ℂ) :
    (fun τ => ((conjFam κ τ : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) =
      fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ) := by
  funext τ
  ext i j
  simp [conjFam]

theorem detChar_unitary_ne_zero {d : ℕ} (n : ι → ℕ) (κ : ι → Matrix.unitaryGroup (Fin d) ℂ) :
    detChar n (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) ≠ 0 := by
  unfold detChar
  refine Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.1 (κ τ).2)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact left_ne_zero_of_mul_eq_one h

theorem inv_inf_ker_stable {a d : ℕ} (n₀ : ι → ℕ) {Pr : Type} [AddCommGroup Pr] [Module ℂ Pr]
    (h : Pol ι d a →ₗ[ℂ] Pr) (σ : (ι → Matrix (Fin d) (Fin d) ℂ) → Module.End ℂ Pr)
    (hh : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ inv (ι := ι) a d n₀,
      h (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) = σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (h P))
    (κ : ι → Matrix.unitaryGroup (Fin d) ℂ) :
    ∀ P ∈ inv (ι := ι) a d n₀ ⊓ LinearMap.ker h, rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P ∈ inv (ι := ι) a d n₀ ⊓ LinearMap.ker h := by
  intro P hP
  obtain ⟨hPV, hPk⟩ := Submodule.mem_inf.1 hP
  refine Submodule.mem_inf.2 ⟨rowSub_mem_inv _ hPV, ?_⟩
  rw [LinearMap.mem_ker] at hPk ⊢
  have := hh (conjFam κ) P hPV
  rw [conjFam_map] at this
  rw [this, hPk, map_zero]

end GlobalTheory.SchurQuot

namespace GlobalTheory.SchurQuot

open GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

theorem quot_eq_zero_of_weight_ne {a d : ℕ} (ha : 0 < a) {n n₀ : ι → ℕ} (hn : n ≠ n₀) {Pr : Type} [AddCommGroup Pr]
    [Module ℂ Pr] (q : Pol ι d a →ₗ[ℂ] Pr)
    (hq : ∀ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (P : Pol ι d a),
      q (colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P)
    {P : Pol ι d a} (hP : ∀ g : ι → Matrix (Fin a) (Fin a) ℂ, colSub g P = detChar n g • P) : q P = 0 := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_unitary_detPowCharacter_separates_weights a ha n n₀ hn
  have h1 := hq g P
  rw [hP, map_smul] at h1
  have h2 : (detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) - detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ))) • q P = 0 := by
    rw [sub_smul, h1, sub_self]
  exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hg)

theorem finiteDimensional_inv (a d : ℕ) (n : ι → ℕ) : FiniteDimensional ℂ (inv (ι := ι) a d n) := by
  have hfin : (Set.range (prodMinors (ι := ι) (a := a) (d := d) (n := n))).Finite := Set.finite_range _
  haveI := FiniteDimensional.span_of_finite ℂ hfin
  exact Submodule.finiteDimensional_of_le (GlobalTheory.MinorFrame.inv_le_span_prodMinors a d n)

theorem exists_const_of_equivariant {a d : ℕ} (had : a ≤ d) (n₀ : ι → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q F : Pol ι d a →ₗ[ℂ] Pr) (σ : (ι → Matrix (Fin d) (Fin d) ℂ) → Module.End ℂ Pr) [Nontrivial Pr]
    (hqs : Function.Surjective q)
    (hq : ∀ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (P : Pol ι d a),
      q (colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P)
    (hqσ : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ inv (ι := ι) a d n₀,
      q (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) = σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (q P))
    (hFσ : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ inv (ι := ι) a d n₀,
      F (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) = σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (F P))
    (hF : ∃ P ∈ inv (ι := ι) a d n₀, F P ≠ 0) :
    ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ P ∈ inv (ι := ι) a d n₀, F P = ρ • q P := by
  set V := inv (ι := ι) a d n₀ with hV

  have havg := GlobalTheory.T.exists_detCharInvariant_same_value_twisted a d n₀ Pr q hq
  have hsurj : Function.Surjective (q ∘ₗ V.subtype) := by
    intro x
    obtain ⟨P, rfl⟩ := hqs x
    obtain ⟨P₀, hP₀, he⟩ := havg P
    exact ⟨⟨P₀, hP₀⟩, he.symm⟩

  have hker := GlobalTheory.T.fockDetCharInvariants_rowSubstitution_irreducible a d n₀ had (V ⊓ LinearMap.ker q) inf_le_left
    (inv_inf_ker_stable n₀ q σ hqσ)
  have hinj : Function.Injective (q ∘ₗ V.subtype) := by
    rcases hker with h0 | hV'
    · rw [← LinearMap.ker_eq_bot]
      rw [eq_bot_iff] at h0 ⊢
      intro P hP
      have h' := h0 (Submodule.mem_inf.2 ⟨P.2, hP⟩)
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext ((Submodule.mem_bot ℂ).1 h'))
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (0 : Pr)
      obtain ⟨P, hP⟩ := hsurj x
      have : (P : Pol ι d a) ∈ V ⊓ LinearMap.ker q := by rw [hV']; exact P.2
      exact hx (hP.symm.trans (LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).2))
  let e : V ≃ₗ[ℂ] Pr := LinearEquiv.ofBijective (q ∘ₗ V.subtype) ⟨hinj, hsurj⟩
  haveI : FiniteDimensional ℂ V := finiteDimensional_inv a d n₀
  haveI : Nontrivial V := e.toEquiv.nontrivial
  let E : Module.End ℂ V := e.symm.toLinearMap ∘ₗ F ∘ₗ V.subtype
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue E
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hEv : E v = c • v := hv.apply_eq_smul
  have hFv : F v = c • q v := by
    have h1 : e (E v) = F v := by simp [E]
    have h2 : e (c • v) = c • q v := by rw [map_smul]; rfl
    rw [← h1, hEv, h2]

  have hFc : ∀ (κ : ι → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ V,
      (F - c • q) (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) =
        σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) ((F - c • q) P) := by
    intro κ P hP
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, hFσ κ P hP, hqσ κ P hP]
  have hker2 := GlobalTheory.T.fockDetCharInvariants_rowSubstitution_irreducible a d n₀ had (V ⊓ LinearMap.ker (F - c • q)) inf_le_left
    (inv_inf_ker_stable n₀ (F - c • q) σ hFc)
  have hall : ∀ P ∈ V, F P = c • q P := by
    rcases hker2 with h0 | hV'
    · exfalso
      have : (v : Pol ι d a) ∈ V ⊓ LinearMap.ker (F - c • q) := by
        refine Submodule.mem_inf.2 ⟨v.2, ?_⟩
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero]
        exact hFv
      have h' : (v : Pol ι d a) ∈ (⊥ : Submodule ℂ (Pol ι d a)) := h0 ▸ this
      exact hv.2 (Subtype.ext ((Submodule.mem_bot ℂ).1 h'))
    · intro P hP
      have : P ∈ V ⊓ LinearMap.ker (F - c • q) := by rw [hV']; exact hP
      have := LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).2
      rw [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at this
      exact this
  refine ⟨c, ?_, hall⟩
  rintro rfl
  obtain ⟨P, hP, hFP⟩ := hF
  exact hFP (by rw [hall P hP, zero_smul])

end GlobalTheory.SchurQuot

namespace GlobalTheory.SchurQuot

open GlobalTheory.MinorFrame

theorem minorF_eq_prodMinors (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) :
    GlobalTheory.BotFormula.minorF rfl rfl T = prodMinors (ι := D.what₂.Tau) (n := n) T := by
  unfold GlobalTheory.BotFormula.minorF GlobalTheory.NormSum.minorPol prodMinors minorAt
  rw [show (fun k : D.what₂.Tau × Fin d × Fin a => (k.1, Fin.cast rfl k.2.1, Fin.cast rfl k.2.2)) = id from
    funext fun k => rfl, MvPolynomial.rename_id]
  rfl

theorem quot_minor_eq_const_smul_compl : ∀ (D : D7) {a a' d : ℕ} (had : a + a' = d) (n₀ : D.what₂.Tau → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q : PolF D d a →ₗ[ℂ] Pr) (q' : PolF D d a' →ₗ[ℂ] Pr) (σ : (D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) → Module.End ℂ Pr),
    0 < a → 0 < a' → Nontrivial Pr → Function.Surjective q → Function.Surjective q' →
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin a) ℂ) (P : PolF D d a),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P) →
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin a') ℂ) (P : PolF D d a'),
      q' (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a') (Fin a') ℂ)) P) = GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a') (Fin a') ℂ)) • q' P) →
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a d n₀,
      q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) = σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (q P)) →
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a' d n₀,
      q' (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) • σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (q' P)) →
    ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ (n : D.what₂.Tau → ℕ) (T : Tup D a d n), ∃ ε : ℤˣ,
      q (GlobalTheory.BotFormula.minorF rfl rfl T) = (ρ * ((ε : ℤ) : ℂ)) • q' (GlobalTheory.BotFormula.minorF rfl rfl (GlobalTheory.BotMatch.complTup D had T)) := by
  intro D a a' d had n₀ Pr _ _ q q' σ ha ha' hPr hqs hq's hq hq' hqσ hq'σ
  obtain ⟨Pl, ε, hPlT, hPlκ⟩ := GlobalTheory.T.exists_complementaryMinor_map_realPlaces D had n₀

  have hPlV : ∀ P ∈ inv (ι := D.what₂.Tau) a d n₀, Pl P ∈ inv (ι := D.what₂.Tau) a' d n₀ := by
    intro P hP
    have hle : Submodule.span ℂ (Set.range (prodMinors (ι := D.what₂.Tau) (a := a) (d := d) (n := n₀))) ≤
        (inv (ι := D.what₂.Tau) a' d n₀).comap Pl := by
      rw [Submodule.span_le]
      rintro _ ⟨T, rfl⟩
      show Pl (prodMinors T) ∈ inv (ι := D.what₂.Tau) a' d n₀
      have h := hPlT T
      rw [minorF_eq_prodMinors, minorF_eq_prodMinors] at h
      rw [h]
      exact Submodule.smul_mem _ _ (prodMinors_mem_inv _)
    exact hle (GlobalTheory.MinorFrame.inv_le_span_prodMinors a d n₀ hP)
  let F : PolF D d a →ₗ[ℂ] Pr := q' ∘ₗ Pl
  have hFσ : ∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ inv (ι := D.what₂.Tau) a d n₀,
      F (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) =
        σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (F P) := by
    intro κ P hP
    simp only [F, LinearMap.comp_apply]
    rw [hPlκ κ P hP, map_smul, hq'σ κ (Pl P) (hPlV P hP), smul_smul,
      inv_mul_cancel₀ (detChar_unitary_ne_zero n₀ κ), one_smul]

  have hF : ∃ P ∈ inv (ι := D.what₂.Tau) a d n₀, F P ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨x, hx⟩ := exists_ne (0 : Pr)
    obtain ⟨P', rfl⟩ := hq's x
    obtain ⟨P₀, hP₀, he⟩ := GlobalTheory.T.exists_detCharInvariant_same_value_twisted a' d n₀ Pr q' hq' P'
    apply hx
    rw [he]
    have hle : Submodule.span ℂ (Set.range (prodMinors (ι := D.what₂.Tau) (a := a') (d := d) (n := n₀))) ≤
        LinearMap.ker q' := by
      rw [Submodule.span_le]
      rintro _ ⟨T', rfl⟩
      obtain ⟨T, rfl⟩ := (GlobalTheory.BotMatch.complTup_bijective D had).2 T'
      have h0 := hcon (prodMinors T) (prodMinors_mem_inv T)
      have h := hPlT T
      rw [minorF_eq_prodMinors, minorF_eq_prodMinors] at h
      simp only [F, LinearMap.comp_apply, h, map_smul] at h0
      show q' (prodMinors (GlobalTheory.BotMatch.complTup D had T)) = 0
      have hε : ((ε T : ℤ) : ℂ) ≠ 0 := by
        rcases Int.units_eq_one_or (ε T) with h1 | h1 <;> simp [h1]
      exact (smul_eq_zero.1 h0).resolve_left hε
    exact hle (GlobalTheory.MinorFrame.inv_le_span_prodMinors a' d n₀ hP₀)
  obtain ⟨ρ, hρ, hFq⟩ := exists_const_of_equivariant (by omega) n₀ Pr q F σ hqs hq hqσ hFσ hF
  refine ⟨ρ⁻¹, inv_ne_zero hρ, fun n T => ?_⟩
  by_cases hn : n = n₀
  · subst hn
    refine ⟨ε T, ?_⟩
    have h := hFq (prodMinors T) (prodMinors_mem_inv T)
    have hT := hPlT T
    rw [minorF_eq_prodMinors, minorF_eq_prodMinors] at hT ⊢
    simp only [F, LinearMap.comp_apply, hT, map_smul] at h
    rw [mul_smul, h, smul_smul, inv_mul_cancel₀ hρ, one_smul]
  · refine ⟨1, ?_⟩
    rw [minorF_eq_prodMinors, minorF_eq_prodMinors]
    rw [quot_eq_zero_of_weight_ne ha hn q hq (fun g => colSub_prodMinors g T),
      quot_eq_zero_of_weight_ne ha' hn q' hq' (fun g => colSub_prodMinors g _), smul_zero]

end GlobalTheory.SchurQuot
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realQuotient_minor_eq_const_smul_complementMinor : ∀ (D : D7) {a a' d : ℕ} (had : a + a' = d) (n₀ : D.what₂.Tau → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q : PolF D d a →ₗ[ℂ] Pr) (q' : PolF D d a' →ₗ[ℂ] Pr) (σ : (D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) → Module.End ℂ Pr),
    0 < a → 0 < a' → Nontrivial Pr → Function.Surjective q → Function.Surjective q' →
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin a) ℂ) (P : PolF D d a),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P) →
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin a') ℂ) (P : PolF D d a'),
      q' (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a') (Fin a') ℂ)) P) = GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a') (Fin a') ℂ)) • q' P) →
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a d n₀,
      q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) = σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (q P)) →
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a' d n₀,
      q' (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) • σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (q' P)) →
    ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ (n : D.what₂.Tau → ℕ) (T : Tup D a d n), ∃ ε : ℤˣ,
      q (GlobalTheory.BotFormula.minorF rfl rfl T) = (ρ * ((ε : ℤ) : ℂ)) • q' (GlobalTheory.BotFormula.minorF rfl rfl (GlobalTheory.BotMatch.complTup D had T)) := by
  atlas_forward_decl GlobalTheory.SchurQuot.quot_minor_eq_const_smul_compl
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.BotMatch

theorem real_quot_compl_minor : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (A A' WW : HSp D) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ)
    (had : A.rank + A'.rank = WW.rank),
    (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) →
    (∃ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β ∧ ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
  ∀ (Pr : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr),
    Function.Surjective q → Function.Surjective q' →
    (∀ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
      (∃ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p') ∧
      ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p' →
        ∃ (Pf : ModuleCat.{0} ℂ) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f ∧ r f = x) ∧
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f ∧ r' f = x) ∧
          (∀ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF ψ θ true FA FW f P) = e (q P ⊗ₜ r f)) ∧
          ∀ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f → ∀ P,
            p' (GlobalTheory.SquareComm.fockF ψ θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
    ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ (n : D.what₂.Tau → ℕ) (T : Tup D A.rank WW.rank n), ∃ ε : ℤˣ,
      q (GlobalTheory.BotFormula.minorF rfl rfl T) = (ρ * ((ε : ℤ) : ℂ)) • q' (GlobalTheory.BotFormula.minorF rfl rfl (GlobalTheory.BotMatch.complTup D had T)) := by
  intro h1 h2 h3 h4 D ψ θ θ' hθ A A' WW FA FA' FW a b had hA hA' hW hex Pr q q' hq hq' hm
  obtain ⟨hnt, n₀, σ, i1, i2, i3, i4⟩ :=
    GlobalTheory.T.chain_frame_signature_data h1 h2 h3 h4 D ψ θ θ' hθ A A' WW FA FA' FW a b had hA hA' hW hex Pr q q' hq hq' hm
  obtain ⟨α, β, ht, -⟩ := hex
  obtain ⟨p, r, -, h5, h6⟩ := ht.sig
  exact GlobalTheory.T.realQuotient_minor_eq_const_smul_complementMinor D had n₀ Pr q q' σ (by omega) (by omega) hnt hq hq' i1 i2 i3 i4

end GlobalTheory.BotMatch
end
