import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfResidueFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSsubIffFlagC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSGIffFlags
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParGMapGlRed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StKHolds

section
noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3 Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MassDataIdxSpl
open scoped TensorProduct

variable {F E R : Type} [Field F] [Field E] [Algebra F E] [Field R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (θ : R ⊗[F] E ≃ₐ[R] R × R)

theorem reindex_mul' {ι : Type} [Fintype ι] [DecidableEq ι] (e : Fin n ≃ ι) (A B : Matrix (Fin n) (Fin n) R) :
    Matrix.reindex e e A * Matrix.reindex e e B = Matrix.reindex e e (A * B) := by
  simp only [Matrix.reindex_apply]
  exact Matrix.submatrix_mul_equiv A B e.symm e.symm e.symm

private theorem flagC_reindex_iff {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] {m : ℕ}
    (e : Fin n ≃ ι) (M : Matrix (Fin n) (Fin n) K) (v : Fin m → Fin n → K) :
    FlagC (Matrix.reindex e e M) (fun b => v b ∘ e.symm) ↔ FlagC M v := by
  let f : (Fin n → K) ≃ₗ[K] (ι → K) := LinearEquiv.funCongrLeft K K e.symm
  have hmv : ∀ w : Fin n → K, Matrix.reindex e e M *ᵥ (w ∘ e.symm) = (M *ᵥ w) ∘ e.symm := by
    intro w
    rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    congr 2
    funext j
    simp
  have key : ∀ (x : Fin n → K) (S : Set (Fin n → K)),
      x ∘ e.symm ∈ Submodule.span K ((fun w : Fin n → K => w ∘ e.symm) '' S) ↔ x ∈ Submodule.span K S := by
    intro x S
    have h1 : (fun w : Fin n → K => w ∘ e.symm) = ⇑(f.toLinearMap) := rfl
    rw [h1, Submodule.span_image, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hyx : y = x := f.injective hxy
      exact hyx ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  unfold FlagC
  refine forall_congr' fun b => ?_
  show Matrix.reindex e e M *ᵥ (v b ∘ e.symm) - v b ∘ e.symm ∈
      Submodule.span K ((fun a => v a ∘ e.symm) '' {a | a < b}) ↔ _
  rw [hmv, show (fun a => v a ∘ e.symm) '' {a | a < b} =
      (fun w : Fin n → K => w ∘ e.symm) '' (v '' {a | a < b}) from
      (Set.image_image (fun w : Fin n → K => w ∘ e.symm) v {a | a < b}).symm]
  exact key (M *ᵥ v b - v b) _

theorem mem_Ssub_iff_sG (hθ : ∀ t, θ (sigR R σ t) = (θ t).swap) {r k : ℕ} (e : Fin n ≃ Idx r k)
    (hJ : IsUnit (jm1 J θ).det) (P : Frame E n r) (Q : GL (Idx r k) R) (l : Fin (r + 1) → R)
    (hl : ∀ b, l b ≠ 0)
    (hy1 : ∀ b, ((Q⁻¹ : GL (Idx r k) R) : Matrix (Idx r k) (Idx r k) R) *ᵥ
      (pr1 θ (ratV (F := F) R (F0 P b)) ∘ e.symm) = Pi.single (pe b) 1)
    (hy2 : ∀ b, (Q : Matrix (Idx r k) (Idx r k) R)ᵀ *ᵥ ((Matrix.reindex e e (jm1 J θ))ᵀ *ᵥ
      (pr2 θ (ratV (F := F) R (F0 P b)) ∘ e.symm)) = l b • Pi.single (pf b) 1)
    (g : HA R σ J) (g1 : GL (Idx r k) R)
    (hg1 : (g1 : Matrix (Idx r k) (Idx r k) R) = Matrix.reindex e e (cmp1 σ J θ g)) :
    g ∈ Ssub R σ J P ↔ Q⁻¹ * g1 * Q ∈ sG R r k := by
  rw [mem_Ssub_iff_flagC σ J θ P g]
  have hU : (Matrix.reindex e e (cmp2 σ J θ g))ᵀ * Matrix.reindex e e (jm1 J θ) *
      ((g1 : GL (Idx r k) R) : Matrix (Idx r k) (Idx r k) R) = Matrix.reindex e e (jm1 J θ) := by
    rw [hg1, Matrix.transpose_reindex, reindex_mul', reindex_mul', cmp_unit σ J θ hθ g]
  have hJ' : IsUnit (Matrix.reindex e e (jm1 J θ)).det := by
    rwa [Matrix.det_reindex_self]
  rw [← frame_mem_sG g1 Q _ _ hJ' hU (fun b => pr1 θ (ratV (F := F) R (F0 P b)) ∘ e.symm)
    (fun b => pr2 θ (ratV (F := F) R (F0 P b)) ∘ e.symm) l hl hy1 hy2, hg1]
  exact and_congr (flagC_reindex_iff e _ _).symm (flagC_reindex_iff e _ _).symm

end MassDataIdxStIm
end
end

section
noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3 MassDataIdxRed
open Formalism.DoubleCosetMeasures (IsUpUni)

variable {A B : Type} [CommRing A] [CommRing B] {r k : ℕ}

theorem mem_sG_iff_map (f : A →+* B) (hf : Function.Injective f) (g : GL (Idx r k) A) :
    g ∈ sG A r k ↔ glRed f g ∈ sG B r k := by
  change Par _ (g : Matrix (Idx r k) (Idx r k) A) ↔ Par _ ((glRed f g : GL (Idx r k) B) : Matrix (Idx r k) (Idx r k) B)
  rw [glRed_coe]
  set x : Matrix (Idx r k) (Idx r k) A := (g : Matrix (Idx r k) (Idx r k) A) with hx
  have z0 : ∀ {a : A}, f a = 0 → a = 0 := fun h => hf (by rw [h, map_zero])
  have z1 : ∀ {a : A}, f a = 1 → a = 1 := fun h => hf (by rw [h, map_one])
  constructor
  · intro h
    refine MassDataIdxStImB.par_map f (map_zero f) (map_one f) (fun h hh => ?_) h
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hh.map f
  · rintro ⟨h11, h33, h21, h31, h32, h, _, h22⟩
    have u11 : IsUpUni (b11 x) :=
      ⟨fun i j hij => z0 (h11.1 hij), fun a => z1 (h11.2 a)⟩
    have u33 : IsUpUni (b33 x) :=
      ⟨fun i j hij => z0 (h33.1 hij), fun a => z1 (h33.2 a)⟩
    have v21 : b21 x = 0 := by ext i j; exact z0 (congrFun (congrFun h21 i) j)
    have v31 : b31 x = 0 := by ext i j; exact z0 (congrFun (congrFun h31 i) j)
    have v32 : b32 x = 0 := by ext i j; exact z0 (congrFun (congrFun h32 i) j)
    have v22 : b22 x = midEmb (Matrix.of fun i j => x (wI i) (wI j)) := by
      ext i j
      have e := congrFun (congrFun h22 i) j
      rcases i with i | i <;> rcases j with j | j
      · rfl
      · exact z0 (by simpa [b22, midEmb] using e)
      · exact z0 (by simpa [b22, midEmb] using e)
      · exact z1 (by simpa [b22, midEmb] using e)
    refine ⟨u11, u33, v21, v31, v32, Matrix.of fun i j => x (wI i) (wI j), ?_, v22⟩
    show IsUnit (Matrix.det _)
    rw [← det_shape u11 u33 v21 v31 v32 _ v22, hx]
    exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit

end MassDataIdxStIm
end
end

section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix

section Loc

variable {D : D7} (X : HidaSetting D)

def StAdaptB (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ (e : Fin X.B.I.n ≃ Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p))
      (l : Fin (D.R.rS + 1) → FpX X p), (∀ b, l b ≠ 0) ∧
      (∀ b, ((Q⁻¹ : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
        (pr1 θ (ratV (F := X.B.I.F) (FpX X p) (F0 (frameOf X u) b)) ∘ e.symm) = Pi.single (pe b) 1) ∧
      (∀ b, (Q : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p))ᵀ *ᵥ ((Matrix.reindex e e (jm1 X.B.I.J θ))ᵀ *ᵥ
        (pr2 θ (ratV (F := X.B.I.F) (FpX X p) (F0 (frameOf X u) b)) ∘ e.symm)) = l b • Pi.single (pf b) 1) ∧
      ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
        ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
          (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
            - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
          ∀ x : K, ((glRed (algebraMap (Op X p) (FpX X p)) (ψ x) : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) =
            ((Q⁻¹ : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) * Matrix.reindex e e (cmp1 X.B.I.cm.sig X.B.I.J θ (x : HAp X p)) * (Q : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p))

theorem isUnit_det_split_form (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) :
    IsUnit (jm1 X.B.I.J θ).det := by
  have h := (unit_JR X p).map (th1 X p θ)
  rw [RingHom.map_det] at h
  exact h

theorem stFrameB_of (u : D.what₂.Word) (p : TypX X) (h : StAdaptB X u p) : StFrameB X u p := by
  obtain ⟨θ, hθ, e, Q, l, hl, hy1, hy2, K, hK, ψ, hψ, hker, hred⟩ := h
  refine ⟨K, hK, ψ, hψ, hker, 1, fun x => ?_⟩
  let g1 : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p) :=
    Q * glRed (algebraMap (Op X p) (FpX X p)) (ψ x) * Q⁻¹
  have hg1 : (g1 : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) =
      Matrix.reindex e e (cmp1 X.B.I.cm.sig X.B.I.J θ (x : HAp X p)) := by
    simp only [g1, Units.val_mul, hred x, ← mul_assoc, Units.mul_inv, one_mul]
    rw [mul_assoc, Units.mul_inv, mul_one]
  have hinj : Function.Injective (algebraMap (Op X p) (FpX X p)) := Subtype.val_injective
  rw [MassDataIdxStIm.mem_Ssub_iff_sG X.B.I.cm.sig X.B.I.J θ hθ e (isUnit_det_split_form X p θ) (frameOf X u) Q l hl
    hy1 hy2 (x : HAp X p) g1 hg1, inv_one, one_mul, mul_one,
    MassDataIdxStIm.mem_sG_iff_map _ hinj (ψ x)]
  simp only [g1, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

theorem parabolic_image_of_adapted (u : D.what₂.Word) (p : TypX X) (h : StAdaptB X u p) : ParabolicReductionImage X u p := parabolic_image_of_frame X u p (stFrameB_of X u p h)

end Loc

end MassDataIdxSteps
end
end

section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix

section Loc

variable {D : D7} (X : HidaSetting D)

def reindex₂ (p : TypX X) (Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) : GL (Fin X.B.I.n) (FpX X p) :=
  Units.map (Matrix.reindexAlgEquiv (FpX X p) (FpX X p) (idxEquiv X).symm).toMonoidHom Q

def StLatGLx (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
    (Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) : Prop :=
  ∀ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p →
    ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
      (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
        - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∀ x : K, ((glRed (algebraMap (Op X p) (FpX X p)) (ψ x) : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) :
          Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) =
        ((Q⁻¹ : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) :
          Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) *
          Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ (x : HAp X p)) *
          (Q : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p))

end Loc

def LatCoreX : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p),
    IsSplitEquiv X p θ → ∀ Q, LatBasis X p θ (reindex₂ X p Q) → StLatGLx X p θ Q

section Loc2

variable {D : D7} (X : HidaSetting D)

def StAdaptQ (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ (Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) (l : Fin (D.R.rS + 1) → FpX X p), (∀ b, l b ≠ 0) ∧
      (∀ b, ((Q⁻¹ : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) :
          Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
        (pr1 θ (ratV (F := X.B.I.F) (FpX X p) (F0 (frameOf X u) b)) ∘ (idxEquiv X).symm) = Pi.single (pe b) 1) ∧
      (∀ b, (Q : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p))ᵀ *ᵥ
        ((Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ *ᵥ
          (pr2 θ (ratV (F := X.B.I.F) (FpX X p) (F0 (frameOf X u) b)) ∘ (idxEquiv X).symm)) =
        l b • Pi.single (pf b) 1) ∧
      LatBasis X p θ (reindex₂ X p Q)

theorem stAdaptB_of (hC : LatCoreX) (u : D.what₂.Word) (p : TypX X) (h : StAdaptQ X u p) : StAdaptB X u p := by
  obtain ⟨θ, hθ, Q, l, hl, h1, h2, hL⟩ := h
  have hG := hC X p θ hθ Q hL
  let K : Subgroup (HAp X p) :=
    { carrier := KvX X p
      mul_mem' := by
        intro a b ha hb
        simp only [KvX, Formalism.L2.SG.TypedSets.Kv, Set.mem_setOf_eq] at ha hb ⊢
        exact Subgroup.mul_mem _ ha hb
      one_mem' := by
        simp only [KvX, Formalism.L2.SG.TypedSets.Kv, Set.mem_setOf_eq]
        exact Subgroup.one_mem _
      inv_mem' := by
        intro a ha
        simp only [KvX, Formalism.L2.SG.TypedSets.Kv, Set.mem_setOf_eq] at ha ⊢
        exact Subgroup.inv_mem _ ha }
  obtain ⟨ψ, hψs, hψ1, hψ2⟩ := hG K rfl
  exact ⟨θ, hθ, idxEquiv X, Q, l, hl, h1, h2, K, rfl, ψ, hψs, hψ1, hψ2⟩

theorem parabolic_image_of_basis_adapted (hC : LatCoreX) (u : D.what₂.Word) (p : TypX X) (h : StAdaptQ X u p) :
    ParabolicReductionImage X u p :=
  parabolic_image_of_adapted X u p (stAdaptB_of X hC u p h)

end Loc2

end MassDataIdxSteps
end
end
