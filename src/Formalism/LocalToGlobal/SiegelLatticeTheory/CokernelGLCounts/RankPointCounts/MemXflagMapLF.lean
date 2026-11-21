import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupMUIndep

section
noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

section Sg

variable {K : Type*} [Field K] {r : ℕ}

def Sg (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K := Matrix.diagonal fun b => (-1) ^ (r - b.val)

theorem Sg_mul_Sg : (Sg r : Matrix (Fin (r + 1)) (Fin (r + 1)) K) * Sg r = 1 := by
  rw [Sg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem zhatOM_eq (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ZhatOM Z = Z * Sg r := by
  ext a b
  rw [Sg, Matrix.mul_diagonal]
  show (-1) ^ (r - b.val) * Z a b = _
  ring

theorem upUni_Sg {U : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUpUni U) : IsUpUni (Sg r * U * Sg r) := by
  intro i j
  simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun hji => by rw [(h i j).1 hji]; ring, fun hij => ?_⟩
  subst hij
  rw [(h i i).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]
  simp

end Sg

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem same_cell (F : FlagG S r T) (F1 F2 : FlagG S r T') (hG1 : Gflag F F1 ≠ 0) (hG2 : Gflag F F2 ≠ 0)
    (w : Point E (r + 1)) (h1 : IsInCell (ZhatOM (Zhat F F1)) w) (h2 : IsInCell (ZhatOM (Zhat F F2)) w) :
    ∃ g : S.V ≃ₗ[E] S.V, g ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧
      (∃ M : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni M ∧ ∀ b, g.symm (F.fvec b) = ∑ c, M c b • F.fvec c) ∧
      ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni U ∧ ∀ b, g (∑ c, U c b • F1.fvec c) = F2.fvec b := by
  obtain ⟨L1, U1, hL1, hU1, e1⟩ := h1
  obtain ⟨L2, U2, hL2, hU2, e2⟩ := h2
  rw [zhatOM_eq] at e1 e2
  have hL1d : IsUnit L1.det := by rw [loUni_det hL1]; exact isUnit_one
  have hU1d : IsUnit U1.det := by rw [upUni_det hU1]; exact isUnit_one
  set L := L2 * L1⁻¹ with hL
  set U := Sg r * (U1⁻¹ * U2) * Sg r with hU
  have hLl : IsLoUni L := loUni_mul hL2 (loUni_inv hL1)
  have hUu : IsUpUni U := upUni_Sg (upUni_mul (upUni_inv hU1) hU2)
  have hZ : Zhat F F2 = L * Zhat F F1 * U := by
    have z1 : Zhat F F1 = L1 * ptMat w * U1 * Sg r := by
      rw [← e1, Matrix.mul_assoc, Sg_mul_Sg, Matrix.mul_one]
    have z2 : Zhat F F2 = L2 * ptMat w * U2 * Sg r := by
      rw [← e2, Matrix.mul_assoc, Sg_mul_Sg, Matrix.mul_one]
    rw [z2, z1, hL, hU]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Sg r) (Sg r), Sg_mul_Sg, Matrix.one_mul, ← Matrix.mul_assoc U1 U1⁻¹,
      Matrix.mul_nonsing_inv _ hU1d, Matrix.one_mul, ← Matrix.mul_assoc L1⁻¹ L1,
      Matrix.nonsing_inv_mul _ hL1d, Matrix.one_mul]
  set M := Lᴴ with hM
  have hMu : IsUpUni M := loUni_iff_ct.1 hLl
  have hZ' : Zhat F F2 = Mᴴ * Zhat F F1 * U := by rw [hM, conjTranspose_conjTranspose]; exact hZ
  obtain ⟨g, hg, hgx⟩ := witt_tuple (tupMU F F1 M U) (Sum.elim F.fvec F2.fvec) (tupMU_indep F F1 M U hMu hUu hG1)
    (PI.PairCorankPos.W.linIndep F F2 hG2) (gram_moved F F1 F2 M U hMu hUu hZ')
  refine ⟨g, hg, ⟨M, hMu, fun b => ?_⟩, U, hUu, fun b => hgx (Sum.inr b)⟩
  have := hgx (Sum.inl b)
  simp only [tupMU, Sum.elim_inl] at this
  rw [← this, LinearEquiv.symm_apply_apply]

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem toPts_inj {K : Type} [Zero K] {i : ℕ} (p q : Point K (i + 1)) (h : toPts p = toPts q) : p = q := by
  have key : ∀ r : Point K (i + 1),
      List.ofFn (fun a : Fin (toPts r).1.length =>
        ((toPts r).2 a, (toPts r).1.blocks.get ⟨a.1, a.2⟩)) = r.1 := by
    intro r
    apply List.ext_get
    · simp [toPts, Composition.length]
    · intro n h1 h2
      simp [toPts]
  apply Subtype.ext
  rw [← key p, ← key q, h]

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem at_ptOf (t : TauC Y u u') (hG : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t)) :
    t.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf t.toTerm) := by
  by_cases hex : ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant
  · exact Formalism.L2.SG.PairVal.ptOf_spec _ hex
  · exfalso
    have hj : Formalism.L2.SG.PairVal.ptOf t.toTerm = Formalism.L2.SG.PairVal.junkPoint D u u' := by
      unfold Formalism.L2.SG.PairVal.ptOf
      rw [dif_neg hex]
    have h0 : NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t) = 0 := by
      unfold ptPN
      rw [hj]
      unfold NGPt
      obtain ⟨w0⟩ : Nonempty (InfinitePlace D.host.E) := by
        first | exact inferInstance | infer_instance
      apply Finset.prod_eq_zero (Finset.mem_univ w0)
      rw [GPt_junk]
      first | simp | rw [map_zero, mul_zero]
    linarith

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

section
noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option maxHeartbeats 1600000

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_Xa_mapFlag {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (j : ℕ) (x : S.V) :
    x ∈ (mapFlag γ hγ F).Xa j ↔ γ.symm x ∈ F.Xa j := by
  have h1 : (mapFlag γ hγ F).Xa j = (F.Xa j).map (γ : S.V →ₗ[E] S.V) := by
    unfold FlagG.Xa
    rw [Submodule.map_span, ← Set.image_comp]
    rfl
  rw [h1]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨γ.symm x, h, by simp⟩

theorem mem_Xflag_mapLF {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) (x : S.V) :
    x ∈ Xflag (mapLF γ F) j ↔ γ.symm x ∈ Xflag F j := by
  unfold Xflag mapLF
  rw [dif_pos hγ]
  exact mem_Xa_mapFlag γ hγ F.fl j x

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem NLam_SRat {T : D.host.E} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {F : LFlag (VS D) D.R.rS T}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NLam Λ F) : n ∈ SRat F := by
  obtain ⟨hA, hf, hp⟩ := hn
  refine ⟨hA.1, hf, hp _ ?_⟩
  refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).2 fun x hx => ?_
  rw [hT_swap F.fl.z x, hT_z_X F.fl hx, star_zero]

theorem NLam_transport (t : TauC Y u u') {Λ : Submodule (𝓞 D.host.E) (VS D).V} {m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hm : m ∈ NLam Λ t.frame) : t.lin⁻¹ * m * t.lin ∈ SRat (lf D (X.Fu u')) := by
  have hγ : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hS := NLam_SRat hm
  obtain ⟨hmi, hmf, hmz⟩ := hS
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ) hmi) hγ,
    fun j x hx => ?_, ?_⟩
  · have hx' : t.lin x ∈ Xflag t.frame (j + 1) :=
      (mem_Xflag_mapLF t.lin hγ (lf D (X.Fu u')) (j + 1) _).2 (by rw [LinearEquiv.symm_apply_apply]; exact hx)
    have h := hmf j _ hx'
    have h' := (mem_Xflag_mapLF t.lin hγ (lf D (X.Fu u')) j _).1 h
    rw [map_sub, LinearEquiv.symm_apply_apply] at h'
    exact h'
  · have h2 : m t.frame.fl.z - t.frame.fl.z ∈ t.frame.fl.X := hmz
    have h3 := (mem_frameX Y t _).1 h2
    rw [map_sub, frame_z_eq_lin_zu, LinearEquiv.symm_apply_apply] at h3
    show t.lin.symm (m (t.lin (X.Fu u').z)) - (X.Fu u').z ∈ _
    exact h3

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end
