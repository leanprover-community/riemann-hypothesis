import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.NonLagrangianCosetsBijection
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSecondTerm
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.NonLagrangianCosetsBijectionRank
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FirstOrbitParabolicLeft
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DiscFubiniVolume
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.PaddedMatrixIdentity.Conjpar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PadMatrixLowerBlockZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.GeometricRayBounds
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.UnipotentBlockCornerEmbedded
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.InFrameW1EmSEqOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DifferentialOperatorClasses
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ExistsNeZeroInFrameW1ColumnI0

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq PositivityTheory.SiegelWeilFormula.Act.C5
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
variable (L) in
def sExp_k (e : AE F E) (b : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks 1 (∑ j, (Matrix.single L.i₀ (L.em j) (b j) + Matrix.single (L.em j) L.i₀ (-(e * cA σ (b j))))) 0 1
theorem nq_cM_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) :
    NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b (cM c)) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_frame_k h]
  refine ⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩
  · rcases k with k | k <;>
      simp [Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.single_apply, Matrix.sum_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L]
  · rcases k with k | k <;> rcases l with l | l
    · have hk : k ≠ L.i₀ := fun e => hkx (by rw [e])
      simp [Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.single_apply, Matrix.sum_apply, Ne.symm hk]
    · have hk : k ≠ L.i₀ := fun e => hkx (by rw [e])
      simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.single_apply, Ne.symm hk]
    · simp
    · have hl : l ≠ L.i₀ := fun e => hly (by rw [e])
      simp [Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.single_apply, Matrix.sum_apply, Ne.symm hl]
namespace B
variable (L) in
def sb_k (e : AE F E) (b : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ j, (Matrix.single L.i₀ (L.em j) (b j) + Matrix.single (L.em j) L.i₀ (-(e * cA σ (b j))))
theorem sExp_eq_k (e : AE F E) (b : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b = Matrix.fromBlocks 1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k L e b) 0 1 := rfl
theorem hne_k (j : Fin L.n) : L.em j ≠ L.i₀ := (L.rng (L.em j)).2 ⟨j, rfl⟩
theorem section_base_base_entry (e : AE F E) (b : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k L e b L.i₀ L.i₀ = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k, Matrix.sum_apply, Matrix.single_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k]
theorem section_base_row_entry (e : AE F E) (b : Fin L.n → AE F E) (k : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k L e b L.i₀ (L.em k) = b k := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k, Matrix.sum_apply, Matrix.single_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k, L.inj.eq_iff]
theorem section_entry_row_base (e : AE F E) (b : Fin L.n → AE F E) (k : Fin L.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k L e b (L.em k) L.i₀ = -(e * cA σ (b k)) := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k, Matrix.sum_apply, Matrix.single_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k, L.inj.eq_iff]
theorem sb_em_em_k (e : AE F E) (b : Fin L.n → AE F E) (j k : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k L e b (L.em j) (L.em k) = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k, Matrix.sum_apply, Matrix.single_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k, (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k j).symm, (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k k).symm]
theorem unipotent_base_base_entry (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u L.i₀ L.i₀ = 1 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.sum_apply, Matrix.single_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k]
theorem unipotent_base_row_entry (u : Fin L.n → AE F E) (k : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u L.i₀ (L.em k) = u k := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k, L.inj.eq_iff, Ne.symm (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k k)]
theorem uA_em_em_k (u : Fin L.n → AE F E) (j k : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u (L.em j) (L.em k) = if j = k then 1 else 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k, L.inj.eq_iff, (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k j).symm]
theorem centre_base_base_entry (a : AF F) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a L.i₀ L.i₀ = a • inclR (F := F) (AF F) δ := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k]
theorem centre_base_row_entry (a : AF F) (k : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a L.i₀ (L.em k) = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.single_apply, Ne.symm (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.hne_k k)]
end B
open B in
theorem nq_sExp_k (e : AE F E) (b : Fin L.n → AE F E) : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b) := by
  refine ⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩
  · rcases k with a | a <;> simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sExp_eq_k, Matrix.one_apply]
  · rcases k with a | a <;> rcases l with c | c
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sExp_eq_k, Matrix.one_apply]
    · have ha : a ≠ L.i₀ := fun h => hkx (by rw [h])
      have hc : c ≠ L.i₀ := fun h => hly (by rw [h])
      obtain ⟨j, rfl⟩ := (L.rng a).1 ha
      obtain ⟨k, rfl⟩ := (L.rng c).1 hc
      simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sExp_eq_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_em_em_k]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sExp_eq_k]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sExp_eq_k, Matrix.one_apply]
open B in
theorem U_sExp_k {ε : ℤˣ} (hσ : ∀ a, σ (σ a) = a) (b : Fin L.n → AE F E) :
    M.U (cA σ).toRingHom (((ε : ℤ) : AE F E)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L (((ε : ℤ) : AE F E)) b) := by
  set e : AE F E := ((ε : ℤ) : AE F E) with he
  have hee : e * e = 1 := by rw [he, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hce : cA σ e = e := by rw [he, map_intCast]
  have hcc : ∀ z, cA σ (cA σ z) = z := cA_inv' hσ
  unfold M.U
  show (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b)ᵀ * kunf.jw d.n e * (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b).map (cA σ) = kunf.jw d.n e
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sExp_eq_k, kunf.nmat_form]
  have h0 : e • (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k L e b).map (cA σ) + (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k L e b)ᵀ = 0 := by
    ext p q
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.zero_apply, smul_eq_mul]
    by_cases hp : p = L.i₀
    · subst hp
      by_cases hq : q = L.i₀
      · subst hq; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.section_base_base_entry]
      · obtain ⟨k, rfl⟩ := (L.rng q).1 hq
        rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.section_base_row_entry, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.section_entry_row_base]; ring
    · obtain ⟨j, rfl⟩ := (L.rng p).1 hp
      by_cases hq : q = L.i₀
      · subst hq
        rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.section_entry_row_base, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.section_base_row_entry, map_neg, map_mul, hce, hcc]
        linear_combination (-(b j)) * hee
      · obtain ⟨k, rfl⟩ := (L.rng q).1 hq
        simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_em_em_k]
  rw [h0]
  rfl
theorem delta_par_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {ε : ℤˣ} (hε : kfour.FrameEq σ d.Y d.b ε) :
    σ δ = -(((ε : ℤ) : E) * δ) := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  have hU : M.U (cA σ).toRingHom (((ε : ℤ) : AE F E)) (inFrame d.b (cM (0, 1))) := kunf.frame_eq hε (cM (0, 1))
  have he : (((ε : ℤ) : AE F E)) * (((ε : ℤ) : AE F E)) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hse : (cA σ).toRingHom (((ε : ℤ) : AE F E)) = ((ε : ℤ) : AE F E) := map_intCast _ _
  have hp := M.even_im_hermitian_sub (fun z => cA_inv' hσ z) he hse L.em L.inj L.rng hU (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.nq_cM_k h (0, 1))
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_frame_k h] at hp
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.single_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L, Ne.symm (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L _)] at hp
  apply kfour.inclR_injective (F := F)
  rw [← GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR, map_neg, map_mul, map_intCast]
  simpa using hp
open B in
theorem row_sC_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (e : AE F E) (b u : Fin L.n → AE F E) (a : AF F) :
    (∀ j, (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b * inFrame d.b (cM (u, a))) (Sum.inl L.i₀) (Sum.inl (L.em j)) = u j) ∧
    (∀ j, (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b * inFrame d.b (cM (u, a))) (Sum.inl L.i₀) (Sum.inr (L.em j)) = b j) ∧
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b * inFrame d.b (cM (u, a))) (Sum.inl L.i₀) (Sum.inr L.i₀) =
      a • inclR (F := F) (AF F) δ - ∑ j, b j * cA σ (u j) ∧
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b * inFrame d.b (cM (u, a))) (Sum.inl L.i₀) (Sum.inl L.i₀) = 1 := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_frame_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sExp_eq_k, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add, Matrix.mul_one,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]
  have hs : ∀ q, (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.sb_k L e b * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u))ᵀ.map (cA σ)) L.i₀ q = ∑ k, b k * cA σ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u) q (L.em k)) := by
    intro q
    rw [Matrix.mul_apply, M.sum_split' L.em L.inj L.rng, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.section_base_base_entry, zero_mul, zero_add]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.section_base_row_entry, Matrix.map_apply, Matrix.transpose_apply]
  refine ⟨fun j => _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.unipotent_base_row_entry u j, fun j => ?_, ?_, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.unipotent_base_base_entry u⟩
  · rw [Matrix.add_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.centre_base_row_entry, zero_add, hs]
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.uA_em_em_k, apply_ite (cA σ)]
  · rw [Matrix.add_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.centre_base_base_entry, hs, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.B.unipotent_base_row_entry, Pi.neg_apply, map_neg, mul_neg]
namespace W
variable (L) in
def Wm_k (a b : AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 - Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 +
    Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) a + Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) b
theorem Wm_mul_k (a b a' b' : AE F E) (h1 : a * a' = 1) (h2 : b * b' = 1) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L a b * _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L b' a' = 1 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, ne_eq, reduceCtorEq, not_false_eq_true, mul_one, one_mul,
    h1, h2]
  abel
theorem Wm_row_out_k (a b : AE F E) {k : Fin d.n} (hk : k ≠ L.i₀) (m : Fin d.n ⊕ Fin d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L a b (Sum.inr k) m = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr k) m := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply, Ne.symm hk]
theorem Wm_row_y_k (a b : AE F E) (m : Fin d.n ⊕ Fin d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L a b (Sum.inr L.i₀) m = if m = Sum.inl L.i₀ then b else 0 := by
  rcases m with i | i
  · by_cases hi : i = L.i₀
    · subst hi; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply, Matrix.one_apply, Ne.symm hi, hi]
  · by_cases hi : i = L.i₀
    · subst hi; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply, Matrix.one_apply, Ne.symm hi]
theorem Wm_col_out_k (a b : AE F E) {l : Fin d.n} (hl : l ≠ L.i₀) (m : Fin d.n ⊕ Fin d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L a b m (Sum.inl l) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) m (Sum.inl l) := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply, Ne.symm hl]
theorem Wm_col_x_k (a b : AE F E) (m : Fin d.n ⊕ Fin d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L a b m (Sum.inl L.i₀) = if m = Sum.inr L.i₀ then b else 0 := by
  rcases m with i | i
  · by_cases hi : i = L.i₀
    · subst hi; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply, Matrix.one_apply, hi, Ne.symm hi]
  · by_cases hi : i = L.i₀
    · subst hi; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k, Matrix.single_apply, Matrix.one_apply, hi, Ne.symm hi]
theorem mul_row_out_k (a b : AE F E) {k : Fin d.n} (hk : k ≠ L.i₀)
    (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (c : Fin d.n ⊕ Fin d.n) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L a b * M) (Sum.inr k) c = M (Sum.inr k) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr k)]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_row_out_k a b hk, Matrix.one_apply_eq, one_mul]
  · intro m _ hm
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_row_out_k a b hk, Matrix.one_apply_ne (Ne.symm hm), zero_mul]
  · simp
theorem mul_row_y_k (a b : AE F E) (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (c : Fin d.n ⊕ Fin d.n) : (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L a b * M) (Sum.inr L.i₀) c = b * M (Sum.inl L.i₀) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inl L.i₀)]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_row_y_k, if_pos rfl]
  · intro m _ hm
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_row_y_k, if_neg hm, zero_mul]
  · simp
theorem mul_col_out_k (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (a b : AE F E) {l : Fin d.n}
    (hl : l ≠ L.i₀) (r : Fin d.n ⊕ Fin d.n) : (M * _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L a b) r (Sum.inl l) = M r (Sum.inl l) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inl l)]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_col_out_k a b hl, Matrix.one_apply_eq, mul_one]
  · intro m _ hm
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_col_out_k a b hl, Matrix.one_apply_ne hm, mul_zero]
  · simp
theorem mul_col_x_k (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (a b : AE F E)
    (r : Fin d.n ⊕ Fin d.n) : (M * _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L a b) r (Sum.inl L.i₀) = M r (Sum.inr L.i₀) * b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr L.i₀)]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_col_x_k, if_pos rfl]
  · intro m _ hm
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_col_x_k, if_neg hm, mul_zero]
  · simp
end W
open W in
theorem weyl_conjugate_exponential_parabolic (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {e : AE F E} {b : Fin L.n → AE F E} {s : d.G}
    (hs : inFrame d.b s = _root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b) : w₁ * s * w₁⁻¹ ∈ par2 σ d.Y := by
  obtain ⟨a₀, b₀, ha, hb, hW⟩ := h.wf
  have hW' : inFrame d.b w₁ = _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L (inclR (F := F) (AF F) a₀) (inclR (F := F) (AF F) b₀) := hW
  have h1 : inclR (F := F) (AF F) a₀ * inclR (F := F) (AF F) a₀⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  have h2 : inclR (F := F) (AF F) b₀ * inclR (F := F) (AF F) b₀⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hb, map_one]
  have hWi : inFrame d.b w₁⁻¹ = _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L (inclR (F := F) (AF F) b₀⁻¹) (inclR (F := F) (AF F) a₀⁻¹) := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, hW', Matrix.inv_eq_right_inv (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_mul_k _ _ _ _ h1 h2)]
  refine (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame _).2 ?_
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hW', hs, hWi]
  have hne := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L
  have hS_rl : ∀ k l, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b (Sum.inr k) (Sum.inl l) = 0 := fun k l => by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k]
  have hS_ry : ∀ k, k ≠ L.i₀ → _root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b (Sum.inr k) (Sum.inr L.i₀) = 0 := fun k hk => by
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k, Matrix.one_apply, hk]
  have hS_xl : ∀ l, l ≠ L.i₀ → _root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b (Sum.inl L.i₀) (Sum.inl l) = 0 := fun l hl => by
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k, Matrix.one_apply, Ne.symm hl]
  have hS_xy : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b (Sum.inl L.i₀) (Sum.inr L.i₀) = 0 := by
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k, Matrix.sum_apply, Matrix.single_apply, hne, Ne.symm (hne _)]
  ext k l
  show (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L _ _ * _root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e b * _root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.Wm_k L _ _) (Sum.inr k) (Sum.inl l) = 0
  by_cases hl : l = L.i₀
  · subst hl
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.mul_col_x_k]
    by_cases hk : k = L.i₀
    · subst hk
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.mul_row_y_k, hS_xy, mul_zero, zero_mul]
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.mul_row_out_k _ _ hk, hS_ry k hk, zero_mul]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.mul_col_out_k _ _ _ hl]
    by_cases hk : k = L.i₀
    · subst hk
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.mul_row_y_k, hS_xl l hl, mul_zero]
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.W.mul_row_out_k _ _ hk, hS_rl]
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq PositivityTheory.SiegelWeilFormula.Act.C5
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem stab_dec_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {x : d.G} (hx : x ∈ rat2 σ d.Y) (hf : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L x) :
    ∃ (s : d.G) (c : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L) (γ' : G2 σ L.Y), s ∈ rat2 σ d.Y ∧ w₁ * s * w₁⁻¹ ∈ par2 σ d.Y ∧ γ' ∈ rat2 σ L.Y ∧
      inFrame L.b γ' = (inFrame d.b x).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) ∧ x = s * (cM c.1 * L.j γ') := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := _root_.PositivityTheory.SiegelWeilFormula.Afc.eps_eq_k L hε hε'
  subst hee
  obtain ⟨G0, hG0⟩ := Afc.rat_frame (b := d.b) x hx
  have hx0 : ∀ r, G0 r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀) := by
    intro r
    apply kfour.inclR_injective (F := F)
    have h1 := hf r
    rw [hG0] at h1
    simp only [incM, Matrix.map_apply] at h1
    rw [h1]
    by_cases hr : r = Sum.inl L.i₀ <;> simp [Matrix.one_apply, hr]
  have hform := form_E hε x hG0
  have hy := yrow_zero hform hx0
  set H := G0.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) with hH_def
  have hH := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.blockH_form_k L hform hx0 hy
  have hε1 : (((ε : ℤ) : E)) * (((ε : ℤ) : E)) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hεσ : (σ : E →+* E) (((ε : ℤ) : E)) = ((ε : ℤ) : E) := map_intCast _ _
  obtain ⟨hHH', hH'H⟩ := kunf.frame_inv_pf (σ : E →+* E) hσ (((ε : ℤ) : E)) hε1 hεσ H hH
  set H' := Matrix.fromBlocks ((H.toBlocks₂₂.map (σ : E →+* E))ᵀ) ((((ε : ℤ) : E)) • (H.toBlocks₁₂.map (σ : E →+* E))ᵀ)
      ((((ε : ℤ) : E)) • (H.toBlocks₂₁.map (σ : E →+* E))ᵀ) ((H.toBlocks₁₁.map (σ : E →+* E))ᵀ) with hH'_def
  have hIA : incM F H * incM F H' = 1 := by rw [← kfour.incM_mul', hHH', Afc.incM_one']
  have hformA : (incM F H)ᵀ * kunf.jw L.n (((ε : ℤ) : AE F E)) * (incM F H).map (cA σ) =
      kunf.jw L.n (((ε : ℤ) : AE F E)) := by
    have h1 := congrArg (incM F) hH
    rw [kfour.incM_mul', kfour.incM_mul', ← Afc.incM_transpose, ← Afc.incM_map_cA, ← QA_eq] at h1
    exact h1
  obtain ⟨g', hg'⟩ := kunf.exists_of_frame (Y := L.Y) hε' (incM F H) (incM F H') hIA hformA
  have hg'r : g' ∈ rat2 σ L.Y := kunf.rat_of_inFrame hg'
  have hg'i : inFrame L.b g'⁻¹ = incM F H' := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, hg']
    exact Matrix.inv_eq_right_inv hIA
  set n := x * L.j g'⁻¹ with hn_def
  have hnF : inFrame d.b n = incM F (G0 * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H') := by
    rw [hn_def, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hG0, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k, hg'i, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_incM_k, kfour.incM_mul']
  have hnq0 : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (G0 * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H') := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.nq_E_k L hx0 hy hHH'
  have hnr : n ∈ rat2 σ d.Y := mul_mem hx (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L (inv_mem hg'r))
  set N0 := G0 * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H' with hN0
  set u₀ : Fin L.n → E := fun j => N0 (Sum.inl L.i₀) (Sum.inl (L.em j)) with hu₀
  set b₀ : Fin L.n → E := fun j => N0 (Sum.inl L.i₀) (Sum.inr (L.em j)) with hb₀
  set z₀ : E := N0 (Sum.inl L.i₀) (Sum.inr L.i₀) + ∑ j, b₀ j * σ (u₀ j) with hz₀
  have hUN0 : M.U (σ : E →+* E) (((ε : ℤ) : E)) N0 := form_E hε n hnF
  have hpz : σ z₀ = -(((ε : ℤ) : E) * z₀) := M.even_im_hermitian_sub hσ hε1 hεσ L.em L.inj L.rng hUN0 hnq0
  have hpd := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.delta_par_k h hε
  have hε0 : (((ε : ℤ) : E)) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hε1; exact zero_ne_one hε1
  have hfix : σ (z₀ / δ) = z₀ / δ := by
    rw [map_div₀, hpz, hpd, neg_div_neg_eq, mul_div_mul_left _ _ hε0]
  obtain ⟨a₀, ha₀⟩ := fixed_in_F d.ok.good.cm (z₀ / δ) hfix
  let c : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L := ⟨(GlobalTheory.ThK.incV F u₀, algebraMap F (AF F) a₀), AddSubgroup.subset_closure ⟨u₀, rfl⟩, ⟨a₀, rfl⟩⟩
  set s := n * (cM c.1)⁻¹ with hs_def
  have hsr : s ∈ rat2 σ d.Y := mul_mem hnr (inv_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_rat'_k h c.2.1 c.2.2))
  set e : AE F E := ((ε : ℤ) : AE F E) with he_def
  have he : e * e = 1 := by
    rw [he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hse : (cA σ).toRingHom e = e := map_intCast _ _
  have hN : inFrame d.b n = _root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e (GlobalTheory.ThK.incV F b₀) * inFrame d.b (cM c.1) := by
    apply M.nq_unique (s := (cA σ).toRingHom) (e := e) (i₀ := L.i₀) (cA_inv' hσ) he hse
    · exact kunf.frame_eq hε n
    · have hUS := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.U_sExp_k (ε := ε) (L := L) hσ (GlobalTheory.ThK.incV F b₀)
      have hUC : M.U (cA σ).toRingHom e (inFrame d.b (cM c.1)) := kunf.frame_eq hε (cM c.1)
      unfold M.U at hUS hUC ⊢
      rw [Matrix.transpose_mul, Matrix.map_mul]
      calc (inFrame d.b (cM c.1))ᵀ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e (GlobalTheory.ThK.incV F b₀))ᵀ * kunf.jw d.n e *
            ((_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e (GlobalTheory.ThK.incV F b₀)).map (cA σ).toRingHom * (inFrame d.b (cM c.1)).map (cA σ).toRingHom)
          = (inFrame d.b (cM c.1))ᵀ * ((_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e (GlobalTheory.ThK.incV F b₀))ᵀ * kunf.jw d.n e *
            (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e (GlobalTheory.ThK.incV F b₀)).map (cA σ).toRingHom) * (inFrame d.b (cM c.1)).map (cA σ).toRingHom := by
            simp only [Matrix.mul_assoc]
        _ = kunf.jw d.n e := by rw [hUS, hUC]
    · rw [hnF]; exact NQ.map _ hnq0
    · exact NQ.mul (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.nq_sExp_k _ _) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.nq_cM_k h _)
    · obtain ⟨r1, r2, r3, r4⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.row_sC_k h e (GlobalTheory.ThK.incV F b₀) (GlobalTheory.ThK.incV F u₀) (algebraMap F (AF F) a₀)
      intro c'
      rw [hnF]
      rcases c' with k | k
      · by_cases hk : k = L.i₀
        · subst hk
          rw [r4]
          have := hnq0.1 (Sum.inl L.i₀)
          simp only [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at this
          simp [incM, this]
        · obtain ⟨j, rfl⟩ := (L.rng k).1 hk
          rw [r1]; rfl
      · by_cases hk : k = L.i₀
        · subst hk
          rw [r3]
          have e1 : algebraMap F (AF F) a₀ • inclR (F := F) (AF F) δ = inclR (F := F) (AF F) z₀ := by
            have : z₀ = algebraMap F E a₀ * δ := by rw [ha₀, div_mul_cancel₀ _ h.δ0]
            rw [this, map_mul]
            show algebraMap F (AF F) a₀ • ((1 : AF F) ⊗ₜ[F] δ) = (1 : AF F) ⊗ₜ[F] (algebraMap F E a₀) * (1 : AF F) ⊗ₜ[F] δ
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, TensorProduct.tmul_smul,
              TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← Algebra.algebraMap_eq_smul_one]
          rw [e1, hz₀]
          simp [incM, GlobalTheory.ThK.incV, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR, map_add, map_sum, map_mul]
        · obtain ⟨j, rfl⟩ := (L.rng k).1 hk
          rw [r2]; rfl
  have hS : inFrame d.b s = _root_.PositivityTheory.SiegelWeilFormula.Act.C6.sExp_k L e (GlobalTheory.ThK.incV F b₀) := by
    have h1 : inFrame d.b (cM c.1) * inFrame d.b (cM c.1)⁻¹ = 1 := by
      rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, mul_inv_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
    rw [hs_def, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hN, Matrix.mul_assoc, h1, Matrix.mul_one]
  refine ⟨s, c, g', hsr, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.weyl_conjugate_exponential_parabolic h hS, hg'r, ?_, ?_⟩
  · rw [hg', hG0]; rfl
  · rw [hs_def, hn_def, map_inv]; group
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem paddedMatrix_mul_submatrix (A : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E))
    (N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L A * N).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) = A * N.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L) _ _ ?_ ?_
  · intro l hl
    have hl' : ¬ ∃ b, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L b = l := fun ⟨b, hb⟩ => hl ⟨b, hb⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_col_k L A _ hl', Matrix.one_apply_ne, zero_mul]
    rintro rfl
    exact hl' ⟨a, rfl⟩
  · intro b
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k]
theorem mul_paddedMatrix_submatrix (B : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E))
    (N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    (N * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L B).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) = N.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) * B := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L) _ _ ?_ ?_
  · intro l hl
    have hl' : ¬ ∃ b, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L b = l := fun ⟨b, hb⟩ => hl ⟨b, hb⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_row_k L B hl', Matrix.one_apply_ne, mul_zero]
    rintro rfl
    exact hl' ⟨c, rfl⟩
  · intro b
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k]
theorem conj_rationalParabolic_embed (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {p' : G2 σ L.Y} (hp : p' ∈ par2 σ L.Y) (hpr : p' ∈ rat2 σ L.Y) (c : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ ∃ c₂ : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L, w₁ * (cM c.1 * L.j p') = p * (w₁ * cM c₂.1) := by
  have hx : (L.j p')⁻¹ * cM c.1 * L.j p' ∈ rat2 σ d.Y :=
    mul_mem (mul_mem (inv_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L hpr)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_rat'_k h c.2.1 c.2.2)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L hpr)
  have hf : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L ((L.j p')⁻¹ * cM c.1 * L.j p') :=
    _root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_mul_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_mul_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_inv_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_j_k p')) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_cM'_k h c.1)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_j_k p')
  obtain ⟨s, c₂, γ', hs, hsP, -, hγ', hx'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.stab_dec_k h hx hf
  have hsub : (inFrame d.b ((L.j p')⁻¹ * cM c.1 * L.j p')).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) = 1 := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← map_inv, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k,
      _root_.PositivityTheory.SiegelWeilFormula.Act.C6.mul_paddedMatrix_submatrix, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.paddedMatrix_mul_submatrix, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.emS_cM_k h, Matrix.mul_one, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel,
      GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have hγ1 : γ' = 1 := kunf.inFrame_injective L.b (by rw [hγ', hsub, GlobalTheory.EisBL.DoubledParabolic.inFrame_one])
  rw [hγ1, map_one, mul_one] at hx'
  refine ⟨L.j p' * (w₁ * s * w₁⁻¹), mul_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_par_k L hp) hsP,
    mul_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L hpr) (mul_mem (mul_mem h.wr hs) (inv_mem h.wr)), c₂, ?_⟩
  have hw := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.weyl_commutes_embedding h p'
  calc w₁ * (cM c.1 * L.j p') = w₁ * L.j p' * ((L.j p')⁻¹ * cM c.1 * L.j p') := by group
    _ = L.j p' * w₁ * (s * cM c₂.1) := by rw [hw, hx']
    _ = L.j p' * (w₁ * s * w₁⁻¹) * (w₁ * cM c₂.1) := by group
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C5
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
namespace I
variable (L) in
theorem sum_split'_k {M : Type} [AddCommMonoid M] (f : Fin d.n → M) : ∑ i, f i = f L.i₀ + ∑ k, f (L.em k) := by
  have himg : Finset.univ.image L.em = Finset.univ.erase L.i₀ := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    rw [L.rng i]
    rfl
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ L.i₀), ← himg, Finset.sum_image (fun a _ b _ h => L.inj h)]
theorem blk_mul_k {M N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)}
    (hM : ∀ r, M r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) r (Sum.inl L.i₀))
    (hN : ∀ c, N (Sum.inr L.i₀) c = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr L.i₀) c) :
    (M * N).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) = M.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) * N.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) := by
  ext a a'
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine Bq.sum_emb (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L) _ fun k hk => ?_
  rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L hk with rfl | rfl
  · rw [hM, Matrix.one_apply_ne, zero_mul]
    exact fun h => _root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inl_k L L.i₀ rfl ⟨a, h⟩
  · rw [hN, Matrix.one_apply_ne, mul_zero]
    exact fun h => _root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inr_k L L.i₀ rfl ⟨a', h.symm⟩
theorem blk_one_k : (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) = 1 := by
  ext a a'
  simp [Matrix.one_apply, (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L).eq_iff]
theorem rowy_cM_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) (k : Fin d.n ⊕ Fin d.n) :
    inFrame d.b (cM c) (Sum.inr L.i₀) k =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr L.i₀) k := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_frame_k h]
  rcases k with k | k
  · simp
  · by_cases hk : k = L.i₀
    · subst hk
      simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.one_apply, Matrix.single_apply, Matrix.sum_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.one_apply, Matrix.single_apply, Matrix.sum_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L, hk, Ne.symm hk]
theorem rowy_inv_k {x : d.G}
    (hx : ∀ k, inFrame d.b x (Sum.inr L.i₀) k =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr L.i₀) k) (k : Fin d.n ⊕ Fin d.n) :
    inFrame d.b x⁻¹ (Sum.inr L.i₀) k =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr L.i₀) k := by
  have h1 : (inFrame d.b x * inFrame d.b x⁻¹) (Sum.inr L.i₀) k =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr L.i₀) k := by
    rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, mul_inv_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr L.i₀)] at h1
  · rwa [hx, Matrix.one_apply_eq, one_mul] at h1
  · intro j _ hj
    rw [hx, Matrix.one_apply_ne (Ne.symm hj), zero_mul]
  · simp
theorem rowy_j_k (g : G2 σ L.Y) (k : Fin d.n ⊕ Fin d.n) :
    inFrame d.b (L.j g) (Sum.inr L.i₀) k =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr L.i₀) k :=
  (L.j_out g (Sum.inr L.i₀) (by simp) k).1
theorem blk_j_k (g : G2 σ L.Y) : (inFrame d.b (L.j g)).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) = inFrame L.b g := by
  ext a a'
  rw [Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k]
theorem weyl_embedded_columns (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (a : Fin L.n ⊕ Fin L.n) (l : Fin d.n ⊕ Fin d.n) :
    inFrame d.b w₁ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a) l = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a) l ∧
      inFrame d.b w₁ l (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) l (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a) := by
  obtain ⟨a₀, b₀, -, -, hW⟩ := h.wf
  rw [hW]
  have hne := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L
  rcases a with a | a <;>
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Matrix.single_apply, Matrix.one_apply, hne a, Ne.symm (hne a)] <;>
    (constructor <;> congr)
theorem weyl_base_rows (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) : ∃ b₀ : E, b₀ ≠ 0 ∧
    (∀ l, inFrame d.b w₁ (Sum.inr L.i₀) l = if l = Sum.inl L.i₀ then inclR (F := F) (AF F) b₀ else 0) ∧
    ∀ j l, inFrame d.b w₁ (Sum.inr (L.em j)) l =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr (L.em j)) l := by
  obtain ⟨a₀, b₀, -, hb, hW⟩ := h.wf
  refine ⟨b₀, hb, fun l => ?_, fun j l => (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.weyl_embedded_columns h (Sum.inr j) l).1⟩
  rw [hW]
  rcases l with i | i <;> by_cases hi : i = L.i₀
  · subst hi; simp [Matrix.single_apply, Matrix.one_apply]
  · simp [Matrix.single_apply, Matrix.one_apply, hi, Ne.symm hi]
  · subst hi; simp [Matrix.single_apply, Matrix.one_apply]
  · simp [Matrix.single_apply, Matrix.one_apply, hi, Ne.symm hi]
theorem row_eq_k {P Wm C C' : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)} {b : AE F E}
    (hP : ∀ i, P (Sum.inr L.i₀) (Sum.inl i) = 0)
    (hWy : ∀ l, Wm (Sum.inr L.i₀) l = if l = Sum.inl L.i₀ then b else 0)
    (hWo : ∀ j l, Wm (Sum.inr (L.em j)) l =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr (L.em j)) l)
    (hE : P * (Wm * C) = Wm * C') (k : Fin d.n ⊕ Fin d.n) :
    b * C' (Sum.inl L.i₀) k = P (Sum.inr L.i₀) (Sum.inr L.i₀) * (b * C (Sum.inl L.i₀) k) +
      ∑ j, P (Sum.inr L.i₀) (Sum.inr (L.em j)) * C (Sum.inr (L.em j)) k := by
  have hy : ∀ X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E),
      (Wm * X) (Sum.inr L.i₀) k = b * X (Sum.inl L.i₀) k := by
    intro X
    rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inl L.i₀)]
    · rw [hWy, if_pos rfl]
    · intro l _ hl
      rw [hWy, if_neg hl, zero_mul]
    · simp
  have hem : ∀ j, (Wm * C) (Sum.inr (L.em j)) k = C (Sum.inr (L.em j)) k := by
    intro j
    rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr (L.em j))]
    · rw [hWo, Matrix.one_apply_eq, one_mul]
    · intro l _ hl
      rw [hWo, Matrix.one_apply_ne (Ne.symm hl), zero_mul]
    · simp
  have e := congrFun (congrFun hE (Sum.inr L.i₀)) k
  rw [← hy C', ← e, Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [hP, zero_mul, Finset.sum_const_zero, zero_add]
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.sum_split'_k L (fun i => P (Sum.inr L.i₀) (Sum.inr i) * (Wm * C) (Sum.inr i) k), hy C]
  simp only [hem]
theorem cx_em_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) (m : Fin L.n) :
    inFrame d.b (cM c) (Sum.inl L.i₀) (Sum.inl (L.em m)) = c.1 m := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_frame_k h]
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.one_apply, Matrix.single_apply, Matrix.sum_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L, L.inj.eq_iff,
    Ne.symm (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L _)]
theorem cx_emr_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) (m : Fin L.n) :
    inFrame d.b (cM c) (Sum.inl L.i₀) (Sum.inr (L.em m)) = 0 := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_frame_k h]
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.single_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L, Ne.symm (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L _)]
theorem cx_y_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) :
    inFrame d.b (cM c) (Sum.inl L.i₀) (Sum.inr L.i₀) = c.2 • inclR (F := F) (E := E) (AF F) δ := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_frame_k h]
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k]
theorem cem_l_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) (j : Fin L.n) (l : Fin d.n) :
    inFrame d.b (cM c) (Sum.inr (L.em j)) (Sum.inl l) = 0 := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_frame_k h]
  simp
theorem cem_em_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) (j m : Fin L.n) :
    inFrame d.b (cM c) (Sum.inr (L.em j)) (Sum.inr (L.em m)) =
      (1 : Matrix (Fin L.n) (Fin L.n) (AE F E)) j m := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_frame_k h]
  by_cases hjm : j = m
  · subst hjm
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.one_apply, Matrix.single_apply, Matrix.sum_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L, Ne.symm (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L _)]
  · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.one_apply, Matrix.single_apply, Matrix.sum_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L, Ne.symm (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L _),
      L.inj.eq_iff, hjm, Ne.symm hjm]
theorem inj_core_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {p : d.G} (hp : p ∈ par2 σ d.Y) (hpr : p ∈ rat2 σ d.Y) {c c' : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L}
    {γ' γ'' : G2 σ L.Y} (h' : γ' ∈ rat2 σ L.Y) (h'' : γ'' ∈ rat2 σ L.Y)
    (e : p * (w₁ * (cM c.1 * L.j γ')) = w₁ * (cM c'.1 * L.j γ'')) :
    γ'' * γ'⁻¹ ∈ par2 σ L.Y ∧ (γ'' = γ' → c = c') := by
  have hP21 : (inFrame d.b p).toBlocks₂₁ = 0 := (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame p).1 hp
  have hP : ∀ i k, inFrame d.b p (Sum.inr i) (Sum.inl k) = 0 := fun i k => congrFun (congrFun hP21 i) k
  refine ⟨?_, fun hγ => ?_⟩
  ·
    set g := γ'' * γ'⁻¹ with hg
    have key : w₁⁻¹ * p * w₁ * (cM c.1 * L.j γ') = cM c'.1 * L.j γ'' := by
      rw [mul_assoc (w₁⁻¹ * p), mul_assoc w₁⁻¹, e, inv_mul_cancel_left]
    have key2 : w₁⁻¹ * p * w₁ = cM c'.1 * L.j g * (cM c.1)⁻¹ := by
      rw [hg, map_mul, map_inv, ← mul_assoc (cM c'.1), ← key]
      group
    have hQ : (inFrame d.b (w₁⁻¹ * p * w₁)).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) = (inFrame d.b p).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) := by
      have hWQ : inFrame d.b w₁ * inFrame d.b (w₁⁻¹ * p * w₁) = inFrame d.b p * inFrame d.b w₁ := by
        rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel,
          one_mul]
      ext a a'
      have e1 := congrFun (congrFun hWQ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a')
      rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a), Finset.sum_eq_single (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a')] at e1
      · rw [(_root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.weyl_embedded_columns h a (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a)).1, (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.weyl_embedded_columns h a' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a')).2, Matrix.one_apply_eq, Matrix.one_apply_eq, one_mul, mul_one] at e1
        exact e1
      · intro l _ hl
        rw [(_root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.weyl_embedded_columns h a' l).2, Matrix.one_apply_ne hl, mul_zero]
      · simp
      · intro l _ hl
        rw [(_root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.weyl_embedded_columns h a l).1, Matrix.one_apply_ne (Ne.symm hl), zero_mul]
      · simp
    have hfixC' := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_cM'_k h c'.1
    have hC1 : (inFrame d.b (cM c.1)⁻¹).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) = 1 := by
      have h1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.blk_mul_k (L := L) (M := inFrame d.b (cM c.1)) (N := inFrame d.b (cM c.1)⁻¹) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_cM'_k h c.1)
        (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.rowy_inv_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.rowy_cM_k h c.1))
      rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, mul_inv_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.blk_one_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.emS_cM_k h, one_mul] at h1
      exact h1.symm
    have hR : (inFrame d.b (cM c'.1 * L.j g * (cM c.1)⁻¹)).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) = inFrame L.b g := by
      rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.blk_mul_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_mul_k hfixC' (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_j_k g)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.rowy_inv_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.rowy_cM_k h c.1)),
        GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.blk_mul_k hfixC' (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.rowy_j_k g), _root_.PositivityTheory.SiegelWeilFormula.Act.C6.emS_cM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.blk_j_k, hC1, one_mul, mul_one]
    have hG : inFrame L.b g = (inFrame d.b p).submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) := by
      rw [← hR, ← key2, hQ]
    refine (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block L.ok.frame g).2 ?_
    ext i k
    rw [hG]
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.zero_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Sum.map_inr,
      Sum.map_inl]
    exact hP _ _
  ·
    subst hγ
    have e2 : p * w₁ * cM c.1 = w₁ * cM c'.1 := by
      have h1 := congrArg (· * (L.j γ'')⁻¹) e
      simpa [mul_assoc] using h1
    have hE : inFrame d.b p * (inFrame d.b w₁ * inFrame d.b (cM c.1)) = inFrame d.b w₁ * inFrame d.b (cM c'.1) := by
      have h1 := congrArg (inFrame d.b) e2
      simpa only [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_assoc] using h1
    obtain ⟨b₀, hb₀, hWy, hWo⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.weyl_base_rows h
    have hrow := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.row_eq_k (fun i => hP L.i₀ i) hWy hWo hE
    set bA := inclR (F := F) (E := E) (AF F) b₀
    have hbinv : inclR (F := F) (E := E) (AF F) b₀⁻¹ * bA = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hb₀, map_one]
    have canc : ∀ X Y : AE F E, bA * X = bA * Y → X = Y := by
      intro X Y hXY
      have h1 := congrArg (inclR (F := F) (E := E) (AF F) b₀⁻¹ * ·) hXY
      simpa only [← mul_assoc, hbinv, one_mul] using h1
    have hfixC := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_cM'_k h c.1
    have hfixC' := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_cM'_k h c'.1
    have hyy : inFrame d.b p (Sum.inr L.i₀) (Sum.inr L.i₀) = 1 := by
      have h1 := hrow (Sum.inl L.i₀)
      have hs : ∑ j, inFrame d.b p (Sum.inr L.i₀) (Sum.inr (L.em j)) *
          inFrame d.b (cM c.1) (Sum.inr (L.em j)) (Sum.inl L.i₀) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [hfixC, Matrix.one_apply_ne (by simp), mul_zero]
      rw [hs, add_zero, hfixC', hfixC, Matrix.one_apply_eq, mul_one] at h1
      exact canc _ _ (by rw [mul_one, mul_comm]; exact h1.symm)
    have hd : ∀ l, inFrame d.b p (Sum.inr L.i₀) (Sum.inr (L.em l)) = 0 := by
      intro l
      have h1 := hrow (Sum.inr (L.em l))
      have hs : ∑ j, inFrame d.b p (Sum.inr L.i₀) (Sum.inr (L.em j)) *
          inFrame d.b (cM c.1) (Sum.inr (L.em j)) (Sum.inr (L.em l)) = inFrame d.b p (Sum.inr L.i₀) (Sum.inr (L.em l)) := by
        rw [Finset.sum_eq_single l]
        · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.cem_em_k h, Matrix.one_apply_eq, mul_one]
        · intro j _ hj
          rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.cem_em_k h, Matrix.one_apply_ne hj, mul_zero]
        · simp
      rw [hs, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.cx_emr_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.cx_emr_k h] at h1
      simp only [mul_zero, zero_add] at h1
      exact h1.symm
    have hu : ∀ m, c'.1.1 m = c.1.1 m := by
      intro m
      have h1 := hrow (Sum.inl (L.em m))
      have hs : ∑ j, inFrame d.b p (Sum.inr L.i₀) (Sum.inr (L.em j)) *
          inFrame d.b (cM c.1) (Sum.inr (L.em j)) (Sum.inl (L.em m)) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.cem_l_k h, mul_zero]
      rw [hs, add_zero, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.cx_em_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.cx_em_k h, hyy, one_mul] at h1
      exact canc _ _ h1
    have ha : c'.1.2 = c.1.2 := by
      have h1 := hrow (Sum.inr L.i₀)
      have hs : ∑ j, inFrame d.b p (Sum.inr L.i₀) (Sum.inr (L.em j)) *
          inFrame d.b (cM c.1) (Sum.inr (L.em j)) (Sum.inr L.i₀) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [hd, zero_mul]
      rw [hs, add_zero, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.cx_y_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.cx_y_k h, hyy, one_mul] at h1
      exact smul_inclR_inj h.δ0 (canc _ _ h1)
    exact Subtype.ext (Prod.ext (funext fun m => (hu m).symm) ha.symm)
end I
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem inj_core_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {p : d.G} (hp : p ∈ par2 σ d.Y) (hpr : p ∈ rat2 σ d.Y) {c c' : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L}
    {γ' γ'' : G2 σ L.Y} (h' : γ' ∈ rat2 σ L.Y) (h'' : γ'' ∈ rat2 σ L.Y)
    (e : p * (w₁ * (cM c.1 * L.j γ')) = w₁ * (cM c'.1 * L.j γ'')) :
    γ'' * γ'⁻¹ ∈ par2 σ L.Y ∧ (γ'' = γ' → c = c') :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C6.I.inj_core_k h hp hpr h' h'' e
theorem conj_par_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {p' : G2 σ L.Y} (hp : p' ∈ par2 σ L.Y) (hpr : p' ∈ rat2 σ L.Y) (c : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ ∃ c₂ : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L, w₁ * (cM c.1 * L.j p') = p * (w₁ * cM c₂.1) := by
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C6.conj_rationalParabolic_embed h hp hpr c
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
namespace N
theorem fix_of_col_k {w x : d.G}
    (hc : ∀ r, inFrame d.b x r (Sum.inl L.i₀) = inFrame d.b w r (Sum.inl L.i₀)) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (w⁻¹ * x) := by
  intro k
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply]
  simp_rw [hc]
  rw [← Matrix.mul_apply, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
theorem weyl_base_column (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) : ∃ b₀ : E, b₀ ≠ 0 ∧ ∀ r, inFrame d.b w₁ r (Sum.inl L.i₀) =
    inclR (F := F) (AF F) ((Pi.single (Sum.inr L.i₀) b₀ : Fin d.n ⊕ Fin d.n → E) r) := by
  obtain ⟨a, b, -, hb, hw⟩ := h.wf
  refine ⟨b, hb, fun r => ?_⟩
  rw [hw]
  rcases r with i | i <;> by_cases hi : i = L.i₀
  · subst hi; simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply]
  · simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply, hi, Ne.symm hi]
  · subst hi; simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply]
  · simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply, hi, Ne.symm hi]
theorem normalize_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {γ : d.G} (hγ : γ ∈ rat2 σ d.Y) (hn : ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L γ) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (w₁⁻¹ * (p * γ)) := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨G0, hG0⟩ := Afc.rat_frame (b := d.b) γ hγ
  have hform := Bq.form_E hε γ hG0
  obtain ⟨b₀, hb₀, hw1⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.N.weyl_base_column h
  have hy : (fun k => G0 (Sum.inr k) (Sum.inl L.i₀)) ≠ 0 := by
    intro h0
    apply hn
    intro i
    rw [hG0]
    show inclR (F := F) (AF F) (G0 (Sum.inr i) (Sum.inl L.i₀)) = 0
    rw [congrFun h0 i, Pi.zero_apply, map_zero]
  obtain ⟨A, β0, hβ, hcol⟩ := exists_E L.i₀ hσ ε hform hb₀ hy
  obtain ⟨pm, hpmr, hpm⟩ := Afc.levi_ex hσ d.ok.frame A
  have hpmP : pm ∈ par2 σ d.Y :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame pm).2 (by rw [hpm, Matrix.toBlocks_fromBlocks₂₁])
  have hβA : incM F β0 ∈ nA σ d.Y d.b := (kfour.mem_nA_iff hσ hε _).2 (nCond_of_E ε hβ)
  set pn := nb ⟨incM F β0, hβA⟩ with hpn_def
  have hpn : inFrame d.b pn = Matrix.fromBlocks 1 (incM F β0) 0 1 := h.nb _
  have hpnP : pn ∈ par2 σ d.Y :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame pn).2 (by rw [hpn, Matrix.toBlocks_fromBlocks₂₁])
  have hpnr : pn ∈ rat2 σ d.Y :=
    kunf.rat_of_inFrame (M := Matrix.fromBlocks 1 β0 0 1) (by rw [hpn, kfour.incM_nM]; rfl)
  refine ⟨pn * pm, mul_mem hpnP hpmP, mul_mem hpnr hpmr, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.N.fix_of_col_k fun r => ?_⟩
  have hF : inFrame d.b (pn * pm * γ) =
      incM F (Matrix.fromBlocks 1 β0 0 1 * Matrix.fromBlocks A.1 0 0 (((A⁻¹).1)ᵀ.map σ) * G0) := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hpn, hpm, hG0, kfour.incM_mul', kfour.incM_mul',
      kfour.incM_nM, Afc.incM_fromBlocks, kfour.incM_zero]
    rfl
  rw [hF, hw1 r]
  show inclR (F := F) (AF F) _ = _
  rw [hcol r]
end N
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem normalize_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {γ : d.G} (hγ : γ ∈ rat2 σ d.Y) (hn : ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L γ) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (w₁⁻¹ * (p * γ)) :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C6.N.normalize_k h hγ hn
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem second_orbit_bijection_weyl (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) :
    ∃ e : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L) ≃ {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ∀ x, ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧
      _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e x).1 = p * (w₁ * (cM x.2.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1))) := by
  have hg : ∀ x : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L), w₁ * (cM x.2.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1)) ∈ rat2 σ d.Y := fun x =>
    (rat2 σ d.Y).mul_mem h.wr ((rat2 σ d.Y).mul_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_rat'_k h x.2.2.1 x.2.2.2) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.rep_mem_k L.sd x.1)))
  have hfix : ∀ x : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L), _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (cM x.2.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1)) := fun x => _root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_mul_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_cM'_k h _) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_j_k _)
  let Fm : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L) → {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)} := fun x =>
    ⟨Quotient.mk _ ⟨_, hg x⟩, by
      obtain ⟨p, hp, -, e⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.out_mk_k d ⟨_, hg x⟩
      rw [e, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.first_orbit_parabolic_left hp]
      exact _root_.PositivityTheory.SiegelWeilFormula.Act.C6.not_first_orbit_weyl h (hfix x)⟩
  have hinj : Function.Injective Fm := by
    rintro ⟨q₁, c₁⟩ ⟨q₂, c₂⟩ hE
    have hE' : (Quotient.mk _ ⟨_, hg ⟨q₁, c₁⟩⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) = Quotient.mk _ ⟨_, hg ⟨q₂, c₂⟩⟩ := congrArg Subtype.val hE
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.mk_eq_mk_k] at hE'
    set g₁ := w₁ * (cM c₁.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q₁))
    set g₂ := w₁ * (cM c₂.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q₂))
    have e : (g₂ * g₁⁻¹) * (w₁ * (cM c₁.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q₁))) = w₁ * (cM c₂.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q₂)) := by
      simp only [g₁, g₂]; group
    have hpr : g₂ * g₁⁻¹ ∈ rat2 σ d.Y := (rat2 σ d.Y).mul_mem (hg ⟨q₂, c₂⟩) ((rat2 σ d.Y).inv_mem (hg ⟨q₁, c₁⟩))
    obtain ⟨hP, hc⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.inj_core_k h hE' hpr (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.rep_mem_k L.sd q₁) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.rep_mem_k L.sd q₂) e
    have hq : q₁ = q₂ := by
      rw [← _root_.PositivityTheory.SiegelWeilFormula.Act.C6.mk_rep_k L.sd q₁, ← _root_.PositivityTheory.SiegelWeilFormula.Act.C6.mk_rep_k L.sd q₂, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.mk_eq_mk_k]
      exact hP
    subst hq
    rw [hc rfl]
  have hsurj : Function.Surjective Fm := by
    rintro ⟨q, hq⟩
    obtain ⟨p, hp, hpr, hfx⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.normalize_k h (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.rep_mem_k d q) hq
    have hr : w₁⁻¹ * (p * _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) ∈ rat2 σ d.Y :=
      (rat2 σ d.Y).mul_mem ((rat2 σ d.Y).inv_mem h.wr) ((rat2 σ d.Y).mul_mem hpr (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.rep_mem_k d q))
    obtain ⟨s, c, γ', hsr, hW, hγ', -, hx⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.stab_dec_k h hr hfx
    obtain ⟨p', hp', hp'r, he'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.out_mk_k L.sd ⟨γ', hγ'⟩
    obtain ⟨p₂, hp₂, hp₂r, c₂, hc₂⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.conj_par_k h ((par2 σ L.Y).inv_mem hp') ((rat2 σ L.Y).inv_mem hp'r) c
    refine ⟨⟨Quotient.mk _ ⟨γ', hγ'⟩, c₂⟩, Subtype.ext ?_⟩
    show (Quotient.mk _ ⟨_, hg ⟨Quotient.mk _ ⟨γ', hγ'⟩, c₂⟩⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) = q
    conv_rhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.Act.C6.mk_rep_k d q]
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.mk_eq_mk_k]
    have hγ'' : γ' = p'⁻¹ * _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (Quotient.mk _ ⟨γ', hγ'⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd) := by rw [he']; group
    have key : p * _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q = (w₁ * s * w₁⁻¹) * p₂ * (w₁ * (cM c₂.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (Quotient.mk _ ⟨γ', hγ'⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd)))) := by
      have h1 : p * _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q = w₁ * (s * (cM c.1 * L.j γ')) := by rw [← hx]; group
      rw [h1]
      conv_lhs => rw [hγ'', map_mul]
      have h2 : w₁ * (s * (cM c.1 * (L.j p'⁻¹ * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (Quotient.mk _ ⟨γ', hγ'⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd))))) =
          (w₁ * s * w₁⁻¹) * ((w₁ * (cM c.1 * L.j p'⁻¹)) * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (Quotient.mk _ ⟨γ', hγ'⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd))) := by group
      rw [h2, hc₂]
      group
    have : _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q * (w₁ * (cM c₂.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (Quotient.mk _ ⟨γ', hγ'⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd))))⁻¹ = p⁻¹ * ((w₁ * s * w₁⁻¹) * p₂) := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, key]; group
    rw [this]
    exact (par2 σ d.Y).mul_mem ((par2 σ d.Y).inv_mem hp) ((par2 σ d.Y).mul_mem hW hp₂)
  refine ⟨Equiv.ofBijective Fm ⟨hinj, hsurj⟩, fun x => ?_⟩
  obtain ⟨p, hp, hpr, e⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.out_mk_k d ⟨_, hg x⟩
  exact ⟨p, hp, hpr, e⟩
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
abbrev Crat_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : Type := {c : (Fin L.n → AE F E) × AF F // c.1 ∈ L.ratV ∧ c.2 ∈ (algebraMap F (AF F)).range}
theorem second_orbit_bijection (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) :
    ∃ e : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L) ≃ {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ∀ x, ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧
      _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e x).1 = p * (w₁ * (cM x.2.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1))) := by
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C6.second_orbit_bijection_weyl ⟨h.nb, h.uM, h.nb', h.wr, h.wf, h.cf, h.δ0⟩
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end
