import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperLeftBlockEqOneIffOfFullRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameReducesToBasisModPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixModPlaceBasisChangeEqConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymAllowed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InModIffForallPlaceMemSpanModulo
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRhoX
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjIdempotentSubOneMemPlaceIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormMiddleSymmetricFrameNotOneAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianE0SymmetricFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipotentDualVectorPairingSymmetricFrameModPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDualVectorPairingSymmetricFrameModPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianZ0SymmetricFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarCharacterEqProdAdditiveCharactersRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodAtOfFixRed
import BuildAid.ForwardExisting

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixModPlace_basisChange_eq_conj : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), FixRed X red b → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (P : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) (u : Fin D.R.r → VA X.B.I), (∀ j, u j - ∑ i, ((((((P : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) i j).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • incl X.B.I (b kv i) ∈ wLf X (D.naut.plGw kv.1 kv.2)) → ∀ k ∈ X.B.I.Kset, GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k ((((P⁻¹ * red k kv * P) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) := by
  first | exact @GlobalTheory.Mem.SymFrame.isMatIn_basisChange | exact GlobalTheory.Mem.SymFrame.isMatIn_basisChange | (intros; apply GlobalTheory.Mem.SymFrame.isMatIn_basisChange <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inMod_iff_forall_place_memSpanModulo : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (S : Set (VA X.B.I)), S ⊆ X.B.I.Lf → ∀ y ∈ X.B.I.Lf, (InMod X.B.I X.B.g S y ↔ ∀ w : HeightOneSpectrum (𝓞 D.host.E), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.Mem.GroupLoc.ModW X w S y) := by
  first | exact @GlobalTheory.Mem.GroupLoc.Crt.inMod_iff_forall_modW | exact GlobalTheory.Mem.GroupLoc.Crt.inMod_iff_forall_modW | (intros; apply GlobalTheory.Mem.GroupLoc.Crt.inMod_iff_forall_modW <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.GroupLoc.Coords

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA PIW.AdelClassFin

variable {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p m : ℕ}

theorem rep_of_int (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {u : Fin m → Fin I.n → I.E ⊗[I.F] Af I.F} (hu : ∀ j, u j ∈ I.Lf) {v : Fin I.n → I.E ⊗[I.F] Af I.F}
    {c : Fin m → ℤ} (h : v - ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w) :
    RepV w p u v (fun j => (c j : ZMod p)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h2 : ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j -
      ∑ j, ((((c j : ℤ) : ZMod p).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun j _ => ?_
    rw [← sub_smul]
    refine Wq_smul ?_ (hu j)
    have hk : c j - ((((c j : ZMod p)).val : ℕ) : ℤ) = (c j / p) * p := by
      rw [ZMod.val_intCast, Int.emod_def]; ring
    have e : (c j : I.E ⊗[I.F] Af I.F) - ((((c j : ℤ) : ZMod p).val : ℕ) : I.E ⊗[I.F] Af I.F) =
        ((c j / p : ℤ) : I.E ⊗[I.F] Af I.F) * (p : I.E ⊗[I.F] Af I.F) := by
      have := congrArg (Int.cast : ℤ → I.E ⊗[I.F] Af I.F) hk
      simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_mul] using this
    rw [e]
    exact Wq_mul (natCast_Wq hp hcard) (intCast_int _)
  have := add_mem h h2
  show v - _ ∈ _
  convert this using 1
  abel

theorem int_comb (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {u : Fin m → Fin I.n → I.E ⊗[I.F] Af I.F} (hu : ∀ j, u j ∈ I.Lf) (S : Set (Fin m))
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ Submodule.span (IntAf I.F I.E) (u '' S) ⊔ Lq I w) :
    ∃ c : Fin m → ℤ, (∀ j, j ∉ S → c j = 0) ∧ y - ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
  classical
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
  have key : ∃ c : Fin m → ℤ, (∀ j, j ∉ S → c j = 0) ∧
      y1 - ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
    clear hy
    induction hy1 using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨Pi.single i 1, fun j hj => Pi.single_eq_of_ne (fun e : j = i => hj (by rw [e]; exact hi)) _, ?_⟩
      rw [Fintype.sum_eq_single i (fun j hj => by simp [hj])]
      simp
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨c, hc0, hc⟩ := hx
      obtain ⟨d, hd0, hd⟩ := hz
      refine ⟨c + d, fun j hj => by simp [hc0 j hj, hd0 j hj], ?_⟩
      have := add_mem hc hd
      convert this using 1
      simp only [Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]
      abel
    | smul s x _ hx =>
      obtain ⟨c, hc0, hc⟩ := hx
      obtain ⟨_, t, -, ht⟩ := congW_exists (w := w) hp hcard s.2
      refine ⟨fun j => t * c j, fun j hj => by simp [hc0 j hj], ?_⟩
      have h1 := (Lq I w).smul_mem s hc
      have h2 : ((s : I.E ⊗[I.F] Af I.F) - (t : I.E ⊗[I.F] Af I.F)) •
          ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
        refine Wq_smul ht (sum_mem fun j _ => ?_)
        rw [Int.cast_smul_eq_zsmul]
        exact zsmul_mem (hu j) _
      have := add_mem h1 h2
      convert this using 1
      show (s : I.E ⊗[I.F] Af I.F) • x - _ = (s : I.E ⊗[I.F] Af I.F) • (x - _) + _
      simp only [Int.cast_mul, mul_smul, ← Finset.smul_sum, smul_sub, sub_smul]
      abel
  obtain ⟨c, hc0, hc⟩ := key
  refine ⟨c, hc0, ?_⟩
  have := add_mem hc hy2
  convert this using 1
  abel

theorem cols_iff (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) (hm : m = I.n)
    {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) (P : GL (Fin m) (ZMod p))
    {u : Fin m → Fin I.n → I.E ⊗[I.F] Af I.F}
    (hP : ∀ j, RepV w p (fun k => iv I (b k)) (u j) (fun k => (P : Matrix (Fin m) (Fin m) (ZMod p)) k j))
    (A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (N : Matrix (Fin m) (Fin m) (ZMod p))
    (i : Fin m) (hN : RepV w p u (A *ᵥ u i) (fun j => N j i)) (S : Set (Fin m)) :
    (∀ j, j ∉ S → N j i = (1 : Matrix (Fin m) (Fin m) (ZMod p)) j i) ↔
      (A - 1) *ᵥ u i ∈ Submodule.span (IntAf I.F I.E) (u '' S) ⊔ Lq I w := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have hu : ∀ j, u j ∈ I.Lf := fun j => by
    have h1 : u j - _ ∈ I.Lf := lamAf_mono I (wLat0_le I w) (hP j)
    have h2 : ∑ k, ((((P : Matrix (Fin m) (Fin m) (ZMod p)) k j).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b k) ∈ I.Lf :=
      sum_mem fun k _ => by
        rw [Nat.cast_smul_eq_nsmul]
        exact nsmul_mem (DictLat.iv_mem I (hb.1 k)) _
    simpa using add_mem h1 h2
  have e1 : ∑ j, ((((1 : Matrix (Fin m) (Fin m) (ZMod p)) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j = u i := by
    rw [Fintype.sum_eq_single i (fun j hj => by simp [Matrix.one_apply_ne hj])]
    simp only [Matrix.one_apply_eq, ZMod.val_one, Nat.cast_one, one_smul]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  constructor
  · intro h
    have h1 : ∑ j, (((N j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j - u i ∈
        Submodule.span (IntAf I.F I.E) (u '' S) := by
      rw [← e1, ← Finset.sum_sub_distrib]
      refine sum_mem fun j _ => ?_
      by_cases hj : j ∈ S
      · rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
        have hm : u j ∈ Submodule.span (IntAf I.F I.E) (u '' S) := Submodule.subset_span ⟨j, hj, rfl⟩
        exact sub_mem (nsmul_mem hm _) (nsmul_mem hm _)
      · rw [h j hj, sub_self]; exact zero_mem _
    have := Submodule.add_mem_sup h1 hN
    convert this using 1
    abel
  · intro h j hj
    obtain ⟨c, hc0, hc⟩ := int_comb hp hcard hu S h
    have h2 : A *ᵥ u i - ∑ l, (((c + Pi.single i 1 : Fin m → ℤ) l : ℤ) : I.E ⊗[I.F] Af I.F) • u l ∈ Lq I w := by
      convert hc using 1
      simp only [Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]
      rw [Fintype.sum_eq_single i (f := fun l => (((Pi.single i 1 : Fin m → ℤ) l : ℤ) : I.E ⊗[I.F] Af I.F) • u l)
        (fun l hl => by simp [hl])]
      simp only [Pi.single_eq_same, Int.cast_one, one_smul]
      abel
    have h3 := rep_unique hp hcard hm hb (rep_comp hp hcard hb.1 hN hP)
      (rep_comp hp hcard hb.1 (rep_of_int hp hcard hu h2) hP)
    have h4 := congrArg (fun v => ((P⁻¹ : GL (Fin m) (ZMod p)) : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ v) h3
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h4
    have h5 := congrFun h4 j
    simp only [Pi.add_apply, hc0 j hj, zero_add] at h5
    rw [h5]
    by_cases e : j = i
    · subst e; simp
    · simp [e]

theorem mem_unipSym_iff {κ : Type} [CommRing κ] {r ρ k : ℕ} (N : GL (Fin r) κ) :
    N ∈ unipSym κ r ρ k ↔ ∀ i j : Fin r, j ∉ {j | symAllowed ρ k i j} →
      (N : Matrix (Fin r) (Fin r) κ) j i = (1 : Matrix (Fin r) (Fin r) κ) j i := by
  constructor
  · rintro ⟨h1, h2⟩ i j hj
    rcases lt_trichotomy j i with h | h | h
    · obtain ⟨a, b, c⟩ : ρ ≤ j.1 ∧ j.1 < ρ + k ∧ i.1 = ρ + k := by
        by_contra hh
        exact hj ⟨h, hh⟩
      rw [h2 j i a b c, Matrix.one_apply_ne h.ne]
    · subst h
      rw [unip_diag h1, Matrix.one_apply_eq]
    · rw [unip_lower h1 h, Matrix.one_apply_ne h.ne']
  · intro h
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j ha hb hc => ?_⟩
    · have hij' : j.val < i.val := hij
      rw [h j i (fun hh => by have := hh.1; omega), Matrix.one_apply_ne (fun e => by rw [e] at hij'; omega)]
    · rw [h i i (fun hh => lt_irrefl _ hh.1), Matrix.one_apply_eq]
    · rw [h j i (fun hh => hh.2 ⟨ha, hb, hc⟩), Matrix.one_apply_ne (fun e => by rw [e] at hb; omega)]

end GlobalTheory.Mem.GroupLoc.Coords

namespace GlobalTheory.Mem.GroupLoc

open Formalism.L2.SG.Pf.RowDictPf in

theorem mem_unipSym_iff_colCond : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (N : GL (Fin D.R.r) (ZMod (D.host.g kv.1))), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → (N ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k ↔ GlobalTheory.Mem.GroupLoc.ColCond X (D.naut.plGw kv.1 kv.2) k) := by
  intro D X h hι hg k _ kv N hN
  choose b hb using fun kv => Formalism.L2.SG.Pf.AllRowsRhoX.exists_b X kv
  obtain ⟨P, hP⟩ := GlobalTheory.T.symmetricFrame_reduces_to_basis_mod_place D X h hι b (fun kv => by
    unfold IsRedBasis
    rw [wLat_eq X]
    exact hb kv) hg 1
  rw [Coords.mem_unipSym_iff]
  unfold ColCond ModW
  refine forall_congr' fun i => ?_
  have hP' := hP kv
  have hN' := hN i
  unfold wLf at hP' hN' ⊢
  rw [wLat_eq X] at hP' hN' ⊢
  exact Coords.cols_iff (w := wB X (D.naut.plGw kv.1 kv.2)) (D.host.g_prime kv.1)
    (by rw [card_wB, card_res_host]) X.n_eq.symm (hb kv) (P kv) hP' (X.B.I.fmat k) _ i hN' _

end GlobalTheory.Mem.GroupLoc
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricFrame_matrix_mem_unipotent_iff_column_span : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (N : GL (Fin D.R.r) (ZMod (D.host.g kv.1))), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → (N ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k ↔ GlobalTheory.Mem.GroupLoc.ColCond X (D.naut.plGw kv.1 kv.2) k) := by
  atlas_forward_decl GlobalTheory.Mem.GroupLoc.mem_unipSym_iff_colCond
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.GroupLoc.Dual

open GlobalTheory.SeeConjRead (flagV)

section Comb

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {ρ k n : ℕ}

theorem fl_e (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n) (a : Fin ρ) (h : i.1 = a.1) :
    flagV ρ k n e f b z i = e a := by
  have := a.2
  unfold flagV
  rw [dif_pos (by omega)]
  exact congrArg e (Fin.ext h)

theorem fl_b (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n) (a : Fin k) (h : i.1 = ρ + a.1) :
    flagV ρ k n e f b z i = b a := by
  have := a.2
  unfold flagV
  rw [dif_neg (by omega), dif_pos (by omega)]
  exact congrArg b (Fin.ext (by simp only; omega))

theorem symmetricFlagBasisVectors_apply_centre (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n) (h : i.1 = ρ + k) :
    flagV ρ k n e f b z i = z := by
  unfold flagV
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos h]

theorem fl_f (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n) (a : Fin ρ) (h : i.1 + a.1 = 2 * ρ + k) :
    flagV ρ k n e f b z i = f a := by
  have := a.2
  unfold flagV
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  exact congrArg f (Fin.ext (by simp only; omega))

theorem img_e (hn : n = 2 * ρ + k + 1) (e f : Fin ρ → M) (b : Fin k → M) (z : M) {m : ℕ} (hm : m ≤ ρ) :
    e '' {a | a.1 < m} = flagV ρ k n e f b z '' {j | j.1 < m} := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    have := a.2
    exact ⟨⟨a.1, by omega⟩, ha, fl_e e f b z _ a rfl⟩
  · rintro ⟨j, hj, rfl⟩
    have hj' : j.1 < m := hj
    exact ⟨⟨j.1, by omega⟩, hj, (fl_e e f b z _ _ rfl).symm⟩

theorem range_eq_img (e : Fin ρ → M) : Set.range e = e '' {a | a.1 < ρ} := by
  rw [show {a : Fin ρ | a.1 < ρ} = Set.univ from Set.eq_univ_of_forall fun a => a.2, Set.image_univ]

theorem img_b (hn : n = 2 * ρ + k + 1) (e f : Fin ρ → M) (b : Fin k → M) (z : M) {m : ℕ} (hm : m ≤ k) :
    Set.range e ∪ b '' {a | a.1 < m} = flagV ρ k n e f b z '' {j | j.1 < ρ + m} := by
  ext x
  constructor
  · rintro (⟨a, rfl⟩ | ⟨a, ha, rfl⟩)
    · have := a.2
      exact ⟨⟨a.1, by omega⟩, show a.1 < ρ + m by omega, fl_e e f b z _ a rfl⟩
    · have ha' : a.1 < m := ha
      exact ⟨⟨ρ + a.1, by omega⟩, show ρ + a.1 < ρ + m by omega, fl_b e f b z _ a rfl⟩
  · rintro ⟨j, hj, rfl⟩
    have hj' : j.1 < ρ + m := hj
    by_cases h : j.1 < ρ
    · exact Or.inl ⟨⟨j.1, h⟩, (fl_e e f b z _ _ rfl).symm⟩
    · exact Or.inr ⟨⟨j.1 - ρ, by omega⟩, show j.1 - ρ < m by omega,
        (fl_b e f b z _ _ (show j.1 = ρ + (j.1 - ρ) by omega)).symm⟩

theorem img_f (hn : n = 2 * ρ + k + 1) (e f : Fin ρ → M) (b : Fin k → M) (z : M) {m : ℕ} (hm : m ≤ ρ) :
    f '' {a | a.1 < m} = flagV ρ k n e f b z '' {j | 2 * ρ + k < j.1 + m} := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : a.1 < m := ha
    exact ⟨⟨2 * ρ + k - a.1, by omega⟩, show 2 * ρ + k < 2 * ρ + k - a.1 + m by omega,
      fl_f e f b z _ a (show 2 * ρ + k - a.1 + a.1 = _ by omega)⟩
  · rintro ⟨j, hj, rfl⟩
    have hj' : 2 * ρ + k < j.1 + m := hj
    have := j.2
    exact ⟨⟨2 * ρ + k - j.1, by omega⟩, show 2 * ρ + k - j.1 < m by omega,
      (fl_f e f b z _ _ (show j.1 + (2 * ρ + k - j.1) = _ by omega)).symm⟩

theorem img_rev (hn : n = 2 * ρ + k + 1) (e f : Fin ρ → M) (b : Fin k → M) (z : M) {m : ℕ} (hm : m ≤ k) :
    Set.range f ∪ b '' {a | a.1 < m} =
      flagV ρ k n e f (fun i => b (Fin.rev i)) z '' {j | ρ + k ≤ j.1 + m ∧ j.1 ≠ ρ + k} := by
  ext x
  constructor
  · rintro (⟨a, rfl⟩ | ⟨a, ha, rfl⟩)
    · have := a.2
      exact ⟨⟨2 * ρ + k - a.1, by omega⟩, show ρ + k ≤ 2 * ρ + k - a.1 + m ∧ 2 * ρ + k - a.1 ≠ ρ + k by omega,
        fl_f e f _ z _ a (show 2 * ρ + k - a.1 + a.1 = _ by omega)⟩
    · have ha' : a.1 < m := ha
      refine ⟨⟨ρ + k - 1 - a.1, by omega⟩, show ρ + k ≤ ρ + k - 1 - a.1 + m ∧ ρ + k - 1 - a.1 ≠ ρ + k by omega, ?_⟩
      rw [fl_b e f _ z _ (Fin.rev a) (by rw [Fin.val_rev]; simp only; omega), Fin.rev_rev]
  · rintro ⟨j, hj, rfl⟩
    have hj' : ρ + k ≤ j.1 + m ∧ j.1 ≠ ρ + k := hj
    have := j.2
    by_cases h : j.1 < ρ + k
    · refine Or.inr ⟨Fin.rev ⟨j.1 - ρ, by omega⟩, ?_,
        (fl_b e f (fun i => b (Fin.rev i)) z j ⟨j.1 - ρ, by omega⟩ (show j.1 = ρ + (j.1 - ρ) by omega)).symm⟩
      show (Fin.rev _).1 < m
      rw [Fin.val_rev]; simp only; omega
    · exact Or.inl ⟨⟨2 * ρ + k - j.1, by omega⟩,
        (fl_f e f _ z _ _ (show j.1 + (2 * ρ + k - j.1) = _ by omega)).symm⟩

theorem comb (hn : n = 2 * ρ + k + 1) (e f : Fin ρ → M) (z : M) (b ε εd : Fin k → M) (W W' : Submodule R M)
    (T T' : M → M) (hneg : T' (-z) = -T' z) (P : Fin n → Fin n → Prop)
    (hcol : ∀ i S, T (flagV ρ k n e f ε z i) ∈ Submodule.span R (flagV ρ k n e f ε z '' S) ⊔ W ↔ ∀ j ∉ S, P j i)
    (hrow : ∀ j S, T' (flagV ρ k n f e εd (-z) j) ∈ Submodule.span R (flagV ρ k n f e εd (-z) '' S) ⊔ W' ↔
      ∀ i ∉ S, P j i)
    (hcase : (ε = b ∧ ∀ i, T' (b i) ∈ W') ∨ (εd = (fun i => b (Fin.rev i)) ∧ ∀ i, T (b i) ∈ W)) :
    (∀ i, T (flagV ρ k n e f ε z i) ∈ Submodule.span R (flagV ρ k n e f ε z '' {j | symAllowed ρ k i j}) ⊔ W) ↔
      ((∀ a : Fin ρ, T (e a) ∈ Submodule.span R (e '' {c | c.1 < a.1}) ⊔ W) ∧
        T z ∈ Submodule.span R (Set.range e) ⊔ W ∧
        ∀ i : Fin k, T (b i) ∈ Submodule.span R (Set.range e ∪ b '' {j | j.1 < i.1}) ⊔ W) ∧
      ((∀ a : Fin ρ, T' (e a) ∈ Submodule.span R (e '' {c | c.1 < a.1}) ⊔ W') ∧
        T' z ∈ Submodule.span R (Set.range e) ⊔ W' ∧
        ∀ i : Fin k, T' (b i) ∈ Submodule.span R (Set.range e ∪ b '' {j | j.1 < i.1}) ⊔ W') := by
  have c1 : ∀ (a : Fin ρ) (i : Fin n), i.1 = a.1 →
      (T (e a) ∈ Submodule.span R (e '' {c | c.1 < a.1}) ⊔ W ↔ ∀ j : Fin n, ¬ j.1 < a.1 → P j i) := fun a i h => by
    rw [img_e hn e f ε z a.2.le, ← fl_e e f ε z i a h]; exact hcol _ _
  have c2 : ∀ i : Fin n, i.1 = ρ + k →
      (T z ∈ Submodule.span R (Set.range e) ⊔ W ↔ ∀ j : Fin n, ¬ j.1 < ρ → P j i) := fun i h => by
    have := hcol i {j | j.1 < ρ}
    rw [symmetricFlagBasisVectors_apply_centre e f ε z i h, ← img_e hn e f ε z le_rfl, ← range_eq_img] at this
    exact this
  have c3 : ∀ (a : Fin k) (i : Fin n), i.1 = ρ + a.1 →
      (T (ε a) ∈ Submodule.span R (Set.range e ∪ ε '' {c | c.1 < a.1}) ⊔ W ↔
        ∀ j : Fin n, ¬ j.1 < ρ + a.1 → P j i) := fun a i h => by
    rw [img_b hn e f ε z a.2.le, ← fl_b e f ε z i a h]; exact hcol _ _
  have r1 : ∀ (a : Fin ρ) (j : Fin n), j.1 + a.1 = 2 * ρ + k →
      (T' (e a) ∈ Submodule.span R (e '' {c | c.1 < a.1}) ⊔ W' ↔
        ∀ i : Fin n, ¬ 2 * ρ + k < i.1 + a.1 → P j i) := fun a j h => by
    rw [img_f hn f e εd (-z) a.2.le, ← fl_f f e εd (-z) j a h]; exact hrow _ _
  have r2 : ∀ j : Fin n, j.1 = ρ + k →
      (T' z ∈ Submodule.span R (Set.range e) ⊔ W' ↔ ∀ i : Fin n, ¬ 2 * ρ + k < i.1 + ρ → P j i) := fun j h => by
    have := hrow j {i | 2 * ρ + k < i.1 + ρ}
    rw [symmetricFlagBasisVectors_apply_centre f e εd (-z) j h, ← img_f hn f e εd (-z) le_rfl, ← range_eq_img, hneg, neg_mem_iff] at this
    exact this
  have r3 : εd = (fun i => b (Fin.rev i)) → ∀ (a : Fin k) (j : Fin n), j.1 + a.1 + 1 = ρ + k →
      (T' (b a) ∈ Submodule.span R (Set.range e ∪ b '' {c | c.1 < a.1}) ⊔ W' ↔
        ∀ i : Fin n, ¬ (ρ + k ≤ i.1 + a.1 ∧ i.1 ≠ ρ + k) → P j i) := fun hd a j h => by
    have := hrow j {i | ρ + k ≤ i.1 + a.1 ∧ i.1 ≠ ρ + k}
    have ha := a.2
    rw [hd, fl_b f e _ (-z) j (Fin.rev a) (by rw [Fin.val_rev]; omega), ← img_rev hn f e b (-z) a.2.le,
      Fin.rev_rev] at this
    exact this
  simp only [hcol, Set.mem_setOf_eq, symAllowed]
  constructor
  · intro H
    refine ⟨⟨fun a => ?_, ?_, fun a => ?_⟩, fun a => ?_, ?_, fun a => ?_⟩
    · have := a.2
      exact (c1 a ⟨a.1, by omega⟩ rfl).2 fun j hj => H _ _ (by simp only; omega)
    · exact (c2 ⟨ρ + k, by omega⟩ rfl).2 fun j hj => H _ _ (by dsimp only; omega)
    · have := a.2
      rcases hcase with ⟨rfl, -⟩ | ⟨-, h⟩
      · exact (c3 a ⟨ρ + a.1, by omega⟩ rfl).2 fun j hj => H _ _ (by simp only; omega)
      · exact Submodule.mem_sup_right (h a)
    · have := a.2
      exact (r1 a ⟨2 * ρ + k - a.1, by omega⟩ (by simp only; omega)).2 fun j hj => H _ _ (by simp only; omega)
    · exact (r2 ⟨ρ + k, by omega⟩ rfl).2 fun j hj => H _ _ (by simp only; omega)
    · have := a.2
      rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
      · exact Submodule.mem_sup_right (h a)
      · exact (r3 h a ⟨ρ + k - 1 - a.1, by omega⟩ (by simp only; omega)).2 fun j hj => H _ _ (by simp only; omega)
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ i j hij
    have hi := i.2
    have hj := j.2
    by_cases a1 : i.1 < ρ
    · exact (c1 ⟨i.1, a1⟩ i rfl).1 (h1 _) j (by simp only; omega)
    by_cases a2 : i.1 = ρ + k
    · exact (c2 i a2).1 h2 j (by omega)
    by_cases a3 : ρ + k < j.1
    · exact (r1 ⟨2 * ρ + k - j.1, by omega⟩ j (by simp only; omega)).1 (h4 _) i (by simp only; omega)
    by_cases a4 : j.1 = ρ + k
    · exact (r2 j a4).1 h5 i (by omega)
    rcases hcase with ⟨rfl, -⟩ | ⟨h, -⟩
    · exact (c3 ⟨i.1 - ρ, by omega⟩ i (by simp only; omega)).1 (h3 _) j (by simp only; omega)
    · exact (r3 h ⟨ρ + k - 1 - j.1, by omega⟩ j (by simp only; omega)).1 (h6 _) i (by simp only; omega)

end Comb

open Formalism.L2.SG.Pf.unitaryCongruence GlobalTheory.Mem.SymChar GlobalTheory.Mem.SymFrame GlobalTheory.DimPartsCompare

variable {D : D7} (X : HidaSetting D)

theorem sig_mem (w : HeightOneSpectrum (𝓞 D.host.E)) {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F}
    (hc : c ∈ wInt X w) : sigA X.B.I c ∈ wInt X (cPl w) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨a, ⟨b, hb, hab⟩, rfl⟩ := hc
    rw [sigA_inclE]
    refine Submodule.subset_span ⟨RingOfIntegers.mapRingEquiv X.ιE.symm (GlobalTheory.SumWCompare.cj _ b),
      ⟨GlobalTheory.SumWCompare.cj _ b, by rw [mem_cPl, GlobalTheory.SumWCompare.cj_cj]; exact hb, X.ιE.apply_symm_apply _⟩, ?_⟩
    congr 1
    apply X.ιE.injective
    rw [X.ιE_conj, hab, ← star_conj, ← GlobalTheory.SumWCompare.cj_coe]
    exact (X.ιE.apply_symm_apply _).symm
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul r a _ ha =>
    show sigA X.B.I ((r : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * a) ∈ _
    rw [map_mul]
    exact (wInt X (cPl w)).smul_mem ⟨_, sigA_mem X.B.I r.2⟩ ha

theorem mul_mem_wInt (w : HeightOneSpectrum (𝓞 D.host.E)) {t c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F}
    (ht : t ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) (hc : c ∈ wInt X w) : t * c ∈ wInt X w :=
  (wInt X w).smul_mem ⟨t, ht⟩ hc

theorem coords (w : HeightOneSpectrum (𝓞 D.host.E)) {n : ℕ} (u v : Fin n → VA X.B.I)
    (hu : ∀ i, u i ∈ X.B.I.Lf) (hv : ∀ i, v i ∈ X.B.I.Lf)
    (hd : ∀ j i, hA X.B.I (v j) (u i) - (if i = j then 1 else 0) ∈ wInt X w)
    {y : VA X.B.I} (hy : GroupLoc.ModW X w (Set.range u) y) (S : Set (Fin n)) :
    GroupLoc.ModW X w (u '' S) y ↔ ∀ j ∉ S, hA X.B.I (v j) y ∈ wInt X w := by
  constructor
  · intro h j hj
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 h
    rw [hA_add_right]
    refine add_mem ?_ (hA_mem_wInt X w (hv j) ht)
    clear h hy
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨i, hi, rfl⟩ := hs
      have := hd j i
      rwa [if_neg (fun (e : i = j) => hj (e ▸ hi)), sub_zero] at this
    | zero => rw [hA_zero_right']; exact zero_mem _
    | add a b _ _ ha hb => rw [hA_add_right]; exact add_mem ha hb
    | smul r a _ ha =>
      show hA X.B.I (v j) ((r : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • a) ∈ _
      rw [hA_smul_right]
      exact mul_mem_wInt X w r.2 ha
  · intro h
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hs
    refine add_mem (sum_mem fun j _ => ?_) (Submodule.mem_sup_right ht)
    by_cases hj : j ∈ S
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩))
    refine Submodule.mem_sup_right (smul_mem_wLf_of_mem_wInt X w (c := c j) ?_ (hu j))
    have h1 := h j hj
    rw [hA_add_right, hA_sum_right'] at h1
    have h2 := sub_mem h1 (hA_mem_wInt X w (hv j) ht)
    rw [add_sub_cancel_right] at h2
    have h3 : ∑ i, ((c i : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) *
        (hA X.B.I (v j) (u i) - (if i = j then 1 else 0))) ∈ wInt X w :=
      sum_mem fun i _ => mul_mem_wInt X w (c i).2 (hd j i)
    have h4 : ∀ i, hA X.B.I (v j) (c i • u i) =
        (c i : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * hA X.B.I (v j) (u i) := fun i => hA_smul_right _ _ _ _
    simp only [h4] at h2
    have h5 := sub_mem h2 h3
    simpa [mul_sub, Finset.sum_sub_distrib] using h5

theorem pres_w (w : HeightOneSpectrum (𝓞 D.host.E)) {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (S : Set (VA X.B.I))
    (hS : ∀ s ∈ S, GroupLoc.ModW X w S ((X.B.I.fmat x - 1) *ᵥ s)) {y : VA X.B.I} (hy : GroupLoc.ModW X w S y) :
    GroupLoc.ModW X w S (X.B.I.fmat x *ᵥ y) := by
  have h : Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) S ⊔ wLf X w ≤
      (Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) S ⊔ wLf X w).comap (mvO X.B.I (X.B.I.fmat x)) := by
    refine sup_le (Submodule.span_le.2 fun s hs => ?_)
      (fun s hs => Submodule.mem_sup_right (fmat_mulVec_mem_wLf X w hx hs))
    show GroupLoc.ModW X w S (X.B.I.fmat x *ᵥ s)
    have e : X.B.I.fmat x *ᵥ s = s + (X.B.I.fmat x - 1) *ᵥ s := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e]
    exact add_mem (Submodule.mem_sup_left (Submodule.subset_span hs)) (hS s hs)
  exact h hy

theorem modW_mono {w : HeightOneSpectrum (𝓞 D.host.E)} {S T : Set (VA X.B.I)} (h : S ⊆ T) {y : VA X.B.I}
    (hy : GroupLoc.ModW X w S y) : GroupLoc.ModW X w T y :=
  (sup_le_sup_right (Submodule.span_mono h) _ : Submodule.span _ S ⊔ wLf X w ≤ _) hy

theorem condAt_inv (w : HeightOneSpectrum (𝓞 D.host.E)) {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (h : CondAt X w x) :
    CondAt X w x⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := h
  have key : ∀ (S : Set (VA X.B.I)) (y : VA X.B.I), (∀ s ∈ S, GroupLoc.ModW X w S ((X.B.I.fmat x⁻¹ - 1) *ᵥ s)) →
      GroupLoc.ModW X w S ((X.B.I.fmat x - 1) *ᵥ y) → GroupLoc.ModW X w S ((X.B.I.fmat x⁻¹ - 1) *ᵥ y) := fun S y hS hy => by
    rw [inv_id]
    exact neg_mem (pres_w X w (K_inv _ hx) S hS hy)
  have e1 : ∀ m : ℕ, ∀ a : Fin D.R.rS, a.1 < m →
      GroupLoc.ModW X w (X.e0 '' {b | b.1 < a.1}) ((X.B.I.fmat x⁻¹ - 1) *ᵥ X.e0 a) := by
    intro m
    induction m with
    | zero => intro a h; exact absurd h (Nat.not_lt_zero _)
    | succ m ih =>
      intro a ha
      refine key _ _ ?_ (h1 a)
      rintro _ ⟨b, hb, rfl⟩
      have hb' : b.1 < a.1 := hb
      exact modW_mono X (Set.image_mono (lt_sub hb'.le)) (ih b (by omega))
  have e3 : ∀ m : ℕ, ∀ i : Fin D.R.k, i.1 < m →
      GroupLoc.ModW X w (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1}) ((X.B.I.fmat x⁻¹ - 1) *ᵥ X.bw i) := by
    intro m
    induction m with
    | zero => intro a h; exact absurd h (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      refine key _ _ ?_ (h3 i)
      rintro _ (⟨b, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact modW_mono X ((Set.image_subset_range _ _).trans Set.subset_union_left) (e1 _ b (Nat.lt_succ_self _))
      · have hj' : j.1 < i.1 := hj
        exact modW_mono X (Set.union_subset_union_right _ (Set.image_mono (lt_sub hj'.le))) (ih j (by omega))
  refine ⟨fun a => e1 _ a (Nat.lt_succ_self _), key _ _ ?_ h2, fun i => e3 _ i (Nat.lt_succ_self _)⟩
  rintro _ ⟨b, rfl⟩
  exact modW_mono X (Set.image_subset_range _ _) (e1 _ b (Nat.lt_succ_self _))

theorem rank_eq (D : D7) : D.R.r = 2 * D.R.rS + D.R.k + 1 := by
  have := D.R.rS_two
  unfold Ranks.r
  omega

theorem span_frame (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) (u : Fin D.R.r → VA X.B.I)
    (he : ∀ a, GroupLoc.ModW X w (Set.range u) (X.e0 a)) (hf : ∀ a, GroupLoc.ModW X w (Set.range u) (X.f0 a))
    (hz : GroupLoc.ModW X w (Set.range u) X.z0) (hb : ∀ a, GroupLoc.ModW X w (Set.range u) (X.bw a))
    (hb' : ∀ a, GroupLoc.ModW X w (Set.range u) (X.bwd a)) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) :
    GroupLoc.ModW X w (Set.range u) y := by
  have h := X.latticeSpan y hy
  refine (sup_le (Submodule.span_le.2 ?_) (le_trans ?_ le_sup_right) :
    _ ≤ Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) (Set.range u) ⊔ wLf X w) h
  · rintro _ ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl) | ⟨a, rfl⟩) | ⟨a, rfl⟩)
    exacts [he a, hf a, hz, hb a, hb' a]
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact smul_mem_wLf_of_mem_wInt X w (wInt_of_zmod X k hg ⟨1, one_mem _, (mul_one _).symm⟩) hx

theorem flagV_mem {e f : Fin D.R.rS → VA X.B.I} {b : Fin D.R.k → VA X.B.I} {z : VA X.B.I}
    (he : ∀ a, e a ∈ X.B.I.Lf) (hf : ∀ a, f a ∈ X.B.I.Lf) (hb : ∀ a, b a ∈ X.B.I.Lf) (hz : z ∈ X.B.I.Lf)
    (i : Fin D.R.r) : flagV D.R.rS D.R.k D.R.r e f b z i ∈ X.B.I.Lf := by
  unfold flagV
  split_ifs
  exacts [he _, hb _, hz, hf _, zero_mem _]

theorem modW_range {w : HeightOneSpectrum (𝓞 D.host.E)} {u : Fin D.R.r → VA X.B.I} {y : VA X.B.I} (i : Fin D.R.r)
    (h : u i = y) : GroupLoc.ModW X w (Set.range u) y :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨i, h⟩)

theorem one_sub_ew (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) (h : EwAt X w) : 1 - X.ew ∈ wInt X w := by
  have h1 := hA_mem_wInt X w X.vectorsInLattice.2.1 (h _ X.vectorsInLattice.2.1)
  rw [hA_smul_right] at h1
  have h2 := mul_mem_wInt X w (sub_mem (one_mem _) X.ew_int) (wInt_of_zmod X k hg X.formsAtZero.1)
  have h3 := sub_mem h2 h1
  rwa [mul_add, add_sub_cancel_left, mul_one] at h3

open Classical in

def epsD (w : HeightOneSpectrum (𝓞 D.host.E)) : Fin D.R.k → VA X.B.I :=
  if EwAt X w then X.bwd else fun i => X.bw (Fin.rev i)

def dualVec (w : HeightOneSpectrum (𝓞 D.host.E)) : Fin D.R.r → VA X.B.I :=
  flagV D.R.rS D.R.k D.R.r X.f0 X.e0 (epsD X w) (-X.z0)

theorem hA_neg_left (x y : VA X.B.I) : hA X.B.I (-x) y = -hA X.B.I x y := by
  rw [← neg_one_smul (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) x, hA_smul_left, map_neg, map_one, neg_one_mul]

theorem hA_adj (x : X.B.I.Gf) (a b : VA X.B.I) :
    hA X.B.I b ((X.B.I.fmat x⁻¹ - 1) *ᵥ a) = sigA X.B.I (hA X.B.I a ((X.B.I.fmat x - 1) *ᵥ b)) := by
  have h := GlobalTheory.St.G.FrameClose.hA_unitary x b (X.B.I.fmat x⁻¹ *ᵥ a)
  have e : X.B.I.fmat x * X.B.I.fmat x⁻¹ = 1 := by rw [← fmat_mul, mul_inv_cancel, fmat_one]
  rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec] at h
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right, map_sub]
  rw [← h, ← hA_symm, ← hA_symm]

theorem colCond_iff_condAt : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (GlobalTheory.Mem.GroupLoc.ColCond X (D.naut.plGw kv.1 kv.2) k ↔ GlobalTheory.Mem.GroupLoc.CondAt X (D.naut.plGw kv.1 kv.2) k ∧ GlobalTheory.Mem.GroupLoc.CondAt X (GlobalTheory.DimPartsCompare.cPl (D.naut.plGw kv.1 kv.2)) k) := by
  intro D X hI hι hgs x hx kv
  have hg := hgs kv
  have hn := rank_eq D
  have hA_e0 := hA_e0_symVec D X kv hg
  have hA_z0 := ZPair.hA_z0_symVec D X kv hg
  have hA_bw := Resid.hA_bw_symVec_not_ewAt D X kv hg
  have hsig := sigA_ew_sub_one_mem_wInt D X hI hι kv hg
  generalize D.naut.plGw kv.1 kv.2 = w at *
  have hg' : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (cPl w).asIdeal := by rw [mem_cPl, map_natCast]; exact hg
  obtain ⟨ief, iz, ib⟩ := X.vectorsInLattice
  have hse := sigA_mem X.B.I X.ew_int

  have p1 : EwAt X w → sigA X.B.I X.ew ∈ wInt X w := fun h => by
    have := mul_mem_wInt X w hse (one_sub_ew X w kv.1 hg h)
    rwa [mul_sub, mul_one, mul_comm, X.ew_orth, sub_zero] at this
  have p2 : ¬ EwAt X w → X.ew ∈ wInt X w := fun h => by
    have := neg_mem (mul_mem_wInt X w X.ew_int (hsig h))
    rwa [mul_sub, mul_one, X.ew_orth, zero_sub, neg_neg] at this
  have q1 : EwAt X w → ∀ i, X.bwd i ∈ wLf X w := fun h i => by
    rw [X.bwd_w]; exact smul_mem_wLf_of_mem_wInt X w (p1 h) (ib i).2
  have q2 : EwAt X w → ∀ i, X.bw i ∈ wLf X (cPl w) := fun h i => by
    have := sig_mem X w (p1 h)
    rw [sigA_sigA] at this
    rw [X.bw_w]; exact smul_mem_wLf_of_mem_wInt X _ this (ib i).1
  have q3 : ¬ EwAt X w → ∀ i, X.bw i ∈ wLf X w := fun h i => by
    rw [X.bw_w]; exact smul_mem_wLf_of_mem_wInt X w (p2 h) (ib i).1
  have q4 : ¬ EwAt X w → ∀ i, X.bwd i ∈ wLf X (cPl w) := fun h i => by
    rw [X.bwd_w]; exact smul_mem_wLf_of_mem_wInt X _ (sig_mem X w (p2 h)) (ib i).2
  have hu : ∀ i, symVec X w i ∈ X.B.I.Lf :=
    flagV_mem X (fun a => (ief a).1) (fun a => (ief a).2)
      (fun a => by unfold epsW; split_ifs; exacts [(ib _).1, (ib _).2]) iz
  have hv : ∀ i, dualVec X w i ∈ X.B.I.Lf :=
    flagV_mem X (fun a => (ief a).2) (fun a => (ief a).1)
      (fun a => by unfold epsD; split_ifs; exacts [(ib _).2, (ib _).1]) (neg_mem iz)

  have hd : ∀ j i, hA X.B.I (dualVec X w j) (symVec X w i) - (if i = j then 1 else 0) ∈ wInt X w := by
    intro j i
    have hj := j.2
    unfold dualVec
    by_cases a1 : j.1 < D.R.rS
    · rw [fl_e _ _ _ _ j ⟨j.1, a1⟩ rfl]
      exact hA_symVec_sub_ite_mem_wInt D X w kv.1 hg ⟨j.1, a1⟩ i
    by_cases a2 : j.1 < D.R.rS + D.R.k
    · rw [fl_b _ _ _ _ j ⟨j.1 - D.R.rS, by omega⟩ (by simp only; omega)]
      unfold epsD
      by_cases h : EwAt X w
      · rw [if_pos h]
        have := Resid.hA_bwd_symVec D X w kv.1 hg h (one_sub_ew X w kv.1 hg h) ⟨j.1 - D.R.rS, by omega⟩ i
        rwa [show Resid.posB D ⟨j.1 - D.R.rS, by omega⟩ = j from Fin.ext (by simp only [Resid.posB]; omega)] at this
      · rw [if_neg h]
        have := hA_bw h (hsig h) (Fin.rev ⟨j.1 - D.R.rS, by omega⟩) i
        rwa [show D.R.rS + D.R.k - 1 - (Fin.rev (⟨j.1 - D.R.rS, by omega⟩ : Fin D.R.k)).1 = j.1 by
          rw [Fin.val_rev]; simp only; omega, if_congr Fin.val_inj rfl rfl] at this
    by_cases a3 : j.1 = D.R.rS + D.R.k
    · rw [symmetricFlagBasisVectors_apply_centre _ _ _ _ j a3, hA_neg_left]
      have := neg_mem (hA_z0 i)
      rw [← a3, if_congr Fin.val_inj rfl rfl] at this
      convert this using 1
      split_ifs <;> ring
    · rw [fl_f _ _ _ _ j ⟨2 * D.R.rS + D.R.k - j.1, by omega⟩ (by simp only; omega)]
      have := hA_e0 ⟨2 * D.R.rS + D.R.k - j.1, by omega⟩ i
      rwa [show 2 * D.R.rS + D.R.k - (⟨2 * D.R.rS + D.R.k - j.1, by omega⟩ : Fin D.R.rS).1 = j.1 by
          simp only; omega, if_congr Fin.val_inj rfl rfl] at this
  have hd' : ∀ i j, hA X.B.I (symVec X w i) (dualVec X w j) - (if j = i then 1 else 0) ∈ wInt X (cPl w) := by
    intro i j
    have := sig_mem X w (hd j i)
    rwa [map_sub, ← hA_symm, apply_ite (sigA X.B.I), map_one, map_zero, if_congr eq_comm rfl rfl] at this

  have su : ∀ y ∈ X.B.I.Lf, GroupLoc.ModW X w (Set.range (symVec X w)) y := fun y hy => by
    refine span_frame X w kv.1 hg _ (fun a => ?_) (fun a => ?_) ?_ (fun a => ?_) (fun a => ?_) hy
    · have := a.2
      exact modW_range X ⟨a.1, by omega⟩ (fl_e _ _ _ _ _ a rfl)
    · have := a.2
      exact modW_range X ⟨2 * D.R.rS + D.R.k - a.1, by omega⟩ (fl_f _ _ _ _ _ a (by simp only; omega))
    · exact modW_range X ⟨D.R.rS + D.R.k, by omega⟩ (symmetricFlagBasisVectors_apply_centre _ _ _ _ _ rfl)
    · have := a.2
      by_cases h : EwAt X w
      · exact modW_range X ⟨D.R.rS + a.1, by omega⟩ ((fl_b _ _ _ _ _ a rfl).trans (by rw [epsW, if_pos h]))
      · exact Submodule.mem_sup_right (q3 h a)
    · have := a.rev.2
      by_cases h : EwAt X w
      · exact Submodule.mem_sup_right (q1 h a)
      · exact modW_range X ⟨D.R.rS + a.rev.1, by omega⟩ ((fl_b _ _ _ _ _ a.rev rfl).trans
          (by rw [epsW, if_neg h]; exact congrArg X.bwd (Fin.rev_rev a)))
  have sv : ∀ y ∈ X.B.I.Lf, GroupLoc.ModW X (cPl w) (Set.range (dualVec X w)) y := fun y hy => by
    refine span_frame X _ kv.1 hg' _ (fun a => ?_) (fun a => ?_) ?_ (fun a => ?_) (fun a => ?_) hy
    · have := a.2
      exact modW_range X ⟨2 * D.R.rS + D.R.k - a.1, by omega⟩ (fl_f _ _ _ _ _ a (by simp only; omega))
    · have := a.2
      exact modW_range X ⟨a.1, by omega⟩ (fl_e _ _ _ _ _ a rfl)
    · exact neg_mem_iff.1 (modW_range X ⟨D.R.rS + D.R.k, by omega⟩ (symmetricFlagBasisVectors_apply_centre _ _ _ _ _ rfl))
    · have := a.rev.2
      by_cases h : EwAt X w
      · exact Submodule.mem_sup_right (q2 h a)
      · exact modW_range X ⟨D.R.rS + a.rev.1, by omega⟩ ((fl_b _ _ _ _ _ a.rev rfl).trans
          (by rw [epsD, if_neg h]; exact congrArg X.bw (Fin.rev_rev a)))
    · have := a.2
      by_cases h : EwAt X w
      · exact modW_range X ⟨D.R.rS + a.1, by omega⟩ ((fl_b _ _ _ _ _ a rfl).trans (by rw [epsD, if_pos h]))
      · exact Submodule.mem_sup_right (q4 h a)
  have sub_w : ∀ (w' : HeightOneSpectrum (𝓞 D.host.E)) (y : X.B.I.Gf), y ∈ X.B.I.Kset → ∀ s ∈ wLf X w',
      (X.B.I.fmat y - 1) *ᵥ s ∈ wLf X w' := fun w' y hy s hs => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (fmat_mulVec_mem_wLf X w' hy hs) hs
  have main := comb (R := Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hn X.e0 X.f0 X.z0 X.bw (epsW X w) (epsD X w) (wLf X w)
    (wLf X (cPl w)) (fun y => (X.B.I.fmat x - 1) *ᵥ y) (fun y => (X.B.I.fmat x⁻¹ - 1) *ᵥ y)
    (Matrix.mulVec_neg _ _)
    (fun j i => hA X.B.I (dualVec X w j) ((X.B.I.fmat x - 1) *ᵥ symVec X w i) ∈ wInt X w)
    (fun i S => coords X w _ _ hu hv hd (su _ (K_sub_mv _ hx (hu i))) S)
    (fun j S => (coords X (cPl w) _ _ hv hu hd' (sv _ (K_sub_mv _ (K_inv _ hx) (hv j))) S).trans
      (forall₂_congr fun i _ => by
        rw [hA_adj]
        refine ⟨fun h => ?_, sig_mem X w⟩
        have := sig_mem X _ h
        rwa [sigA_sigA, cPl_cPl] at this))
    (by
      by_cases h : EwAt X w
      · exact Or.inl ⟨by rw [epsW, if_pos h], fun i => sub_w _ _ (K_inv _ hx) _ (q2 h i)⟩
      · exact Or.inr ⟨by rw [epsD, if_neg h], fun i => sub_w _ _ hx _ (q3 h i)⟩)
  refine Iff.trans main (and_congr Iff.rfl ⟨fun h => ?_, fun h => condAt_inv X _ hx h⟩)
  have := condAt_inv X (cPl w) (K_inv _ hx) h
  rwa [inv_inv] at this

end GlobalTheory.Mem.GroupLoc.Dual

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPositionColumnCond_iff_congruence_conj : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (GlobalTheory.Mem.GroupLoc.ColCond X (D.naut.plGw kv.1 kv.2) k ↔ GlobalTheory.Mem.GroupLoc.CondAt X (D.naut.plGw kv.1 kv.2) k ∧ GlobalTheory.Mem.GroupLoc.CondAt X (GlobalTheory.DimPartsCompare.cPl (D.naut.plGw kv.1 kv.2)) k) := by
  atlas_forward_decl GlobalTheory.Mem.GroupLoc.Dual.colCond_iff_condAt
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.GroupLoc

theorem membership_iff_unipSym : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ Ns : G0g D.nd, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))) → (k ∈ X.K2 ↔ ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k) := by
  intro D X h hE hg k hk Ns hNs
  have hK2 : k ∈ X.K2 ↔ K2cong X.B.I X.B.g X.e0 X.z0 X.bw k := ⟨fun hm => hm.2, fun hm => ⟨hk, hm⟩⟩
  have hLf : ∀ y ∈ X.B.I.Lf, (X.B.I.fmat k - 1) *ᵥ y ∈ X.B.I.Lf := by
    intro y hy
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem ((hk y).1 hy) hy
  have hS1 : ∀ a : Fin D.R.rS, X.e0 '' {b | b.1 < a.1} ⊆ X.B.I.Lf := by
    rintro a _ ⟨b, -, rfl⟩; exact (X.vectorsInLattice.1 b).1
  have hS2 : Set.range X.e0 ⊆ X.B.I.Lf := by
    rintro _ ⟨b, rfl⟩; exact (X.vectorsInLattice.1 b).1
  have hS3 : ∀ i : Fin D.R.k, Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1} ⊆ X.B.I.Lf := by
    rintro i _ (⟨b, rfl⟩ | ⟨j, -, rfl⟩)
    · exact (X.vectorsInLattice.1 b).1
    · exact (X.vectorsInLattice.2.2 j).1
  have hK : K2cong X.B.I X.B.g X.e0 X.z0 X.bw k ↔
      ∀ w : HeightOneSpectrum (𝓞 D.host.E), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → CondAt X w k := by
    have e1 := fun a => GlobalTheory.T.inMod_iff_forall_place_memSpanModulo D X h hE _ (hS1 a) _ (hLf _ (X.vectorsInLattice.1 a).1)
    have e2 := GlobalTheory.T.inMod_iff_forall_place_memSpanModulo D X h hE _ hS2 _ (hLf _ X.vectorsInLattice.2.1)
    have e3 := fun i => GlobalTheory.T.inMod_iff_forall_place_memSpanModulo D X h hE _ (hS3 i) _ (hLf _ (X.vectorsInLattice.2.2 i).1)
    constructor
    · rintro ⟨h1, h2, h3⟩ w hw
      exact ⟨fun a => (e1 a).1 (h1 a) w hw, e2.1 h2 w hw, fun i => (e3 i).1 (h3 i) w hw⟩
    · intro H
      exact ⟨fun a => (e1 a).2 fun w hw => (H w hw).1 a, e2.2 fun w hw => (H w hw).2.1,
        fun i => (e3 i).2 fun w hw => (H w hw).2.2 i⟩
  have hgE : ((X.B.g : ℕ) : 𝓞 D.host.E) = ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
    rw [X.g_eq, Nat.cast_mul]
  have hgw : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := by
    rintro ⟨kk, v⟩
    rw [hgE]
    fin_cases kk
    · exact Ideal.mul_mem_right _ _ (hg ⟨0, v⟩)
    · exact Ideal.mul_mem_left _ _ (hg ⟨1, v⟩)
  have hP : (∀ w : HeightOneSpectrum (𝓞 D.host.E), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → CondAt X w k) ↔
      ∀ kv : (Σ k : Fin 2, D.nd.PlG k), CondAt X (D.naut.plGw kv.1 kv.2) k ∧
        CondAt X (GlobalTheory.DimPartsCompare.cPl (D.naut.plGw kv.1 kv.2)) k := by
    constructor
    · intro H kv
      refine ⟨H _ (hgw kv), H _ ?_⟩
      rw [GlobalTheory.DimPartsCompare.mem_cPl, map_natCast]
      exact hgw kv
    · intro H w hw
      rw [hgE] at hw
      rcases w.isPrime.mem_or_mem hw with h0 | h1
      · obtain ⟨v, rfl | rfl⟩ := GlobalTheory.DimPartsCompare.cover 0 w h0
        · exact (H ⟨0, v⟩).1
        · exact (H ⟨0, v⟩).2
      · obtain ⟨v, rfl | rfl⟩ := GlobalTheory.DimPartsCompare.cover 1 w h1
        · exact (H ⟨1, v⟩).1
        · exact (H ⟨1, v⟩).2
  rw [hK2, hK, hP]
  exact forall_congr' fun kv => (GlobalTheory.T.symmetricPositionColumnCond_iff_congruence_conj D X h hE hg k hk kv).symm.trans (GlobalTheory.T.symmetricFrame_matrix_mem_unipotent_iff_column_span D X h hE hg k hk kv (Ns kv) (hNs kv)).symm

end GlobalTheory.Mem.GroupLoc
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_deeperLevel_iff_matrices_mod_place_symmetric : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ Ns : G0g D.nd, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))) → (k ∈ X.K2 ↔ ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k) := by
  atlas_forward_decl GlobalTheory.Mem.GroupLoc.membership_iff_unipSym
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.SymFrame.conj_symLevel : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (eR : G' ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ x : X.B.I.E, HEq (X.ιE x) x) → R.toLevCh.Is A.μ0 → (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) → (∀ kv, R.C.P.Div kv.1 (plg kv).1) → (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) → ∀ (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsGenericPsi R.Pg ψ0 → ∀ π : Equiv.Perm (Fin D.R.r), IsSymOrd D.R.rS D.R.k π → ∀ (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), IsRedHom X red → FixRed X red b → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ c : G0g D.nd, ∀ k ∈ X.B.I.Kset, (k ∈ X.K2 ↔ reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H) ∧ ∀ hk : reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H, (((PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨_, hk⟩ : ℂˣ) : ℂ) = star (X.chi2 k) := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R X h eR plg iso hpin hIs hplg hDiv heG ψ0 hψ0 π hπ red b hred hfix hw
  classical
  obtain ⟨P, hP⟩ := GlobalTheory.T.symmetricFrame_reduces_to_basis_mod_place D X h hpin b (fun kv => (hfix kv).1) hw π
  obtain ⟨ψ', a, hψ'1, hchi⟩ := GlobalTheory.T.star_character_eq_prod_additive_characters_root_alt D X h hpin hw
  have hsc : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ d : Fin D.R.r → (ZMod (D.host.g kv.1))ˣ,
      ∀ u : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), u ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k →
        ψ' kv (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a kv i j : ZMod (D.host.g kv.1)) * u.val i j else 0) =
          (ψ0 (plg kv)).compAddMonoidHom (iso kv).toAddMonoidHom
            (edgeSum (symEdge D.R.rS D.R.k) ((GlobalTheory.SeeConjRead.diagGL d)⁻¹ * u * GlobalTheory.SeeConjRead.diagGL d)) := by
    intro kv
    haveI := Fact.mk (D.host.g_prime kv.1)
    refine GlobalTheory.SeeConjScale.scale_conj (Field.toIsField _) D.R.rS D.R.k (ψ' kv) _ (hψ'1 kv) ?_ (a kv)
    intro h1
    apply hψ0 _ (plg kv).2
    ext y
    have := DFunLike.congr_fun h1 ((iso kv).symm y)
    simpa using this
  choose d hd using hsc
  let c : G0g D.nd := fun kv => P kv * GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j))
  refine ⟨c, fun k hk => ?_⟩
  let Ns : G0g D.nd := fun kv => Units.map (Matrix.reindexAlgEquiv (ZMod (D.host.g kv.1)) (ZMod (D.host.g kv.1)) π.symm).toMonoidHom
    ((P kv)⁻¹ * red k kv * P kv)
  have hNs : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) = (((((P kv)⁻¹ * red k kv * P kv) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))).submatrix π π := by
    intro kv
    ext i j
    simp [Ns, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
  have hMat : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2)
      (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) := by
    intro kv
    rw [hNs kv]
    exact GlobalTheory.Mem.SymFrame.isMatIn_perm _ k _ π (GlobalTheory.T.matrixModPlace_basisChange_eq_conj D X red b hfix kv (hw kv) (P kv) _ (hP kv) k hk)
  have hval : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), reord π (R.eG (eR.symm (c⁻¹ * red k * c))) (plg kv) =
      Formalism.UG.bc ((iso kv : ZMod (D.host.g kv.1) ≃+* kP (plg kv).1) : ZMod (D.host.g kv.1) →+* kP (plg kv).1)
        ((GlobalTheory.SeeConjRead.diagGL (d kv))⁻¹ * Ns kv * GlobalTheory.SeeConjRead.diagGL (d kv)) := by
    intro kv
    have e1 : (c⁻¹ * red k * c) kv = (GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)))⁻¹ *
        ((P kv)⁻¹ * red k kv * P kv) * GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)) := by
      simp only [c, Pi.mul_apply, Pi.inv_apply, mul_inv_rev, mul_assoc]
    have e2 := heG (eR.symm (c⁻¹ * red k * c)) kv
    rw [MulEquiv.apply_symm_apply, e1] at e2
    apply Units.ext
    ext i j
    have e3 : ((reord π (R.eG (eR.symm (c⁻¹ * red k * c))) (plg kv) : GL (Fin D.R.r) (kP (plg kv).1)) :
        Matrix (Fin D.R.r) (Fin D.R.r) (kP (plg kv).1)) i j =
        ((R.eG (eR.symm (c⁻¹ * red k * c)) (plg kv) : GL (Fin D.R.r) (kP (plg kv).1)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (kP (plg kv).1)) (π i) (π j) := by
      simp [reord, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
    rw [e3, e2]
    show (iso kv) ((((GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)))⁻¹ *
        ((P kv)⁻¹ * red k kv * P kv) * GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) (π i) (π j)) =
      (iso kv) (((((GlobalTheory.SeeConjRead.diagGL (d kv))⁻¹ * Ns kv * GlobalTheory.SeeConjRead.diagGL (d kv)) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) i j)
    rw [GlobalTheory.SeeConjRead.diagGL_conj_apply, GlobalTheory.SeeConjRead.diagGL_conj_apply, hNs kv]
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  have hmemiff : reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H ↔
      ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k := by
    show _ ∈ Subgroup.pi Set.univ _ ↔ _
    rw [Subgroup.mem_pi]
    constructor
    · intro H kv
      have h1 := H (plg kv) (Set.mem_univ _)
      rw [hval kv, GlobalTheory.Mem.SymFrame.mem_unipSym_bc] at h1
      exact (GlobalTheory.SeeConjRead.unipSym_conj_iff _ _ _ _).2 h1
    · intro H PP _
      obtain ⟨kv, rfl⟩ := plg.surjective PP
      rw [hval kv, GlobalTheory.Mem.SymFrame.mem_unipSym_bc]
      exact (GlobalTheory.SeeConjRead.unipSym_conj_iff _ _ _ _).1 (H kv)
  have hK2 := GlobalTheory.T.mem_deeperLevel_iff_matrices_mod_place_symmetric D X h hpin hw k hk Ns hMat
  refine ⟨hK2.trans hmemiff.symm, fun hx => ?_⟩
  have hU := hmemiff.1 hx
  have hk2 : k ∈ X.K2 := hK2.2 hU
  rw [hchi k hk2 Ns hMat hU]
  have hchiv : (((PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨_, hx⟩ : ℂˣ) : ℂ) =
      ∏ PP : R.Pg, ψ0 PP.1 (edgeSum (symEdge D.R.rS D.R.k) (reord π (R.eG (eR.symm (c⁻¹ * red k * c))) PP)) := by
    unfold PsharpSym LevelP.ofLocal
    rw [MonoidHom.finset_prod_apply, Units.coe_prod]
    rfl
  rw [hchiv]
  refine (Fintype.prod_equiv plg _ _ (fun _ => rfl)).symm.trans (Finset.prod_congr rfl fun kv _ => ?_)
  rw [hval kv, GlobalTheory.Mem.SymFrame.edgeSum_bc, hd kv _ (hU kv)]
  rfl
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_level_conjCharacter_symmetricLevel : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (eR : G' ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ x : X.B.I.E, HEq (X.ιE x) x) → R.toLevCh.Is A.μ0 → (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) → (∀ kv, R.C.P.Div kv.1 (plg kv).1) → (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) → ∀ (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsGenericPsi R.Pg ψ0 → ∀ π : Equiv.Perm (Fin D.R.r), IsSymOrd D.R.rS D.R.k π → ∀ (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), IsRedHom X red → FixRed X red b → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ c : G0g D.nd, ∀ k ∈ X.B.I.Kset, (k ∈ X.K2 ↔ reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H) ∧ ∀ hk : reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H, (((PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨_, hk⟩ : ℂˣ) : ℂ) = star (X.chi2 k) := by
  atlas_forward_decl GlobalTheory.Mem.SymFrame.conj_symLevel
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

theorem cong_zsmul {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (a a' : Fin r → ℤ) (h : ∀ l, (a l : ZMod g) = a' l) :
    ∑ l, a l • u l - ∑ l, a' l • u l ∈ W := by
  rw [← Finset.sum_sub_distrib]
  refine W.sum_mem fun l _ => ?_
  have h1 : ((a l - a' l : ℤ) : ZMod g) = 0 := by push_cast; rw [h l, sub_self]
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1
  rw [← sub_smul, ht, mul_comm, mul_zsmul, natCast_zsmul]
  exact W.zsmul_mem (hu l) t

theorem cong_nsmul {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (a a' : Fin r → ℕ) (h : ∀ l, (a l : ZMod g) = a' l) :
    ∑ l, a l • u l - ∑ l, a' l • u l ∈ W := by
  have := cong_zsmul W u hu (fun l => (a l : ℤ)) (fun l => (a' l : ℤ)) (fun l => by push_cast; exact h l)
  simpa only [natCast_zsmul] using this

theorem sum_nsmul_sum {V : Type*} [AddCommGroup V] {r : ℕ} (u : Fin r → V) (a : Fin r → ℕ)
    (b : Fin r → Fin r → ℕ) :
    ∑ j, a j • ∑ l, b l j • u l = ∑ l, (∑ j, a j * b l j) • u l := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem rebase_rel {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} [NeZero g] (F : V →+ V) (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (M c d : Matrix (Fin r) (Fin r) (ZMod g)) (hcd : c * d = 1)
    (h : ∀ i, F (u i) - ∑ j, (M j i).val • u j ∈ W) (i : Fin r) :
    F (∑ j, (c j i).val • u j) - ∑ m, ((d * M * c) m i).val • ∑ l, (c l m).val • u l ∈ W := by
  rw [map_sum]
  simp only [map_nsmul]
  have e1 : ∑ j, (c j i).val • F (u j) = ∑ j, (c j i).val • (F (u j) - ∑ l, (M l j).val • u l) +
      ∑ j, (c j i).val • ∑ l, (M l j).val • u l := by
    rw [← Finset.sum_add_distrib]; congr 1; funext j; rw [← smul_add, sub_add_cancel]
  rw [e1, sum_nsmul_sum, sum_nsmul_sum, add_sub_assoc]
  refine W.add_mem (W.sum_mem fun j _ => W.nsmul_mem (h j) _) (cong_nsmul W u hu _ _ fun l => ?_)
  have e2 : c * (d * M * c) = M * c := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hcd, Matrix.one_mul]
  have e3 := congrFun (congrFun e2 l) i
  rw [Matrix.mul_apply, Matrix.mul_apply] at e3
  simp only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [show ∑ x, c x i * M l x = ∑ j, M l j * c j i from Finset.sum_congr rfl fun _ _ => mul_comm _ _, ← e3]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem rebase_span {V : Type*} [AddCommGroup V] (W : AddSubgroup V) {r g : ℕ} [NeZero g] (u : Fin r → V)
    (hu : ∀ j, g • u j ∈ W) (c d : Matrix (Fin r) (Fin r) (ZMod g)) (hcd : c * d = 1) (a : Fin r → ℤ) :
    ∃ e : Fin r → ℤ, ∑ j, a j • u j - ∑ m, e m • ∑ j, (c j m).val • u j ∈ W := by
  refine ⟨fun m => ∑ l, ((d m l).val : ℤ) * a l, ?_⟩
  have e1 : ∑ m, (∑ l, ((d m l).val : ℤ) * a l) • ∑ j, (c j m).val • u j =
      ∑ j, (∑ m, (∑ l, ((d m l).val : ℤ) * a l) * ((c j m).val : ℤ)) • u j := by
    simp only [Finset.smul_sum, ← natCast_zsmul, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [e1]
  refine cong_zsmul W u hu _ _ fun j => ?_
  have e2 := congrFun (congrFun hcd j) j
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id]
  have e3 : ∑ m, (∑ l, d m l * (a l : ZMod g)) * c j m = ∑ l, (c * d) j l * (a l : ZMod g) := by
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e3, hcd]
  simp [Matrix.one_apply]

variable {D : D7}

theorem incl_sum_nsmul (X : HidaSetting D) {r : ℕ} (a : Fin r → ℕ) (x : Fin r → Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (∑ j, a j • x j) = ∑ j, a j • incl X.B.I (x j) := by
  funext t
  simp [incl, map_sum, map_nsmul, Finset.sum_apply]

theorem incl_nsmul (X : HidaSetting D) (a : ℕ) (x : Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (a • x) = a • incl X.B.I x := by
  funext t
  simp [incl, map_nsmul]

theorem nsmul_mem_wLat (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (g : ℕ)
    (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) {y : Fin X.B.I.n → X.B.I.E} (hy : y ∈ X.B.I.L) :
    g • y ∈ wLat X w := by
  apply Submodule.subset_span
  refine ⟨(g : 𝓞 X.B.I.E), ⟨(g : 𝓞 D.host.E), hg, by simp⟩, y, hy, by ext t; simp⟩

theorem incl_mem_wLf (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {y : Fin X.B.I.n → X.B.I.E}
    (hy : y ∈ wLat X w) : incl X.B.I y ∈ wLf X w :=
  Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩

theorem fixRed_conj : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E) (c : G0g D.nd), (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → FixRed X red b → ∃ b' : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E, FixRed X (fun k => c⁻¹ * red k * c) b' := by
  intro D X red b c hg hf
  classical
  refine ⟨fun kv i => ∑ j, (((c kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
    Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val • b kv j, fun kv => ?_⟩
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  obtain ⟨⟨hbL, hbspan⟩, hrel⟩ := hf kv
  have hcd : ((c kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) *
      (((c kv)⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) = 1 :=
    Units.mul_inv (c kv)
  have hgL : ∀ j, D.host.g kv.1 • b kv j ∈ (wLat X (D.naut.plGw kv.1 kv.2)).toAddSubgroup :=
    fun j => nsmul_mem_wLat X _ _ (hg kv) (hbL j)
  refine ⟨⟨fun i => ?_, fun y hy => ?_⟩, fun k hk i => ?_⟩
  · exact Submodule.sum_mem _ fun j _ => nsmul_mem (hbL j) _
  · obtain ⟨a, ha⟩ := hbspan y hy
    obtain ⟨e, he⟩ := rebase_span _ (b kv) hgL _ _ hcd a
    refine ⟨e, ?_⟩
    have h2 := Submodule.add_mem _ ha he
    simp only [Int.cast_smul_eq_zsmul] at h2 ⊢
    rwa [sub_add_sub_cancel] at h2
  · have hu : ∀ j, D.host.g kv.1 • incl X.B.I (b kv j) ∈ (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup := fun j => by
      rw [← incl_nsmul]; exact incl_mem_wLf X _ (hgL j)
    have hM : ∀ i, (Matrix.mulVecLin (X.B.I.fmat k)).toAddMonoidHom (incl X.B.I (b kv i)) -
        ∑ j, (((red k kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val • incl X.B.I (b kv j) ∈
        (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup := fun i => by
      have := hrel k hk i
      simp only [Nat.cast_smul_eq_nsmul] at this
      exact this
    have key := rebase_rel _ _ _ hu _ _ _ hcd hM i
    simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply] at key
    simp only [incl_sum_nsmul, Nat.cast_smul_eq_nsmul, Pi.mul_apply, Pi.inv_apply, Units.val_mul]
    exact key

end GlobalTheory.Mem.SRe

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFixedBasisReductionMap_conj : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E) (c : G0g D.nd), (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → FixRed X red b → ∃ b' : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E, FixRed X (fun k => c⁻¹ * red k * c) b' := by
  atlas_forward_decl GlobalTheory.Mem.SRe.fixRed_conj
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem mem_baseLevel_iff_finiteGroup_lift (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {g0 : G0 R.Pg D.R.r} {κ : GA D (Yc D 0)}
    (hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) :
    κ ∈ levS (Yc D 0) (R.βY 0) (R.dat0 P) ↔ g0 ∈ P.H := by
  have e : rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = g0 := hl.2.2
  show κ ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) κ ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P) ∧
    rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) ∈ P.H) ↔ _
  rw [e]
  exact ⟨fun hk => hk.2.2, fun hg => ⟨hl.1, hl.2.1, hg⟩⟩

theorem baseLevelCharacter_eq_blockCharacter_lift (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {g0 : G0 R.Pg D.R.r} {κ : GA D (Yc D 0)}
    (hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) (hg : g0 ∈ P.H) :
    levChi (Yc D 0) (R.βY 0) (R.dat0 P) κ = ((P.chi ⟨g0, hg⟩ : ℂˣ) : ℂ) := by
  have e : rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = g0 := hl.2.2
  have e2 : levFn (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = ext1 P.H P.chi (rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ)) := by
    show ext1 P.H P.chi _ * (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ = _
    simp
  unfold levChi
  rw [e2, e, extendOne_of_mem _ hg]

end GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levChi_flag_triv (R : RealDat D A Ks) (κ : GA D (Yc D 0)) :
    levChi (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) κ = 1 := by
  unfold levChi
  show ((ext1 (⊤ : Subgroup (G0 R.Pg D.R.r)) (⇑(1 : (⊤ : Subgroup (G0 R.Pg D.R.r)) →* ℂˣ)) _ *
    (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ : ℂˣ) : ℂ) = 1
  unfold ext1
  split_ifs <;> simp

theorem hasType_flag1 (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (F : GA D (Yc D 0) → ℂ)
    (hF : ∀ k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 P), ∀ g, F (g * k) = levChi (Yc D 0) (R.βY 0) (R.dat0 P) k * F g) :
    HasType (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) F := by
  intro κ hκ g
  have h1 : κ ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) κ ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv) ∧
      rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) κ) ∈ (⊥ : Subgroup (G0 R.Pg D.R.r))) := hκ
  have e : rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = 1 := Subgroup.mem_bot.1 h1.2.2
  have hJ : κ ∈ levS (Yc D 0) (R.βY 0) (R.dat0 P) := by
    show κ ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) κ ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P) ∧
      rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) ∈ P.H)
    rw [e]
    exact ⟨h1.1, h1.2.1, P.H.one_mem⟩
  have c1 : levChi (Yc D 0) (R.βY 0) (R.dat0 P) κ = 1 := by
    unfold levChi
    show ((ext1 P.H P.chi (rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ)) *
      (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ : ℂˣ) : ℂ) = 1
    rw [e]
    have h2 : ext1 P.H (⇑P.chi) (1 : G0 R.Pg D.R.r) = 1 := blockDiagonalExtendByOnePrimeField_one P.H P.chi
    erw [h2]
    simp
  have c2 : levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) κ = 1 := by
    unfold levChi
    show ((ext1 (⊥ : Subgroup (G0 R.Pg D.R.r)) (⇑(1 : (⊥ : Subgroup (G0 R.Pg D.R.r)) →* ℂˣ)) _ *
      (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ : ℂˣ) : ℂ) = 1
    unfold ext1
    split_ifs <;> simp
  rw [hF κ hJ g, c1, c2]

theorem mult_act_of_lift (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {g0 : G0 R.Pg D.R.r} {κ : GA D (Yc D 0)}
    (hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) :
    ∀ T ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 P)) (levChi (Yc D 0) (R.βY 0) (R.dat0 P)),
      ∀ (v : (MP R).Vec) (g : GA D (Yc D 0)),
        (T : MMap (MP R)) v (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 ((T : MMap (MP R)) v) g := by
  intro T hT
  induction hT using Submodule.span_induction with
  | mem T hT =>
    intro v g
    have hF := hasType_flag1 R P (T v) (fun k hk g' => hT.lev v k hk g')
    have := level_action_spec hF ⟨κ, hl⟩ κ hl g
    show T v (g * κ) = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (T v) g
    rw [this, levChi_flag_triv, inv_one, one_mul]
  | zero =>
    intro v g
    show (0 : GA D (Yc D 0) → ℂ) (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (0 : GA D (Yc D 0) → ℂ) g
    rw [map_zero]
    rfl
  | add T₁ T₂ _ _ h₁ h₂ =>
    intro v g
    show (T₁ v + T₂ v) (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (T₁ v + T₂ v) g
    rw [map_add, Pi.add_apply, Pi.add_apply, h₁ v g, h₂ v g]
  | smul a T _ hT =>
    intro v g
    show (a • T v) (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (a • T v) g
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, hT v g]

end GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe

theorem isRedHom_conj {D : D7} {X : HidaSetting D} {red : X.B.I.Gf → G0g D.nd}
    {b' : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E} (c : G0g D.nd) (hred : IsRedHom X red)
    (hf : FixRed X (fun k => c⁻¹ * red k * c) b') : IsRedHom X (fun k => c⁻¹ * red k * c) := by
  refine ⟨goodAt_of_fixRed hf, fun k hk k' hk' => ?_, fun γ => ?_, fun k hk => ?_⟩
  · simp only [hred.2.1 k hk k' hk', mul_assoc, mul_inv_cancel_left]
  · obtain ⟨k, hk, e⟩ := hred.2.2.1 (c * γ * c⁻¹)
    exact ⟨k, hk, by simp only [e]; group⟩
  · rw [← hred.2.2.2 k hk]
    show c⁻¹ * red k * c = 1 ↔ red k = 1
    constructor
    · intro e
      calc red k = c * (c⁻¹ * red k * c) * c⁻¹ := by group
        _ = 1 := by rw [e]; group
    · intro e; rw [e]; group

theorem seeAt_exists : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed D → ∃ t, SeeAt R F X h t := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F X h hι hL hlev hpin hE
  obtain ⟨eR, plg, iso, hpl, he, hdiv, heG⟩ := hpin
  obtain ⟨ψ0, hgen, -, π, hπ, hmem, hchi⟩ := hlev
  have hgw : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := by
    intro kv
    have := D.naut.plGw_over kv.1 kv.2
    simp [placesOver] at this
    exact this
  obtain ⟨t₀, ht₀, red, b, hred, hfix, hlift, hcover⟩ := GlobalTheory.Mem.SRe.TrPt.exists_trans D G' Pl0 T A Ks R X h eR plg iso hι hL hpl hdiv heG
  obtain ⟨c, hc⟩ := GlobalTheory.T.conj_level_conjCharacter_symmetricLevel D G' Pl0 T A Ks R X h eR plg iso hι hL hpl hdiv heG ψ0 hgen π hπ red b hred hfix hgw
  obtain ⟨b', hfix'⟩ := GlobalTheory.T.isFixedBasisReductionMap_conj D X red b c hgw hfix
  obtain ⟨kc, hkc, hkcv⟩ := hred.2.2.1 c
  have hK : ∀ x, x ∈ X.B.I.Kset ↔ x ∈ GlobalTheory.RowLev.Inhab.Ksub X.B.I := fun x => Iff.rfl
  have hmul := hred.2.1
  have red_one : red 1 = 1 := by
    have e := hmul 1 ((hK 1).2 (Subgroup.one_mem _)) 1 ((hK 1).2 (Subgroup.one_mem _))
    rw [mul_one] at e
    exact left_eq_mul.mp e
  have red_inv : ∀ x ∈ X.B.I.Kset, red x⁻¹ = (red x)⁻¹ := by
    intro x hx
    have hx' : x⁻¹ ∈ X.B.I.Kset := (hK _).2 (Subgroup.inv_mem _ ((hK x).1 hx))
    have e := hmul x⁻¹ hx' x hx
    rw [inv_mul_cancel, red_one] at e
    exact eq_inv_of_mul_eq_one_left e.symm
  have memK : ∀ k ∈ X.B.I.Kset, kc⁻¹ * k * kc ∈ X.B.I.Kset := fun k hk =>
    (hK _).2 (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ((hK _).1 hkc)) ((hK _).1 hk)) ((hK _).1 hkc))
  have red_conj : ∀ k ∈ X.B.I.Kset, red (kc⁻¹ * k * kc) = c⁻¹ * red k * c := by
    intro k hk
    have hkc' : kc⁻¹ ∈ X.B.I.Kset := (hK _).2 (Subgroup.inv_mem _ ((hK _).1 hkc))
    have h1 : kc⁻¹ * k ∈ X.B.I.Kset := (hK _).2 (Subgroup.mul_mem _ ((hK _).1 hkc') ((hK _).1 hk))
    rw [hmul _ h1 _ hkc, hmul _ hkc' _ hk, red_inv _ hkc, hkcv]
  obtain ⟨t, ht⟩ : ∃ t : GA D (D.sp.Y 0), t = (iotaX X h).symm (1, kc) * t₀ := ⟨_, rfl⟩
  have hkap : ∀ k, kap X h t k = kap X h t₀ (kc⁻¹ * k * kc) := by
    intro k
    have e : ((1 : X.B.I.Ginf), kc⁻¹ * k * kc) = ((1, kc) : X.B.I.GA)⁻¹ * (1, k) * (1, kc) := by
      ext <;> simp
    show (t⁻¹ * (iotaX X h).symm (1, k) * t : GA D (D.sp.Y 0)) =
      t₀⁻¹ * (iotaX X h).symm (1, kc⁻¹ * k * kc) * t₀
    rw [e, map_mul, map_mul, map_inv, ht]
    group
  set red' : X.B.I.Gf → G0g D.nd := fun k => c⁻¹ * red k * c with hred'def
  have hred' : IsRedHom X red' := isRedHom_conj c hred hfix'
  have hliftT : ∀ k ∈ X.B.I.Kset, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (eR.symm (red' k))) (kap X h t k) := by
    intro k hk
    rw [hkap, hred'def]
    simp only
    rw [← red_conj k hk]
    exact hlift _ (memK k hk)
  have key : ∀ k ∈ X.B.I.Kset, (kap X h t k ∈ JR R F ↔ k ∈ X.K2) ∧
      ∀ hJ : kap X h t k ∈ JR R F, chiR R F (kap X h t k) = star (X.chi2 k) := by
    intro k hk
    have hl := hliftT k hk
    have hiff := mem_baseLevel_iff_finiteGroup_lift R (R.levR F true) hl
    have hc1 := (hc k hk).1
    refine ⟨?_, fun hJ => ?_⟩
    · rw [show kap X h t k ∈ JR R F ↔ _ from hiff, hmem, hc1]
    · have hg : R.eG (eR.symm (red' k)) ∈ (R.levR F true).H := hiff.1 hJ
      have hg' : reord π (R.eG (eR.symm (red' k))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H := (hmem _).1 hg
      show levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) (kap X h t k) = _
      rw [baseLevelCharacter_eq_blockCharacter_lift R (R.levR F true) hl hg, hchi _ hg hg']
      exact (hc k hk).2 hg'
  have hio : ∀ k, iotaX X h ((iotaX X h).symm (1, k)) = (1, k) := fun k => (iotaX X h).apply_symm_apply _
  have hconjEq : ∀ k, (t⁻¹)⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹ = (iotaX X h).symm (1, k) := by
    intro k
    group
  have hK2K : ∀ k ∈ X.K2, k ∈ X.B.I.Kset := fun k hk => hk.1
  refine ⟨t, ⟨?_, ?_, eR.symm, red', ?_, ⟨hred', ?_⟩, ?_⟩⟩
  · have e : t = t₀ * (t₀⁻¹ * (iotaX X h).symm (1, kc) * t₀) := by rw [ht]; group
    rw [e]
    exact Subgroup.mul_mem _ ht₀ (hlift kc hkc).1
  · intro y
    have hJ' : ∀ k, (t⁻¹)⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹ ∈ iotaX X h ⁻¹' concreteLevelAdelicSubset X ↔ k ∈ X.K2 := by
      intro k
      rw [hconjEq, Set.mem_preimage, hio]
      exact ⟨fun hh => hh.2, fun hh => ⟨rfl, hh⟩⟩
    have hy : y ∈ JR R F ∨ (t⁻¹)⁻¹ * y * t⁻¹ ∈ iotaX X h ⁻¹' concreteLevelAdelicSubset X → ∃ k ∈ X.B.I.Kset, y = kap X h t k := by
      rintro (hy | hy)
      · have hyF : y ∈ levG (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) := ⟨hy.1, hy.2.1, Subgroup.mem_top _⟩
        obtain ⟨k', hk', e⟩ := hcover y hyF
        refine ⟨kc * k' * kc⁻¹, (hK _).2 (Subgroup.mul_mem _ (Subgroup.mul_mem _ ((hK _).1 hkc) ((hK _).1 hk'))
          (Subgroup.inv_mem _ ((hK _).1 hkc))), ?_⟩
        rw [hkap, e]
        congr 1
        group
      · have h2 : (iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).1 = 1 ∧ (iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).2 ∈ X.K2 := hy
        refine ⟨(iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).2, h2.2.1, ?_⟩
        have e : (iotaX X h).symm (1, (iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).2) = (t⁻¹)⁻¹ * y * t⁻¹ := by
          rw [← h2.1]
          exact (iotaX X h).symm_apply_apply _
        show y = (t⁻¹ * (iotaX X h).symm (1, _) * t : GA D (D.sp.Y 0))
        rw [e]
        group
    refine ⟨⟨fun h1 => ?_, fun h1 => ?_⟩, fun h1 => ?_⟩
    · obtain ⟨k, hk, rfl⟩ := hy (Or.inl h1)
      exact (hJ' k).2 ((key k hk).1.1 h1)
    · obtain ⟨k, hk, rfl⟩ := hy (Or.inr h1)
      exact (key k hk).1.2 ((hJ' k).1 h1)
    · obtain ⟨k, hk, rfl⟩ := hy (Or.inl h1)
      rw [(key k hk).2 h1]
      show adelicCharacterOfHidaSetting X (iotaX X h ((t⁻¹)⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹)) = _
      rw [hconjEq, hio]
      rfl
  · intro k hk
    have hkK := hK2K k hk
    have hJ := (key k hkK).1.2 hk
    exact ⟨hJ, (key k hkK).2 hJ⟩
  · intro k hk T hT v g
    exact mult_act_of_lift R (R.levR F true) (hliftT k hk) T hT v g
  · intro γ
    show star (D.ntypes.e0.coeff γ) = D.what₂.embLL ((idemOf A.X).coeff (eR.symm γ))
    rw [he, MulEquiv.apply_symm_apply, hE γ]

end GlobalTheory.Mem.SRe
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicPoint_carries_rowLevel : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed D → ∃ t, SeeAt R F X h t := by
  atlas_forward_decl GlobalTheory.Mem.SRe.seeAt_exists
end
