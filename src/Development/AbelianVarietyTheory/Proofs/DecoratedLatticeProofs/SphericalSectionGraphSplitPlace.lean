import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqMulOfSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormCmExtensionSplitPlaceEqZpow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubledUnitaryChartSplitPlace
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleCharacterFinitePlaceComponent_eq_mul_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') → ∀ x : (Fv F v ⊗[F] E)ˣ, ((charAt χ v x : Circle) : ℂ) = (locChar χ w (Units.map (toCompl h).toMonoidHom x) : ℂˣ) * (locChar χ w' (Units.map (toCompl h').toMonoidHom x) : ℂˣ) := by
  first | exact @GlobalTheory.LFun.charAt_eq_locChar_mul_locChar | exact GlobalTheory.LFun.charAt_eq_locChar_mul_locChar | (intros; apply GlobalTheory.LFun.charAt_eq_locChar_mul_locChar <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_cmExtension_splitPlace_eq_zpow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → ∀ x : (Fv F v ⊗[F] E)ˣ, (absEv F E v x : ℝ) = (qV E w : ℝ) ^ (-(ordL (toCompl h x.1) + ordL (toCompl h' x.1))) := by
  first | exact @GlobalTheory.Doubling.AbsSplit.absEv_split | exact GlobalTheory.Doubling.AbsSplit.absEv_split | (intros; apply GlobalTheory.Doubling.AbsSplit.absEv_split <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doubled_unitary_chart_split_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L], ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E), IsSplitChart σ J L h e → ∃ f : GLoc σ Q v ≃* GL (Fin (n + n)) (w.adicCompletion E), (∀ g, g ∈ KFin σ Q L v ↔ f g ∈ KGL w (n + n)) ∧ (∀ y y', f (ioH _ σ hQ (y, y')) = blkGL finSumFinEquiv (e y, e y')) ∧ (∀ g, g ∈ siegelH (Fv F v) σ Q ↔ KeepsDiag finSumFinEquiv (f g).1) ∧ ∀ p : siegelH (Fv F v) σ Q, toCompl h (aH _ σ Q p).1 = (leviMat finSumFinEquiv (f p).1).det ∧ ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → ordL (toCompl h' (aH _ σ Q p).1) = -ordL (quotMat finSumFinEquiv (f p).1).det := by
  first | exact @GlobalTheory.LFun.DblSplit.exists_dbl_chart | exact GlobalTheory.LFun.DblSplit.exists_dbl_chart | (intros; apply GlobalTheory.LFun.DblSplit.exists_dbl_chart <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

noncomputable section

namespace GlobalTheory.GraphShear

open Matrix

theorem mem_GLint_of_entries {L : Type} [Field L] {ι : Type} [Fintype ι] [DecidableEq ι] {O : Subring L}
    {x : GL ι L} (h1 : ∀ i j, x.1 i j ∈ O) (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) : x ∈ Formalism.UG.GLint ι O := by
  unfold Formalism.UG.GLint Formalism.UG.bc
  have hinj : Function.Injective (O.subtype.mapMatrix : Matrix ι ι O →+* Matrix ι ι L) := fun A B h => by
    ext i j
    exact congrFun (congrFun h i) j
  have hA : O.subtype.mapMatrix (Matrix.of fun i j => (⟨x.1 i j, h1 i j⟩ : O)) = x.1 := by
    ext i j
    rfl
  have hB : O.subtype.mapMatrix (Matrix.of fun i j => (⟨(x⁻¹).1 i j, h2 i j⟩ : O)) = (x⁻¹).1 := by
    ext i j
    rfl
  refine ⟨⟨Matrix.of fun i j => (⟨x.1 i j, h1 i j⟩ : O), Matrix.of fun i j => (⟨(x⁻¹).1 i j, h2 i j⟩ : O), ?_, ?_⟩, ?_⟩
  · apply hinj
    rw [map_mul, map_one, hA, hB]
    exact Units.mul_inv x
  · apply hinj
    rw [map_mul, map_one, hA, hB]
    exact Units.inv_mul x
  · exact Units.ext hA

theorem exists_kappa {L : Type} [Field L] {O : Subring L} {n : ℕ} {ϖ : L} (h0 : ϖ ≠ 0) (hϖO : ϖ ∈ O)
    (d : Fin n → ℤ) (t k₁ k₂ : GL (Fin n) L) (ht : t.1 = Matrix.diagonal (fun i => ϖ ^ d i))
    (hk₁ : k₁ ∈ Formalism.UG.GLint (Fin n) O) (hk₂ : k₂ ∈ Formalism.UG.GLint (Fin n) O) :
    ∃ κ ∈ Formalism.UG.GLint (Fin (n + n)) O,
      KeepsDiag finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1 ∧
      leviMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1 =
        k₁.1 * Matrix.diagonal (fun i => ϖ ^ max (d i) 0) ∧
      quotMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1 =
        k₁.1 * Matrix.diagonal (fun i => ϖ ^ min (d i) 0) := by
  have hsc : ∀ a : ℤ, (ϖ ^ (-a).toNat - 1) * (ϖ ^ a.toNat - 1) = 0 ∧
      ϖ ^ a.toNat - 1 + 1 = ϖ ^ max a 0 ∧
      ϖ ^ a * (1 + (ϖ ^ (-a).toNat - 1)) = ϖ ^ max a 0 ∧
      ϖ ^ a - (ϖ ^ a.toNat - 1) = ϖ ^ min a 0 := by
    intro a
    rcases le_total 0 a with h | h
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
      have e1 : (-(m : ℤ)).toNat = 0 := by omega
      have e2 : (m : ℤ).toNat = m := by omega
      have e3 : max (m : ℤ) 0 = m := by omega
      have e4 : min (m : ℤ) 0 = 0 := by omega
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [e1, e2, e3, e4, pow_zero, sub_self, zero_mul, zpow_natCast, zpow_zero,
        sub_add_cancel, add_zero, mul_one] <;> ring
    · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat h
      have e1 : (-(-(m : ℤ))).toNat = m := by omega
      have e2 : (-(m : ℤ)).toNat = 0 := by omega
      have e3 : max (-(m : ℤ)) 0 = 0 := by omega
      have e4 : min (-(m : ℤ)) 0 = -(m : ℤ) := by omega
      have hm : ϖ ^ m ≠ 0 := pow_ne_zero m h0
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [e1, e2, e3, e4, hm, h0]
  have hmem : ∀ (M : Matrix (Fin n) (Fin n) L) (f : Fin n → L), (∀ i, f i ∈ O) → M = Matrix.diagonal f →
      ∀ i j, M i j ∈ O := by
    intro M f hf hM i j
    rw [hM, Matrix.diagonal_apply]
    split_ifs
    · exact hf i
    · exact O.zero_mem
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) L) i j ∈ O :=
    hmem 1 (fun _ => 1) (fun _ => O.one_mem) Matrix.diagonal_one.symm
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) L, B = Matrix.diagonal fun i => ϖ ^ (-d i).toNat - 1 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin n) (Fin n) L, C = Matrix.diagonal fun i => ϖ ^ (d i).toNat - 1 := ⟨_, rfl⟩
  have hBO : ∀ i j, B i j ∈ O := hmem B _ (fun _ => O.sub_mem (O.pow_mem hϖO _) O.one_mem) hB
  have hCO : ∀ i j, C i j ∈ O := hmem C _ (fun _ => O.sub_mem (O.pow_mem hϖO _) O.one_mem) hC
  have hBC : B * C = 0 := by
    rw [hB, hC, Matrix.diagonal_mul_diagonal]
    simp only [(hsc _).1, Matrix.diagonal_zero]
  have hCB : C * B = 0 := by
    rw [hB, hC, Matrix.diagonal_mul_diagonal]
    simp only [mul_comm (ϖ ^ (d _).toNat - 1), (hsc _).1, Matrix.diagonal_zero]
  have hC1 : C + 1 = Matrix.diagonal (fun i => ϖ ^ max (d i) 0) := by
    rw [hC, ← Matrix.diagonal_one, Matrix.diagonal_add]
    congr 1
    funext i
    exact (hsc (d i)).2.1
  have hTB : t.1 * (1 + B) = Matrix.diagonal (fun i => ϖ ^ max (d i) 0) := by
    rw [ht, hB, ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact (hsc (d i)).2.2.1
  have hTC : t.1 - C = Matrix.diagonal (fun i => ϖ ^ min (d i) 0) := by
    rw [ht, hC, Matrix.diagonal_sub]
    congr 1
    funext i
    exact (hsc (d i)).2.2.2
  generalize (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)) = e
  have hfb : ∀ (P Q R S : Matrix (Fin n) (Fin n) L), (∀ i j, P i j ∈ O) → (∀ i j, Q i j ∈ O) →
      (∀ i j, R i j ∈ O) → (∀ i j, S i j ∈ O) → ∀ a b, Matrix.fromBlocks P Q R S a b ∈ O := by
    intro P Q R S hP hQ hR hS a b
    rcases a with a | a <;> rcases b with b | b
    · exact hP a b
    · exact hQ a b
    · exact hR a b
    · exact hS a b
  have hUU : Matrix.fromBlocks 1 B C 1 * Matrix.fromBlocks 1 (-B) (-C) 1 = 1 := by
    rw [Matrix.fromBlocks_multiply]
    simp [hBC, hCB, Matrix.fromBlocks_one]
  have hUU' : Matrix.fromBlocks 1 (-B) (-C) 1 * Matrix.fromBlocks 1 B C 1 = 1 := by
    rw [Matrix.fromBlocks_multiply]
    simp [hBC, hCB, Matrix.fromBlocks_one]
  let U : GL (Fin (n + n)) L :=
    ⟨(Matrix.fromBlocks 1 B C 1).submatrix e.symm e.symm, (Matrix.fromBlocks 1 (-B) (-C) 1).submatrix e.symm e.symm,
      by rw [Matrix.submatrix_mul_equiv, hUU, Matrix.submatrix_one_equiv],
      by rw [Matrix.submatrix_mul_equiv, hUU', Matrix.submatrix_one_equiv]⟩
  have hU : U ∈ Formalism.UG.GLint (Fin (n + n)) O := by
    apply mem_GLint_of_entries
    · intro i j
      exact hfb 1 B C 1 hone hBO hCO hone (e.symm i) (e.symm j)
    · intro i j
      exact hfb 1 (-B) (-C) 1 hone (fun a b => O.neg_mem (hBO a b)) (fun a b => O.neg_mem (hCO a b)) hone
        (e.symm i) (e.symm j)
  have hblk : ∀ x y : GL (Fin n) L, x ∈ Formalism.UG.GLint (Fin n) O → y ∈ Formalism.UG.GLint (Fin n) O →
      blkGL e (x, y) ∈ Formalism.UG.GLint (Fin (n + n)) O := by
    intro x y hx hy
    unfold Formalism.UG.GLint at hx hy ⊢
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨blkGL e (x', y'), bc_blkGL e O.subtype x' y'⟩
  refine ⟨blkGL e (k₂⁻¹, k₁) * U, Subgroup.mul_mem _ (hblk _ _ (Subgroup.inv_mem _ hk₂) hk₁) hU, ?_⟩
  have hprod : blkGL e (k₁ * t * k₂, 1) * (blkGL e (k₂⁻¹, k₁) * U) = blkGL e (k₁ * t, k₁) * U := by
    rw [← mul_assoc, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel_right, one_mul]
  rw [hprod]
  have hsub : ((blkGL e (k₁ * t, k₁) * U : GL (Fin (n + n)) L) : Matrix (Fin (n + n)) (Fin (n + n)) L).submatrix e e =
      Matrix.fromBlocks (k₁.1 * t.1) (k₁.1 * t.1 * B) (k₁.1 * C) k₁.1 := by
    rw [Units.val_mul, val_blkGL]
    show ((Matrix.fromBlocks _ 0 0 _).submatrix e.symm e.symm *
      (Matrix.fromBlocks 1 B C 1).submatrix e.symm e.symm).submatrix e e = _
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id,
      Matrix.fromBlocks_multiply]
    simp [Units.val_mul]
  refine ⟨?_, ?_, ?_⟩
  · unfold KeepsDiag leviMat
    rw [hsub]
    simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
      Matrix.toBlocks_fromBlocks₂₂]
    have h1 : C + 1 = t.1 * (1 + B) := by rw [hC1, hTB]
    calc k₁.1 * C + k₁.1 = k₁.1 * (C + 1) := by rw [mul_add, mul_one]
      _ = k₁.1 * (t.1 * (1 + B)) := by rw [h1]
      _ = k₁.1 * t.1 + k₁.1 * t.1 * B := by rw [mul_add, mul_one, mul_add, mul_assoc]
  · unfold leviMat
    rw [hsub]
    simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂]
    rw [← hTB, mul_add, mul_one, mul_add, mul_assoc]
  · unfold quotMat
    rw [hsub]
    simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₁]
    rw [← hTC, mul_sub]

theorem ordL_det_mul_diagonal {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {O : Subring L}
    (hO : ∀ x ∈ O, Valued.v x ≤ (1 : WithZero (Multiplicative ℤ))) {n : ℕ} {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {k : GL (Fin n) L} (hk : k ∈ Formalism.UG.GLint (Fin n) O) (f : Fin n → ℤ) :
    ordL (k.1 * Matrix.diagonal fun i => ϖ ^ f i).det = ∑ i, f i := by
  have hdet : Valued.v k.1.det = 1 := by
    have hk' := hk
    unfold Formalism.UG.GLint at hk'
    obtain ⟨y, hy⟩ := hk'
    have hkmat : k.1 = O.subtype.mapMatrix y.1 := by
      rw [← hy]
      rfl
    have hinv : (k⁻¹).1 = O.subtype.mapMatrix (y⁻¹).1 := by
      rw [← hy, ← map_inv]
      rfl
    have hm1 : k.1.det ∈ O := by
      rw [hkmat, ← RingHom.map_det]
      exact (y.1.det).2
    have hm2 : (k⁻¹).1.det ∈ O := by
      rw [hinv, ← RingHom.map_det]
      exact ((y⁻¹).1.det).2
    have hmul : k.1.det * (k⁻¹).1.det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    have hv : Valued.v k.1.det * Valued.v (k⁻¹).1.det = 1 := by
      rw [← map_mul, hmul, map_one]
    refine le_antisymm (hO _ hm1) ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v k.1.det * Valued.v (k⁻¹).1.det := hv.symm
      _ ≤ Valued.v k.1.det * 1 := mul_le_mul' le_rfl (hO _ hm2)
      _ = Valued.v k.1.det := mul_one _
  have hpow : ∀ i, Valued.v (ϖ ^ f i) =
      ((Multiplicative.ofAdd (-(f i)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro i
    rw [map_zpow₀, hϖ, ← WithZero.coe_zpow]
    congr 1
    rw [← ofAdd_zsmul]
    congr 1
    simp
  have hD : Valued.v (Matrix.diagonal fun i => ϖ ^ f i).det =
      ((Multiplicative.ofAdd (-(∑ i, f i)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [Matrix.det_diagonal, map_prod, Finset.prod_congr rfl (fun i _ => hpow i), ← Finset.sum_neg_distrib, ofAdd_sum]
    exact (map_prod (WithZero.coeMonoidHom : Multiplicative ℤ →* WithZero (Multiplicative ℤ)) _ _).symm
  have hord : ∀ (z : L) (s : ℤ),
      Valued.v z = ((Multiplicative.ofAdd (-s) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → ordL z = s := by
    intro z s hz
    unfold Formalism.UG.ordL
    split_ifs with h
    · rw [hz] at h
      exact absurd h WithZero.coe_ne_zero
    · have h2 : WithZero.unzero h = Multiplicative.ofAdd (-s) :=
        WithZero.coe_injective (by rw [WithZero.coe_unzero, hz])
      rw [h2, toAdd_ofAdd, neg_neg]
  rw [Matrix.det_mul]
  exact hord _ _ (by rw [map_mul, hdet, one_mul, hD])

theorem graph_shear : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (d : Fin n → ℤ) (t k₁ k₂ : GL (Fin n) (w.adicCompletion E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → k₁ ∈ KGL w n → k₂ ∈ KGL w n → ∃ κ ∈ KGL w (n + n), KeepsDiag finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1 ∧ ordL (leviMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1).det = ∑ i, max (d i) 0 ∧ ordL (quotMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1).det = ∑ i, min (d i) 0 := by
  intro E _ _ w n ϖ hϖ d t k₁ k₂ ht hk₁ hk₂
  have hK : ∀ m, GlobalTheory.LFun.KGL w m = Formalism.UG.GLint (Fin m) (w.adicCompletionIntegers E).toSubring := fun m => rfl
  have hϖ' : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := hϖ
  have hO : ∀ x ∈ (w.adicCompletionIntegers E).toSubring, Valued.v x ≤ (1 : WithZero (Multiplicative ℤ)) :=
    fun x hx => hx
  have hϖO : ϖ ∈ (w.adicCompletionIntegers E).toSubring := by
    show Valued.v ϖ ≤ 1
    rw [hϖ']
    exact le_of_lt (by decide)
  have h0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ'
    exact WithZero.zero_ne_coe hϖ'
  rw [hK] at hk₁ hk₂
  obtain ⟨κ, hκ, h1, h2, h3⟩ := exists_kappa h0 hϖO d t k₁ k₂ ht hk₁ hk₂
  refine ⟨κ, (hK _).symm ▸ hκ, h1, ?_, ?_⟩
  · rw [h2]
    exact ordL_det_mul_diagonal hO hϖ' hk₁ _
  · rw [h3]
    exact ordL_det_mul_diagonal hO hϖ' hk₁ _

end GlobalTheory.GraphShear

end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_keepsDoublingDiagonal_adicCompletion : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (d : Fin n → ℤ) (t k₁ k₂ : GL (Fin n) (w.adicCompletion E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → k₁ ∈ KGL w n → k₂ ∈ KGL w n → ∃ κ ∈ KGL w (n + n), KeepsDiag finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1 ∧ ordL (leviMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1).det = ∑ i, max (d i) 0 ∧ ordL (quotMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1).det = ∑ i, min (d i) 0 := by
  first | exact @GlobalTheory.GraphShear.graph_shear | exact GlobalTheory.GraphShear.graph_shear | (intros; apply GlobalTheory.GraphShear.graph_shear <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.Core.Rk.KerSplit

section General

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LFun
open Formalism.UG (ordL)
open Formalism.L2.Host (atFin unif unif_spec IsUnifAt IsUnitAt)

theorem locChar_eq_val_zpow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ : (AF F ⊗[F] E)ˣ →* Circle} {w : HeightOneSpectrum (𝓞 E)} (h : UnrAt χ w) (y : (w.adicCompletion E)ˣ) :
    locChar χ w y = val χ w ^ ordL y.1 := by
  have hy : Valued.v y.1 ≠ 0 := by simp
  have h0 : Valued.v y.1 = WithZero.exp (-ordL y.1) := by
    rw [ordL, dif_neg hy, neg_neg]
    exact (WithZero.coe_unzero hy).symm
  have h1 : IsUnitAt w (y * (atFin w (unif w)) ^ (-ordL y.1)) := by
    have := unif_spec w
    unfold IsUnifAt at this
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, this, ← WithZero.exp_zsmul]
    nth_rewrite 1 [h0]
    rw [← WithZero.exp_add]
    simp
  have := h _ h1
  rwa [map_mul, map_zpow, zpow_neg, mul_inv_eq_one] at this

theorem npow_zpow_neg {r : ℝ≥0} {q : ℕ} {m : ℤ} (h : (r : ℝ) = (q : ℝ) ^ (-m)) (z : ℂ) :
    GlobalTheory.Doubling.npow r z = (q : ℂ) ^ (-z * (m : ℂ)) := by
  rw [GlobalTheory.Doubling.npow, h, Complex.ofReal_zpow, Complex.ofReal_natCast, ← Complex.cpow_intCast,
    ← Complex.cpow_mul]
  · congr 1; push_cast; ring
  · rw [← Complex.natCast_log, Complex.mul_im, Complex.ofReal_im, Complex.intCast_im]; simp [Real.pi_pos]
  · rw [← Complex.natCast_log, Complex.mul_im, Complex.ofReal_im, Complex.intCast_im]; simp [Real.pi_pos.le]

open GlobalTheory.AdelicU GlobalTheory.Doubling Formalism.UG in
set_option maxHeartbeats 800000 in

theorem char_value {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hc : IsCMExt F E σ) {χ : (AF F ⊗[F] E)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 F)}
    {w w' : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (h' : w'.under (𝓞 F) = v) (hne : w ≠ w')
    (hall : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') (hU : UnrAt χ w) (hU' : UnrAt χ w')
    (hm : val χ w * val χ w' = 1) {n : ℕ} (d : Fin n → ℤ) (x : (Fv F v ⊗[F] E)ˣ)
    (o1 : ordL (toCompl h x.1) = ∑ i, max (d i) 0) (o2 : ordL (toCompl h' x.1) = -∑ i, min (d i) 0) (z : ℂ) :
    ((charAt χ⁻¹ v x : Circle) : ℂ) * GlobalTheory.Doubling.npow (absEv F E v x) z =
      (((val χ w)⁻¹ : ℂˣ) : ℂ) ^ (∑ i, d i) * (qV E w : ℂ) ^ (-z * ((∑ i, |d i| : ℤ) : ℂ)) := by
  have habs := GlobalTheory.T.norm_cmExtension_splitPlace_eq_zpow _ _ _ hc v w h w' h' hne x
  have hch := GlobalTheory.T.ideleCharacterFinitePlaceComponent_eq_mul_of_split _ _ χ⁻¹ v w h w' h' hne hall x
  have s1 : ∑ i, max (d i) 0 + -∑ i, min (d i) 0 = ∑ i, |d i| := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [abs_eq_max_neg]; omega
  have s2 : ∑ i, max (d i) 0 + ∑ i, min (d i) 0 = ∑ i, d i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by omega
  rw [o1, o2, s1] at habs
  rw [locChar_eq_val_zpow hU.inv, locChar_eq_val_zpow hU'.inv, val_inv, val_inv, ← Units.val_mul] at hch
  change _ = (((val χ w)⁻¹ ^ ordL (toCompl h x.1) * (val χ w')⁻¹ ^ ordL (toCompl h' x.1) : ℂˣ) : ℂ) at hch
  rw [o1, o2, eq_inv_of_mul_eq_one_right hm, inv_inv, zpow_neg (val χ w), ← inv_zpow, ← zpow_add, s2,
    Units.val_zpow_eq_zpow_val] at hch
  rw [hch, npow_zpow_neg habs]

end General

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open GlobalTheory.LFun (locChar IsSplitChart IsInertChart KGL UnrAt)

set_option maxHeartbeats 1600000 in

theorem sphSec_split : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (χ : (AE D)ˣ →* Circle) (b : ℕ), ResEta D χ b → ∀ v : FinPl D, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → UnrAt χ w) → ∀ (s : ℂ) (φ : Gv (dblSp A) v → ℂ), IsSphSecAt A L v χ⁻¹ s φ → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (e : Gv A v ≃* GL (Fin A.rank) (w.adicCompletion D.host.E)), IsSplitChart D.sp.cm.sig A.gram L h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin A.rank → ℤ) (t : GL (Fin A.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w A.rank, ∀ k₂ ∈ KGL w A.rank, φ (ioAt A v (e.symm (k₁ * t * k₂))) = (((GlobalTheory.LFun.val χ w)⁻¹ : ℂˣ) : ℂ) ^ (∑ i, d i) * (qV D.host.E w : ℂ) ^ (-((A.rank : ℂ) / 2 + s) * ((∑ i, |d i| : ℤ) : ℂ)) := by
  intro D A L hL χ b hχ v hv hU s φ hφ w h e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  haveI := hL.1
  have hc := isCMExt_host D
  obtain ⟨w', hne, hall, -⟩ := GlobalTheory.LFun.SplitChart.exists_conj_place hc h hv
  have h' : w'.under (𝓞 D.host.F) = v := (hall w').2 (Or.inr rfl)
  have hm : GlobalTheory.LFun.val χ w * GlobalTheory.LFun.val χ w' = 1 :=
    GlobalTheory.LFun.ResEta.val_mul_val hc.2.2.1 ((GlobalTheory.LFun.resEta_iff χ _).1 hχ) hne h h' (hU w h) (hU w' h')
  obtain ⟨f, hfK, hfi, hfP, hfa⟩ := GlobalTheory.T.exists_doubled_unitary_chart_split_place _ _ _ hc A.rank A.gram (GlobalTheory.Doubling.isHermND_gram A) (dblSp A).gram
    (gram_hdbl A) L v w h hv (IwSplit.isSelfDualAt_of_isSelfDualC hL v) e he
  obtain ⟨κ, hκ, hP, hl, hq⟩ := GlobalTheory.T.exists_integral_keepsDoublingDiagonal_adicCompletion _ w A.rank ϖ hϖ d t k₁ k₂ ht hk₁ hk₂
  have hp : f (ioAt A v (e.symm (k₁ * t * k₂)) * f.symm κ) = blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ := by
    rw [map_mul, f.apply_symm_apply, ioAt, hfi, e.apply_symm_apply, map_one]
  rw [← hp] at hP hl hq
  rw [← hφ.2.1 (f.symm κ) ((hfK _).2 (by rwa [f.apply_symm_apply]))]
  generalize ioAt A v (e.symm (k₁ * t * k₂)) * f.symm κ = g at hP hl hq ⊢
  obtain ⟨ha, ha'⟩ := hfa ⟨g, (hfP g).2 hP⟩
  have ha' := ha' w' h' hne
  have law := (mem_degPSH.1 hφ.1).1 ⟨g, (hfP g).2 hP⟩ 1
  generalize aH _ D.sp.cm.sig (dblSp A).gram ⟨g, (hfP g).2 hP⟩ = x at ha ha' law
  have o1 : Formalism.UG.ordL (GlobalTheory.LFun.toCompl h x.1) = ∑ i, max (d i) 0 := by rw [ha]; exact hl
  have o2 : Formalism.UG.ordL (GlobalTheory.LFun.toCompl h' x.1) = -∑ i, min (d i) 0 := by rw [ha']; exact congrArg _ hq
  rw [mul_one, hφ.2.2, mul_one] at law
  refine law.trans ?_
  rw [add_comm ((A.rank : ℂ) / 2) s]
  exact char_value hc h h' hne hall (hU w h) (hU w' h') hm d x o1 o2 _

end GlobalTheory.Core.Rk.KerSplit
end
end
