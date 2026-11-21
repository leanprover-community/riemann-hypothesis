import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormIntegralMatrix
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.CompletionExists
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.DualPairingExists
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SpanEquality
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.HeisenbergMatrixFacts
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.PointwiseOfSpanHeisenberg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUpLatEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceZeroIntegersModUniformizerCardOfCardSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIntegersModUniformizerEqQSq
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SmallCornerOfHeisenbergDual
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.CountOfHeisenbergIndex
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.CosetSurjectiveOfLevi
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.RecursionIdentity

section
section
noncomputable section

open Matrix Formalism.UG GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertSmith

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem exists_zpow_val {ϖ y : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (hy : y ≠ 0) :
    ∃ d : ℤ, Valued.v y = Valued.v (ϖ ^ d) := by
  refine ⟨Formalism.UG.ordL y, ?_⟩
  rw [GlobalTheory.Hk3.Smith.v_eq_ord hy, map_zpow₀, hϖ]
  change _ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ Formalism.UG.ordL y
  rw [← WithZero.coe_zpow, ← ofAdd_zsmul]
  congr 2
  simp

theorem isInt_diagonal {n : ℕ} {s : Fin n → L} (hs : ∀ i, Valued.v (s i) = 1) : IsInt (Matrix.diagonal s) := by
  intro i j
  rw [GlobalTheory.Hk3.Smith.mem_intL, Matrix.diagonal_apply]
  split_ifs with h
  · exact (hs i).le
  · simp

theorem smith : Smith := by
  intro L _ _ ϖ n hϖ g hg
  obtain ⟨P, Q, ⟨hPi, P', hP'i, hPP'⟩, ⟨hQi, Q', hQ'i, hQQ'⟩, hD⟩ := GlobalTheory.Hk3.Smith.exists_diag n n g
  have hP'P : P' * P = 1 := mul_eq_one_comm.mp hPP'
  have hdetP : P.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hPP'
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hdetQ : Q.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hQQ'
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hDdiag : P * g * Q = Matrix.diagonal (fun i => (P * g * Q) i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact hD i j (fun h => hij (Fin.ext h))
  have hne : ∀ i, (P * g * Q) i i ≠ 0 := by
    have hdet : (P * g * Q).det ≠ 0 := by
      rw [Matrix.det_mul, Matrix.det_mul]
      exact mul_ne_zero (mul_ne_zero hdetP hg) hdetQ
    rw [hDdiag, Matrix.det_diagonal] at hdet
    exact fun i => Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)
  have hvϖ : Valued.v ϖ ≠ 0 := by
    rw [hϖ]
    exact WithZero.coe_ne_zero
  have hϖ0 : ϖ ≠ 0 := fun h => hvϖ (by rw [h, map_zero])
  choose d hd using fun i => exists_zpow_val hϖ (hne i)
  have hpow0 : ∀ i, ϖ ^ d i ≠ 0 := fun i => zpow_ne_zero _ hϖ0
  obtain ⟨u, hu⟩ : ∃ u : Fin n → L, ∀ i, u i = (P * g * Q) i i / ϖ ^ d i := ⟨_, fun i => rfl⟩
  have hvu : ∀ i, Valued.v (u i) = 1 := by
    intro i
    rw [hu i, map_div₀, hd i, div_self]
    exact fun h => hpow0 i (by
      by_contra h'
      exact h' ((Valuation.zero_iff _).mp h))
  have hvu' : ∀ i, Valued.v ((u i)⁻¹) = 1 := fun i => by rw [map_inv₀, hvu i, inv_one]
  have hu0 : ∀ i, u i ≠ 0 := fun i h => by
    have h1 := hvu i
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  have hDfac : P * g * Q = Matrix.diagonal (fun i => ϖ ^ d i) * Matrix.diagonal u := by
    rw [Matrix.diagonal_mul_diagonal]
    conv_lhs => rw [hDdiag]
    congr 1
    funext i
    rw [hu i]
    field_simp
  have hinv : (fun i => u i * (u i)⁻¹) = fun _ => (1 : L) := funext fun i => mul_inv_cancel₀ (hu0 i)
  refine ⟨d, P', P, Matrix.diagonal u * Q', Q * Matrix.diagonal (fun i => (u i)⁻¹), hP'i, hPi,
    GlobalTheory.Hk3.Smith.mul_int (isInt_diagonal hvu) hQ'i, GlobalTheory.Hk3.Smith.mul_int hQi (isInt_diagonal hvu'),
    hPP', ?_, ?_⟩
  · calc Matrix.diagonal u * Q' * (Q * Matrix.diagonal fun i => (u i)⁻¹)
        = Matrix.diagonal u * (Q' * Q) * Matrix.diagonal (fun i => (u i)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [mul_eq_one_comm.mp hQQ', Matrix.mul_one, Matrix.diagonal_mul_diagonal, hinv,
            Matrix.diagonal_one]
  · calc g = P' * (P * g * Q) * Q' := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP'P, Matrix.one_mul, Matrix.mul_assoc, hQQ',
            Matrix.mul_one]
      _ = _ := by
          rw [hDfac]
          simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.InertSmith

end
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smith_normal_form_exists : Smith := by
  atlas_forward_decl GlobalTheory.CompanionTheory.InertSmith.smith
end

section
section
open Matrix

namespace GlobalTheory.CompanionTheory.InertZeta

open GlobalTheory.InertZeta

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem isInt_diagonal {f : Fin n → L} (hf : ∀ i, f i ∈ Formalism.UG.intL L) : IsInt (Matrix.diagonal f) := fun i j => by
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · exact hf i
  · exact zero_mem _

theorem hasLen_diagonal {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (d : Fin n → ℤ) :
    HasLen (Matrix.diagonal fun i => ϖ ^ d i) (∑ i, (-d i).toNat) := by
  have h0 : ϖ ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have h1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hpow : ∀ e : ℕ, ϖ ^ e ∈ Formalism.UG.intL L := fun e => by
    change Valued.v (ϖ ^ e) ≤ 1
    rw [map_pow]
    exact pow_le_one' h1 e
  have hnum : ∀ i, ϖ ^ d i * ϖ ^ (-d i).toNat = ϖ ^ (d i).toNat := fun i => by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0]
    congr 1
    omega
  refine ⟨Matrix.diagonal fun i => if 0 ≤ d i then 1 else 0, Matrix.diagonal fun i => if 0 ≤ d i then 0 else 1,
    Matrix.diagonal fun i => ϖ ^ (-d i).toNat, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · refine isInt_diagonal fun i => ?_
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · refine isInt_diagonal fun i => ?_
    split_ifs
    · exact zero_mem _
    · exact one_mem _
  · exact isInt_diagonal fun i => hpow _
  · rw [Matrix.diagonal_mul_diagonal]
    refine isInt_diagonal fun i => ?_
    rw [hnum]
    exact hpow _
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    by_cases h : 0 ≤ d i
    · have : (-d i).toNat = 0 := by omega
      simp [h, this]
    · have e : ϖ ^ d i * ϖ ^ (-d i).toNat = 1 := by
        rw [hnum, show (d i).toNat = 0 by omega, pow_zero]
      simp [h, e]
  · rw [Matrix.det_diagonal, map_prod]
    simp only [map_pow, hϖ]
    rw [Finset.prod_pow_eq_pow_sum, ← WithZero.exp_nsmul]
    congr 1
    simp

theorem fracExists_of_smith : Smith → FracExists := by
  intro hS L _ _ ϖ n hϖ g hg
  obtain ⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, rfl⟩ := hS L ϖ n hϖ g hg
  have h := (hasLen_diagonal hϖ d).mul_mul ha ha' hb hb' ea eb
  rw [h.len_eq]
  exact h

end GlobalTheory.CompanionTheory.InertZeta
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fraction_exists_of_smith : Smith → FracExists := by
  atlas_forward_decl GlobalTheory.CompanionTheory.InertZeta.fracExists_of_smith
end

section
section
open GlobalTheory.InertZeta Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.InertZeta

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem mem_intL_iff {x : L} : x ∈ Formalism.UG.intL L ↔ Valued.v x ≤ 1 := Iff.rfl

theorem det_updateRow_one (i : Fin n) (ρ : Fin n → L) :
    ((1 : Matrix (Fin n) (Fin n) L).updateRow i ρ).det = ρ i := by
  rw [← Matrix.det_transpose, ← Matrix.updateCol_transpose, Matrix.transpose_one, ← Matrix.cramer_apply,
    Matrix.cramer_one]
  rfl

theorem rowLat_updateRow {M : Matrix (Fin n) (Fin n) L} {ρ : Fin n → L} {i : Fin n}
    (h0 : ρ i ≠ 0) (h1 : Valued.v (ρ i)⁻¹ ≤ 1) (h2 : ∀ j, Valued.v (ρ j) ≤ Valued.v (ρ i)) :
    rowLat M ⊔ Submodule.span (Formalism.UG.intL L) {ρ ᵥ* M} = rowLat (M.updateRow i (ρ ᵥ* M)) := by
  set w := ρ ᵥ* M with hw
  apply le_antisymm
  · refine sup_le (rowLat_le.2 fun j => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
    · by_cases hj : j = i
      · subst hj
        refine mem_rowLat.2 ⟨fun l => if l = j then (ρ j)⁻¹ else -(ρ l * (ρ j)⁻¹), fun l => ?_, ?_⟩
        · by_cases hl : l = j
          · simp only [if_pos hl]
            exact h1
          · simp only [hl, if_false]
            refine neg_mem ?_
            rw [mem_intL_iff, map_mul, map_inv₀]
            exact mul_inv_le_one_of_le₀ (h2 l) zero_le'
        · rw [Matrix.vecMul_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
          have e1 : ∑ l ∈ Finset.univ.erase j, (if l = j then (ρ j)⁻¹ else -(ρ l * (ρ j)⁻¹)) • (M.updateRow j w) l
              = ∑ l ∈ Finset.univ.erase j, (-(ρ l * (ρ j)⁻¹)) • M l :=
            Finset.sum_congr rfl fun l hl => by
              have := Finset.ne_of_mem_erase hl
              simp [this, Matrix.updateRow_ne]
          have e2 : w = ρ j • M j + ∑ l ∈ Finset.univ.erase j, ρ l • M l := by
            rw [hw, Matrix.vecMul_eq_sum]
            exact (Finset.add_sum_erase _ (fun l => ρ l • M l) (Finset.mem_univ j)).symm
          rw [e1]
          simp only [if_true, Matrix.updateRow_self]
          rw [e2, smul_add, smul_smul, inv_mul_cancel₀ h0, one_smul, Finset.smul_sum, add_assoc,
            ← Finset.sum_add_distrib]
          simp only [smul_smul, neg_smul]
          have : ∀ l, (ρ j)⁻¹ * ρ l = ρ l * (ρ j)⁻¹ := fun l => mul_comm _ _
          simp [this]
      · have := row_mem_rowLat (M.updateRow i w) j
        rwa [Matrix.updateRow_ne hj] at this
    · have := row_mem_rowLat (M.updateRow i w) i
      rwa [Matrix.updateRow_self] at this
  · refine rowLat_le.2 fun j => ?_
    by_cases hj : j = i
    · subst hj
      rw [Matrix.updateRow_self]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · rw [Matrix.updateRow_ne hj]
      exact Submodule.mem_sup_left (row_mem_rowLat M j)

theorem addVec : AddVec := by
  intro L _ _ n M k ρ e hM hρ he
  by_cases e0 : e = 0
  · subst e0
    refine ⟨M, by simpa using hM, ?_⟩
    refine sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 (mem_rowLat.2 ⟨ρ, fun i => ?_, rfl⟩))
    exact mem_intL_iff.2 (by simpa using hρ i)
  · obtain ⟨i, hi⟩ := he.resolve_left e0
    have h0 : ρ i ≠ 0 := fun h => by
      rw [h, map_zero] at hi
      exact WithZero.exp_ne_zero hi.symm
    have hone : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (e : ℤ) := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    have h1 : Valued.v (ρ i)⁻¹ ≤ 1 := by
      rw [map_inv₀, hi]
      exact inv_le_one_of_one_le₀ hone
    refine ⟨M.updateRow i (ρ ᵥ* M), ?_, rowLat_updateRow h0 h1 fun j => hi ▸ hρ j⟩
    have e1 : M.updateRow i (ρ ᵥ* M) = (1 : Matrix (Fin n) (Fin n) L).updateRow i ρ * M := by
      ext a b
      by_cases ha : a = i
      · subst ha
        simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
      · simp [Matrix.updateRow_ne ha, Matrix.mul_apply, Matrix.one_apply]
    rw [e1, Matrix.det_mul, det_updateRow_one, map_mul, hi, hM, ← WithZero.exp_add, add_comm]

end GlobalTheory.CompanionTheory.InertZeta

end
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_vector_exists : AddVec := by
  atlas_forward_decl GlobalTheory.CompanionTheory.InertZeta.addVec
end

section
section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.BorelUMod.UpLatIndex

noncomputable section

namespace GlobalTheory.CompanionTheory.InertIndex

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

def boxLat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (c : Fin n → ℤ) :
    AddSubgroup (Fin n → L) :=
  AddSubgroup.pi Set.univ fun i => ordBall L (c i)

theorem mem_boxLat {c : Fin n → ℤ} {x : Fin n → L} : x ∈ boxLat L c ↔ ∀ i, x i ∈ ordBall L (c i) := by
  simp [boxLat, AddSubgroup.mem_pi]

theorem relIndex_boxLat (c C : Fin n → ℤ) :
    (boxLat L C).relIndex (boxLat L c) = ∏ i, (ordBall L (C i)).relIndex (ordBall L (c i)) := by
  let f : boxLat L c →+ (∀ i, ordBall L (c i) ⧸ (ordBall L (C i)).addSubgroupOf (ordBall L (c i))) :=
    { toFun := fun x i => QuotientAddGroup.mk ⟨x.1 i, mem_boxLat.1 x.2 i⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := fun y => by
    refine ⟨⟨fun i => ((y i).out : L), mem_boxLat.2 fun i => (y i).out.2⟩, funext fun i => ?_⟩
    exact (y i).out_eq
  have hc : (boxLat L C).addSubgroupOf (boxLat L c) = f.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, funext_iff, AddSubgroup.mem_addSubgroupOf, mem_boxLat]
    constructor
    · intro h i
      exact (QuotientAddGroup.eq_zero_iff _).2 (h i)
    · intro h i
      exact AddSubgroup.mem_addSubgroupOf.1
        ((QuotientAddGroup.eq_zero_iff (⟨x.1 i, mem_boxLat.1 x.2 i⟩ : ordBall L (c i))).1 (h i))
  rw [AddSubgroup.relIndex, hc, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
    AddSubgroup.card_top, Nat.card_pi]
  rfl

theorem mem_intL_iff {x : L} : x ∈ intL L ↔ Valued.v x ≤ 1 := Iff.rfl

theorem vecMul_mem_intV {M : Matrix (Fin n) (Fin n) L} (hM : IsInt M) {r : Fin n → L} (hr : r ∈ intV L n) :
    r ᵥ* M ∈ intV L n := by
  rw [mem_intV] at hr ⊢
  intro j
  change ∑ i, r i * M i j ∈ intL L
  exact Subring.sum_mem _ fun i _ => mul_mem (hr i) (hM i j)

theorem v_zpow {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (m : ℤ) :
    Valued.v (ϖ ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; simp

theorem mem_preLat_iff {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {d : Fin n → ℤ}
    {a b b' : Matrix (Fin n) (Fin n) L} (hb : IsInt b) (hb' : IsInt b') (eb : b * b' = 1) (r : Fin n → L) :
    r ∈ preLat (a * Matrix.diagonal (fun i => ϖ ^ d i) * b) ↔ r ᵥ* a ∈ boxLat L (fun i => -d i) := by
  have h0 : ϖ ≠ 0 := fun e => by
    rw [e, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have key : ∀ s : Fin n → L, s ᵥ* Matrix.diagonal (fun i => ϖ ^ d i) ∈ intV L n ↔
      s ∈ boxLat L (fun i => -d i) := fun s => by
    rw [mem_intV, mem_boxLat]
    refine forall_congr' fun i => ?_
    rw [Matrix.vecMul_diagonal, mem_intL_iff, mem_ordBall, map_mul, v_zpow hϖ, neg_neg]
    have e : WithZero.exp (d i) = 1 * (WithZero.exp (-d i))⁻¹ := by rw [WithZero.exp_neg, inv_inv, one_mul]
    rw [e, le_mul_inv_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero)]
  have hr : r ∈ preLat (a * Matrix.diagonal (fun i => ϖ ^ d i) * b) ↔
      r ᵥ* (a * Matrix.diagonal (fun i => ϖ ^ d i) * b) ∈ intV L n := by
    rw [mem_preLat, mem_intV]
  rw [hr, ← key, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
  refine ⟨fun h => ?_, fun h => vecMul_mem_intV hb h⟩
  have := vecMul_mem_intV hb' h
  rwa [Matrix.vecMul_vecMul, eb, Matrix.vecMul_one] at this

theorem latIndex (hS : Smith) : LatIndex := by
  intro L _ _ ϖ σ q n hU A k hA hk
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have hdet : A.det ≠ 0 := fun h => by
    rw [h, map_zero] at hk; exact WithZero.exp_ne_zero hk.symm
  obtain ⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, hAe⟩ := hS L ϖ n hϖ A hdet
  have ea' : a * a' = 1 := mul_eq_one_comm.1 ea
  have eb' : b' * b = 1 := mul_eq_one_comm.1 eb
  have hDe : Matrix.diagonal (fun i => ϖ ^ d i) = a' * A * b' := by
    rw [hAe]
    calc _ = (a' * a) * Matrix.diagonal (fun i => ϖ ^ d i) * (b * b') := by rw [ea, eb]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hD : IsInt (Matrix.diagonal (fun i => ϖ ^ d i)) := hDe ▸ (ha'.mul hA).mul hb'
  have hd : ∀ i, 0 ≤ d i := fun i => by
    have h := hD i i
    rw [Matrix.diagonal_apply_eq, mem_intL_iff, v_zpow hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    omega
  have hprod : ∀ s : Finset (Fin n), ∏ i ∈ s, WithZero.exp (-(d i)) =
      (WithZero.exp (-∑ i ∈ s, d i) : WithZero (Multiplicative ℤ)) := fun s => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, ← WithZero.exp_add, neg_add]
  have hsum : ∑ i, d i = k := by
    have h := hk
    rw [hAe, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, v_det_eq_one ha ha' ea', v_det_eq_one hb hb' eb,
      Matrix.det_diagonal, map_prod, one_mul, mul_one, Finset.prod_congr rfl fun i _ => v_zpow hϖ (d i), hprod,
      WithZero.exp_inj] at h
    omega
  let f : (Fin n → L) →+ (Fin n → L) := a.vecMulLinear.toAddMonoidHom
  have hfa : ∀ r, f r = r ᵥ* a := fun _ => rfl
  have hf : Function.Surjective f := fun s => ⟨s ᵥ* a', by
    rw [hfa, Matrix.vecMul_vecMul, ea, Matrix.vecMul_one]⟩
  have h1 : intV L n = (boxLat L fun _ => 0).comap f := by
    ext r
    have e : ∀ x : Fin n → L, x ∈ boxLat L (fun _ => 0) ↔ x ∈ intV L n := fun x => by
      rw [mem_boxLat, mem_intV]
      refine forall_congr' fun i => ?_
      rw [mem_ordBall, mem_intL_iff, neg_zero, WithZero.exp_zero]
    rw [AddSubgroup.mem_comap, e, hfa]
    refine ⟨fun h => vecMul_mem_intV ha h, fun h => ?_⟩
    have := vecMul_mem_intV ha' h
    rwa [Matrix.vecMul_vecMul, ea', Matrix.vecMul_one] at this
  have h2 : preLat A = (boxLat L fun i => -d i).comap f := by
    ext r
    rw [AddSubgroup.mem_comap, hfa, hAe]
    exact mem_preLat_iff hϖ hb hb' eb r
  rw [h1, h2, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hf, relIndex_boxLat,
    Finset.prod_congr rfl fun i _ => relIndex_ordBall hU (k := -d i) (K := 0) (by linarith [hd i]),
    Finset.prod_pow_eq_pow_sum, ← pow_mul]
  congr 2
  have : ((∑ i, (0 - -d i).toNat : ℕ) : ℤ) = k := by
    rw [Nat.cast_sum, ← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.toNat_of_nonneg (by linarith [hd i])]
    ring
  exact_mod_cast this

end GlobalTheory.CompanionTheory.InertIndex

end
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_index_of_smith : Smith → LatIndex := by
  atlas_forward_decl GlobalTheory.CompanionTheory.InertIndex.latIndex
end

section
section
open GlobalTheory.InertZeta Formalism.UG

namespace GlobalTheory.CompanionTheory.InertZeta

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem traceZero_eq_map {σ : L →+* L} {c : L} (hc : c ≠ 0) (hσ : σ c = c) :
    traceZero σ c =
      ((intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker).map (AddMonoidHom.mulLeft c⁻¹) := by
  ext x
  rw [mem_traceZero, AddSubgroup.mem_map]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨c * x, AddSubgroup.mem_inf.2 ⟨h1, ?_⟩, by simp [hc]⟩
    rw [AddMonoidHom.mem_ker]
    show σ (c * x) + c * x = 0
    rw [map_mul, hσ, ← mul_add, h2, mul_zero]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hy
    rw [AddMonoidHom.mem_ker] at h2
    have h2' : σ y + y = 0 := h2
    have hi : σ c⁻¹ = c⁻¹ := by rw [map_inv₀, hσ]
    refine ⟨?_, ?_⟩
    · show c * (c⁻¹ * y) ∈ intL L
      rw [mul_inv_cancel_left₀ hc]
      exact h1
    · show σ (c⁻¹ * y) + c⁻¹ * y = 0
      rw [map_mul, hi, ← mul_add, h2', mul_zero]

theorem traceIndex : TraceIndex := by
  intro L _ _ ϖ σ q f hU
  have hbase := GlobalTheory.SatakeWeyl.traceZeroIndex_of_intIndex GlobalTheory.SatakeWeyl.intIndex L ϖ σ q hU
  obtain ⟨-, -, hϖ, hv, -, -, -⟩ := hU
  have hv' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hv
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv'
    exact WithZero.exp_ne_zero hv'.symm
  have hϖ1 : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hv', ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  set T := (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker with hT
  have hS : ∀ f : ℕ, traceZero σ (ϖ ^ f) = T.map (AddMonoidHom.mulLeft (ϖ ^ f)⁻¹) := fun f =>
    traceZero_eq_map (pow_ne_zero f h0) (by rw [map_pow, hϖ])
  have hmono : ∀ f : ℕ, traceZero σ (ϖ ^ f) ≤ traceZero σ (ϖ ^ (f + 1)) := by
    intro f x hx
    obtain ⟨h1, h2⟩ := mem_traceZero.1 hx
    refine mem_traceZero.2 ⟨?_, h2⟩
    rw [pow_succ', mul_assoc]
    exact mul_mem hϖ1 h1
  have hstep : ∀ f : ℕ, (traceZero σ (ϖ ^ f)).relIndex (traceZero σ (ϖ ^ (f + 1))) = q := by
    intro f
    have hinj : Function.Injective (AddMonoidHom.mulLeft (ϖ ^ (f + 1))⁻¹) :=
      mul_right_injective₀ (inv_ne_zero (pow_ne_zero _ h0))
    have e : T.map (AddMonoidHom.mulLeft (ϖ ^ f)⁻¹) =
        (T.map (AddMonoidHom.mulLeft ϖ)).map (AddMonoidHom.mulLeft (ϖ ^ (f + 1))⁻¹) := by
      ext x
      simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨ϖ * y, ⟨y, hy, rfl⟩, ?_⟩
        field_simp
        ring
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨y, hy, ?_⟩
        field_simp
        ring
    rw [hS f, hS (f + 1), e, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
    exact hbase
  induction f with
  | zero =>
    rw [pow_zero, pow_zero, AddSubgroup.relIndex_self]
  | succ f ih =>
    have hle : traceZero σ 1 ≤ traceZero σ (ϖ ^ f) := by
      clear ih
      induction f with
      | zero => rw [pow_zero]
      | succ f ih => exact ih.trans (hmono f)
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle (hmono f), ih, hstep, pow_succ]

end GlobalTheory.CompanionTheory.InertZeta
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_index_formula : TraceIndex := by
  atlas_forward_decl GlobalTheory.CompanionTheory.InertZeta.traceIndex
end

section
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertLevi

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

def edge (c d : L) (f : Fin N → L) : Fin (N + 2) → L := Fin.cons c (Fin.snoc f d : Fin (N + 1) → L)

omit [Valued L (WithZero (Multiplicative ℤ))] in
@[simp] theorem edge_zero (c d : L) (f : Fin N → L) : edge c d f 0 = c := rfl

omit [Valued L (WithZero (Multiplicative ℤ))] in
@[simp] theorem edge_mid (c d : L) (f : Fin N → L) (j : Fin N) : edge c d f (mid j) = f j := by
  simp [edge, mid]

omit [Valued L (WithZero (Multiplicative ℤ))] in
@[simp] theorem edge_last (c d : L) (f : Fin N → L) : edge c d f (Fin.last (N + 1)) = d := by
  rw [edge, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]

def blkMat (x y : L) (A : Matrix (Fin N) (Fin N) L) : Matrix (Fin (N + 2)) (Fin (N + 2)) L :=
  fun i j => edge (edge x 0 (fun _ => 0) j) (edge 0 y (fun _ => 0) j) (fun p => edge 0 0 (A p) j) i

theorem gram_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (cT σ M * antiJ L n * M) i j = ∑ k, σ (M k i) * M k.rev j := by
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, antiJ, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k.rev]
  · rw [if_pos (by have := k.isLt; simp only [Fin.val_rev]; omega), mul_one]
  · intro l _ hl
    rw [if_neg, mul_zero, zero_mul]
    intro h
    apply hl
    ext
    have := k.isLt
    have := l.isLt
    simp only [Fin.val_rev]
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem blkMat_gram {x y : L} (hxy : σ x * y = 1) (hyx : σ y * x = 1) {A : Matrix (Fin N) (Fin N) L}
    (hA : cT σ A * antiJ L N * A = antiJ L N) :
    cT σ (blkMat x y A) * antiJ L (N + 2) * blkMat x y A = antiJ L (N + 2) := by
  ext i j
  rw [gram_apply, sum_idx]
  simp only [Fin.rev_last, ← mid_rev, Fin.rev_zero]
  rcases idx_cases i with rfl | ⟨r, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨s, rfl⟩ | rfl
  · simp [blkMat, antiJ]
  · simp [blkMat, antiJ, val_mid, s.isLt.ne]
  · simp [blkMat, antiJ, hxy]
  · simp [blkMat, antiJ, val_mid, r.isLt.ne]
  · have h := congrFun (congrFun hA r) s
    rw [gram_apply] at h
    simp only [blkMat, edge_zero, edge_mid, edge_last, map_zero, zero_mul, mul_zero, zero_add, add_zero]
    rw [h]
    simp only [antiJ]
    have e1 := val_mid r
    have e2 := val_mid s
    by_cases h1 : (r : ℕ) + s + 1 = N
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]
  · simp [blkMat, antiJ, val_mid]
  · simp [blkMat, antiJ, hyx]
  · simp [blkMat, antiJ, val_mid]
  · simp [blkMat, antiJ]

theorem leviExists : LeviExists := by
  intro L _ _ ϖ σ q N hU a g₀
  obtain ⟨_, _, hσϖ, hvϖ, _⟩ := hU
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    simp at hvϖ
  have hσx : σ (ϖ ^ a) = ϖ ^ a := by rw [map_zpow₀, hσϖ]
  have hσy : σ (ϖ ^ (-a)) = ϖ ^ (-a) := by rw [map_zpow₀, hσϖ]
  have hxy : σ (ϖ ^ a) * ϖ ^ (-a) = 1 := by rw [hσx, ← zpow_add₀ hϖ, add_neg_cancel, zpow_zero]
  have hyx : σ (ϖ ^ (-a)) * ϖ ^ a = 1 := by rw [hσy, ← zpow_add₀ hϖ, neg_add_cancel, zpow_zero]
  have hA : cT σ (mat g₀) * antiJ L N * mat g₀ = antiJ L N := g₀.2
  have hJJ : antiJ L (N + 2) * antiJ L (N + 2) = 1 := by
    ext i j
    simp only [Matrix.mul_apply, antiJ, Matrix.one_apply, ite_mul, one_mul, zero_mul]
    have hi := i.isLt
    have hj := j.isLt
    rw [Finset.sum_eq_single i.rev]
    · rw [if_pos (by simp only [Fin.val_rev]; omega)]
      by_cases h : i = j
      · subst h
        rw [if_pos (by simp only [Fin.val_rev]; omega), if_pos rfl]
      · rw [if_neg (by simp only [Fin.val_rev]; intro h'; apply h; ext; omega), if_neg h]
    · intro l _ hl
      rw [if_neg]
      intro h'
      apply hl
      ext
      have := l.isLt
      simp only [Fin.val_rev]
      omega
    · intro h
      exact absurd (Finset.mem_univ _) h
  set B := blkMat (ϖ ^ a) (ϖ ^ (-a)) (mat g₀) with hB
  have hG : cT σ B * antiJ L (N + 2) * B = antiJ L (N + 2) := blkMat_gram hxy hyx hA
  have hCB : antiJ L (N + 2) * cT σ B * antiJ L (N + 2) * B = 1 := by
    calc antiJ L (N + 2) * cT σ B * antiJ L (N + 2) * B
        = antiJ L (N + 2) * (cT σ B * antiJ L (N + 2) * B) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hG, hJJ]
  have hBC : B * (antiJ L (N + 2) * cT σ B * antiJ L (N + 2)) = 1 := mul_eq_one_comm.mp hCB
  let U : GL (Fin (N + 2)) L := ⟨B, antiJ L (N + 2) * cT σ B * antiJ L (N + 2), hBC, hCB⟩
  have hU : U ∈ GU σ (N + 2) := hG
  refine ⟨⟨U, hU⟩, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    show B i j = 0
    rcases idx_cases i with rfl | ⟨r, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨s, rfl⟩ | rfl <;>
      simp [hB, blkMat, blk_zero, blk_mid, blk_last] at hij ⊢
  · show B 0 0 = ϖ ^ a
    simp [hB, blkMat]
  · show B (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a)
    simp [hB, blkMat]
  · intro i j
    show B (mid i) (mid j) = mat g₀ i j
    simp [hB, blkMat]

end GlobalTheory.CompanionTheory.InertLevi

end
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_decomposition_exists : LeviExists := by
  atlas_forward_decl GlobalTheory.CompanionTheory.InertLevi.leviExists
end

section
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertZeta

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem rad_mul_levi_apply {β : Fin n → ℕ} {u p : GU σ n} (hu : u ∈ radU σ β) (hp : p ∈ leviU σ β) {i j : Fin n}
    (hij : β j ≤ β i) : mat (u * p) i j = mat p i j := by
  rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hu i i le_rfl, Matrix.one_apply_eq, one_mul]
  · intro l _ hl
    rcases le_or_gt (β l) (β i) with h1 | h1
    · rw [hu i l h1, Matrix.one_apply_ne hl.symm, zero_mul]
    · rw [hp l j (by omega), mul_zero]
  · simp

theorem rad_levi_rad_apply {β : Fin n → ℕ} {u p u' : GU σ n} (hu : u ∈ radU σ β) (hp : p ∈ leviU σ β)
    (hu' : u' ∈ radU σ β) {i j : Fin n} (hij : β j ≤ β i) : mat (u * p * u') i j = mat p i j := by
  rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hu' j j le_rfl, Matrix.one_apply_eq, mul_one]
    exact rad_mul_levi_apply hu hp hij
  · intro l _ hl
    rcases le_or_gt (β j) (β l) with h1 | h1
    · rw [hu' l j h1, Matrix.one_apply_ne hl, mul_zero]
    · rw [rad_mul_levi_apply hu hp (by omega), hp i l (by omega), zero_mul]
  · simp

variable {N : ℕ}

theorem levi_mul_zero {x y : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) : mat (x * y) 0 0 = mat x 0 0 * mat y 0 0 := by
  rw [mat_mul, Matrix.mul_apply, sum_idx, Finset.sum_eq_zero, hx 0 (Fin.last (N + 1)) (by simp), zero_mul, add_zero,
    add_zero]
  intro j _
  rw [hx 0 (mid j) (by simp), zero_mul]

theorem levi_mul_last {x y : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) :
    mat (x * y) (Fin.last (N + 1)) (Fin.last (N + 1)) =
      mat x (Fin.last (N + 1)) (Fin.last (N + 1)) * mat y (Fin.last (N + 1)) (Fin.last (N + 1)) := by
  rw [mat_mul, Matrix.mul_apply, sum_idx, Finset.sum_eq_zero, hx (Fin.last (N + 1)) 0 (by simp), zero_mul, zero_add,
    zero_add]
  intro j _
  rw [hx (Fin.last (N + 1)) (mid j) (by simp), zero_mul]

theorem levi_mul_mid {x y : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) (i j : Fin N) :
    mat (x * y) (mid i) (mid j) = ∑ k, mat x (mid i) (mid k) * mat y (mid k) (mid j) := by
  rw [mat_mul, Matrix.mul_apply, sum_idx, hx (mid i) 0 (by simp), hx (mid i) (Fin.last (N + 1)) (by simp)]
  simp

end

theorem cosetInj : CosetInj := by
  intro L _ _ ϖ σ q N hU a a' g₀ g₀' m m' hm hm' u hu u' hu' hk
  obtain ⟨-, hσ, hσϖ, hϖ, -, -, -⟩ := hU
  obtain ⟨hl, h0, h1, h2⟩ := hm
  obtain ⟨hl', h0', h1', h2'⟩ := hm'
  have hli : m⁻¹ ∈ leviU σ (blk N) := inv_mem hl
  have hp : m⁻¹ * m' ∈ leviU σ (blk N) := mul_mem hli hl'
  have e : (m * u)⁻¹ * (m' * u') = u⁻¹ * (m⁻¹ * m') * u' := by group
  rw [e] at hk
  have hint : ∀ i j, blk N j ≤ blk N i → mat (m⁻¹ * m') i j ∈ intL L := fun i j hij => by
    rw [← rad_levi_rad_apply (inv_mem hu) hp hu' hij]
    exact (mem_KU_iff hσ _).1 hk i j
  have e0 : mat (m⁻¹ * m') 0 0 = ϖ ^ (a' - a) := by
    have hϖ0 : ϖ ≠ 0 := fun h => by
      rw [h, map_zero] at hϖ
      exact WithZero.coe_ne_zero hϖ.symm
    rw [levi_mul_zero hli, mat_inv_apply, Fin.rev_zero, h1, h0', map_zpow₀, hσϖ, ← zpow_add₀ hϖ0]
    congr 1 <;> ring
  have e1 : mat (m⁻¹ * m') (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (a - a') := by
    have hϖ0 : ϖ ≠ 0 := fun h => by
      rw [h, map_zero] at hϖ
      exact WithZero.coe_ne_zero hϖ.symm
    rw [levi_mul_last hli, mat_inv_apply, Fin.rev_last, h0, h1', map_zpow₀, hσϖ, ← zpow_add₀ hϖ0]
    congr 1 <;> ring
  have hv0 : 0 < Valued.v ϖ := by rw [hϖ]; exact WithZero.zero_lt_coe _
  have hv1 : Valued.v ϖ < 1 := by
    rw [hϖ]
    exact WithZero.coe_lt_one.2 (by decide)
  have i0 : Valued.v ϖ ^ (a' - a) ≤ 1 := by
    have : Valued.v (mat (m⁻¹ * m') 0 0) ≤ 1 := hint 0 0 le_rfl
    rwa [e0, map_zpow₀] at this
  have i1 : Valued.v ϖ ^ (a - a') ≤ 1 := by
    have : Valued.v (mat (m⁻¹ * m') (Fin.last (N + 1)) (Fin.last (N + 1))) ≤ 1 :=
      hint _ _ (le_refl (blk N (Fin.last (N + 1))))
    rwa [e1, map_zpow₀] at this
  rw [zpow_le_one_iff_right_of_lt_one₀ hv0 hv1] at i0 i1
  refine ⟨by omega, (mem_KU_iff hσ _).2 fun i j => ?_⟩
  have := hint (mid i) (mid j) (by simp)
  have e2 : ∀ i j, mat m⁻¹ (mid i) (mid j) = mat g₀⁻¹ i j := fun i j => by
    rw [mat_inv_apply, mat_inv_apply, ← mid_rev, ← mid_rev, h2]
  rw [levi_mul_mid hli] at this
  simp only [e2, h2'] at this
  rw [mat_mul, Matrix.mul_apply]
  exact this

end GlobalTheory.CompanionTheory.InertZeta

end
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_injective : CosetInj := by
  atlas_forward_decl GlobalTheory.CompanionTheory.InertZeta.cosetInj
end

section
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertTrans

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem conj_mem_radU {n : ℕ} {β : Fin n → ℕ} {m u : GU σ n} (hm : m ∈ leviU σ β) (hu : u ∈ radU σ β) :
    m * u * m⁻¹ ∈ radU σ β := by
  have hA : ∀ i j, β i ≠ β j → mat m i j = 0 := hm
  have hC : ∀ i j, β i ≠ β j → mat m⁻¹ i j = 0 := inv_mem hm
  have hB : ∀ i j, β j ≤ β i → mat u i j = (1 : Matrix (Fin n) (Fin n) L) i j := hu
  show ∀ i j, β j ≤ β i → mat (m * u * m⁻¹) i j = (1 : Matrix (Fin n) (Fin n) L) i j
  intro i j h
  have e : (mat m * mat u * mat m⁻¹) i j = (mat m * mat m⁻¹) i j := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : β p = β j
    · congr 1
      rw [Matrix.mul_apply]
      calc _ = ∑ l, mat m i l * (1 : Matrix (Fin n) (Fin n) L) l p := Finset.sum_congr rfl fun l _ => by
              by_cases hl : β i = β l
              · rw [hB l p (by omega)]
              · rw [hA i l hl, zero_mul, zero_mul]
        _ = _ := by rw [← Matrix.mul_apply, Matrix.mul_one]
    · rw [hC p j hp, mul_zero, mul_zero]
  rw [mat_mul, mat_mul, e, mat_mul_inv]

theorem blk_mono {i j : Fin (N + 2)} (h : j < i) : blk N j ≤ blk N i := by
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl
  · simp at h
  · simp at h
  · simp at h
  · simp
  · simp
  · exact absurd h (not_lt.2 (Fin.le_last _))
  · simp
  · simp
  · simp

theorem isUnipU_of_radQ {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) : IsUnipU u := by
  have hB : ∀ i j, blk N j ≤ blk N i → mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j := hu
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · exact (hB i j (blk_mono h)).trans (Matrix.one_apply_ne (ne_of_gt h))
  · exact (hB i i le_rfl).trans (Matrix.one_apply_eq i)

theorem levi_off {ϖ : L} {a : ℤ} {g : GU σ N} {m : GU σ (N + 2)} (h : IsLeviElt ϖ a g m) :
    (∀ l, mat m 0 (mid l) = 0) ∧ (∀ l, mat m (mid l) 0 = 0) ∧ mat m 0 (Fin.last (N + 1)) = 0 ∧
      mat m (Fin.last (N + 1)) 0 = 0 ∧ (∀ l, mat m (mid l) (Fin.last (N + 1)) = 0) ∧
      ∀ l, mat m (Fin.last (N + 1)) (mid l) = 0 := by
  have hA : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := h.1
  exact ⟨fun l => hA _ _ (by simp), fun l => hA _ _ (by simp), hA _ _ (by simp), hA _ _ (by simp),
    fun l => hA _ _ (by simp), fun l => hA _ _ (by simp)⟩

theorem levi_borel {ϖ : L} {a : ℤ} {g : GU σ N} {m : GU σ (N + 2)} (h : IsLeviElt ϖ a g m) (hg : IsBorelU g) :
    IsBorelU m := by
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := levi_off h
  intro i j hij
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl
  · simp at hij
  · simp at hij
  · simp at hij
  · exact o2 _
  · exact (h.2.2.2 i j).trans (hg i j (by
      have h' : j.val + 1 < i.val + 1 := hij
      exact Fin.lt_def.2 (by omega)))
  · exact absurd hij (not_lt.2 (Fin.le_last _))
  · exact o4
  · exact o6 _
  · exact absurd hij (lt_irrefl _)

theorem levi_mem_K {ϖ : L} {g : GU σ N} {m : GU σ (N + 2)} (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (h : IsLeviElt ϖ 0 g m) (hg : g ∈ KU σ N) : m ∈ KU σ (N + 2) := by
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := levi_off h
  rw [mem_KU_iff hσ]
  intro i j
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl
  · rw [h.2.1, zpow_zero]; exact one_mem _
  · rw [o1]; exact zero_mem _
  · rw [o3]; exact zero_mem _
  · rw [o2]; exact zero_mem _
  · rw [h.2.2.2]; exact P.fSatake_K_int hg i j
  · rw [o5]; exact zero_mem _
  · rw [o4]; exact zero_mem _
  · rw [o6]; exact zero_mem _
  · rw [h.2.2.1, neg_zero, zpow_zero]; exact one_mem _

theorem levi_eq_mul {ϖ : L} {a : ℤ} {b k : GU σ N} {mb mk m : GU σ (N + 2)} (hb : IsLeviElt ϖ a b mb)
    (hk : IsLeviElt ϖ 0 k mk) (hm : IsLeviElt ϖ a (b * k) m) : m = mb * mk := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := levi_off hb
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := levi_off hk
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := levi_off hm
  apply mat_injective
  ext i j
  rw [mat_mul, Matrix.mul_apply, sum_idx]
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
    simp only [b1, b2, b3, b4, b5, b6, k1, k2, k3, k4, k5, k6, m1, m2, m3, m4, m5, m6, hb.2.1, hb.2.2.1, hb.2.2.2,
      hk.2.1, hk.2.2.1, hk.2.2.2, hm.2.1, hm.2.2.1, hm.2.2.2, zero_mul, mul_zero, Finset.sum_const_zero, add_zero,
      zero_add, zpow_zero, neg_zero, mul_one, mat_mul, Matrix.mul_apply]

theorem sphTrans_of_leviExists : LeviExists → SphTrans := by
  intro hL L _ _ ϖ σ q N r hU hr α φ φ₀ hα hφ h1 hφ₀ h01 a g₀ m hm u hu
  obtain ⟨b₀, k₀, hb₀, hk₀, rfl⟩ := P.fIwasawa_iwasawa σ hU.1 hU.2.1 g₀
  obtain ⟨mb, hmb⟩ := hL L ϖ σ q N hU a b₀
  obtain ⟨mk, hmk⟩ := hL L ϖ σ q N hU 0 k₀
  have e := levi_eq_mul hmb hmk hm
  have hkK : mk ∈ KU σ (N + 2) := levi_mem_K hU.2.1 hmk hk₀
  have hmbB : IsBorelU mb := levi_borel hmb hb₀
  have hu' : mk * u * mk⁻¹ ∈ radQ σ N := conj_mem_radU hmk.1 hu
  have hu'B := isUnipU_of_radQ hu'
  have e2 : m * u = (mb * (mk * u * mk⁻¹)) * 1 * mk := by rw [e]; group
  have d : ∀ (i : Fin (N + 2)) (x : L), mat mb i i = x →
      (((mb * (mk * u * mk⁻¹) : GU σ (N + 2)) : GL (Fin (N + 2)) L) : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i i = x := by
    intro i x hx
    have := P.fSatake_borel_diag_mul hmbB hu'B.1 i
    rw [hu'B.2, mul_one] at this
    exact this.trans hx
  have e3 : φ₀ (b₀ * k₀) = chiDeltaU q (Fin.tail α) b₀ := by
    have := hφ₀ b₀ 1 k₀ hb₀ hk₀
    rwa [mul_one, h01, mul_one] at this
  rw [e2, hφ _ _ _ (P.fSatake_borel_mul hmbB hu'B.1) hkK, h1, mul_one, e3]
  unfold chiDeltaU
  rw [Fin.prod_univ_succ]
  congr 1
  · have h0 : ((0 : Fin (r + 1)) : ℕ) < N + 2 := by simp
    rw [dif_pos h0]
    have e0 : (⟨((0 : Fin (r + 1)) : ℕ), h0⟩ : Fin (N + 2)) = 0 := rfl
    rw [e0, d _ _ hmb.2.1, P.fSatake_ord_zpow hU.2.2.2.1]
    push_cast
    simp only [Fin.val_zero]
    congr 3
    push_cast
    ring
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi : i.val < N := by have := i.2; omega
    have hi' : (i.succ : Fin (r + 1)).val < N + 2 := by simp; omega
    rw [dif_pos hi, dif_pos hi']
    have ei : (⟨(i.succ : Fin (r + 1)).val, hi'⟩ : Fin (N + 2)) = mid ⟨i.val, hi⟩ := by
      ext; simp
    rw [ei, d _ _ (hmb.2.2.2 ⟨i.val, hi⟩ ⟨i.val, hi⟩)]
    have ex : ((N + 2 : ℕ) : ℤ) - 1 - 2 * ((i.succ : Fin (r + 1)).val : ℤ) = (N : ℤ) - 1 - 2 * (i.val : ℤ) := by
      simp; ring
    rw [ex]
    rfl

end GlobalTheory.CompanionTheory.InertTrans

end
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_transitive_of_levi : LeviExists → SphTrans := by
  atlas_forward_decl GlobalTheory.CompanionTheory.InertTrans.sphTrans_of_leviExists
end

section
section
open Formalism.UG GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertZeta

private theorem mem_range_bc_of_entries_mem_intL {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    (g : GL (Fin n) L) (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) :
    g ∈ (Formalism.UG.bc (Formalism.UG.intL L).subtype).range := by
  let M : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) := fun i j => ⟨_, h1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) := fun i j => ⟨_, h2 i j⟩
  have hM : (Formalism.UG.intL L).subtype.mapMatrix M = g := by ext i j; rfl
  have hM' : (Formalism.UG.intL L).subtype.mapMatrix M' = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    ext i j; rfl
  have inj : Function.Injective
      ((Formalism.UG.intL L).subtype.mapMatrix : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) → Matrix (Fin n) (Fin n) L) :=
    fun A B h => Matrix.ext fun i j => Subtype.ext (by simpa [RingHom.mapMatrix_apply] using congrFun (congrFun h i) j)
  refine ⟨⟨M, M', inj ?_, inj ?_⟩, Units.ext hM⟩
  · rw [map_mul, map_one, hM, hM']
    exact g.mul_inv
  · rw [map_mul, map_one, hM, hM']
    exact g.inv_mul

private theorem entry_lemma_2 {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
    (hv : ∀ x, Valued.v (σ x) = Valued.v x) (g : Formalism.UG.GU σ 1) (i j : Fin 1) :
    ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) i j ∈ Formalism.UG.intL L := by
  have hg : Formalism.UG.cT σ ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) * Formalism.UG.antiJ L 1 *
      ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) = Formalism.UG.antiJ L 1 := g.2
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  set x := ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) 0 0 with hx
  have e : σ x * x = 1 := by
    have := congrFun (congrFun hg 0) 0
    simpa [Matrix.mul_apply, Formalism.UG.cT, Formalism.UG.antiJ, hx] using this
  have e2 : Valued.v x ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [← hv x]
    rw [← map_mul, e, map_one]
  refine (Valuation.mem_integer_iff _ _).mpr ?_
  exact (pow_le_one_iff two_ne_zero).mp e2.le

theorem smallRank : SmallRank := by
  intro L _ _ ϖ σ q n hσ hn g
  rw [Formalism.UG.KU, Subgroup.mem_subgroupOf, Formalism.UG.intPts, Subgroup.mem_inf]
  refine ⟨g.2, ?_⟩
  interval_cases n
  · exact mem_range_bc_of_entries_mem_intL _ (fun i => i.elim0) (fun i => i.elim0)
  · exact mem_range_bc_of_entries_mem_intL _ (entry_lemma_2 hσ.2.1 g) (entry_lemma_2 hσ.2.1 g⁻¹)

end GlobalTheory.CompanionTheory.InertZeta
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_rank_bound : SmallRank := by
  atlas_forward_decl GlobalTheory.CompanionTheory.InertZeta.smallRank
end

section
section
open MeasureTheory GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertZeta

theorem cosetIntegral : CosetIntegral := by
  intro G _ _ _ _ _ μ _ K hK hμK F Z hF hZ
  set f : G ⧸ K → ℂ := fun x => F x.out with hf_def
  have hFf : ∀ g, F g = f (QuotientGroup.mk g) := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K g
    simp only [hf_def, hh, hF g h h.2]
  set C : G ⧸ K → Set G := fun x => (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {x} with hC_def
  have hC_eq : ∀ x, C x = (fun h => x.out⁻¹ * h) ⁻¹' (K : Set G) := by
    intro x
    ext g
    simp only [hC_def, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    conv_lhs => rw [← QuotientGroup.out_eq' x]
    rw [eq_comm, QuotientGroup.eq]
  have hC_open : ∀ x, IsOpen (C x) := fun x => by
    rw [hC_eq]
    exact hK.preimage (continuous_const_mul _)
  have hC_meas : ∀ x, MeasurableSet (C x) := fun x => (hC_open x).measurableSet
  have hC_one : ∀ x, μ (C x) = 1 := fun x => by
    rw [hC_eq, measure_preimage_mul, hμK]
  have hF_on : ∀ x, Set.EqOn F (fun _ => f x) (C x) := by
    intro x g hg
    simp only [hC_def, Set.mem_preimage, Set.mem_singleton_iff] at hg
    rw [hFf g, hg]
  have hcount : (Function.support f).Countable := hZ.summable.countable_support
  have : Countable (Function.support f) := hcount.to_subtype
  set s : Function.support f → Set G := fun i => C i with hs_def
  have hs_meas : ∀ i, MeasurableSet (s i) := fun i => hC_meas _
  have hs_disj : Pairwise (Function.onFun Disjoint s) := by
    intro i j hij
    refine Disjoint.preimage _ (Set.disjoint_singleton.2 fun h => hij (Subtype.ext h))
  have hs_int : ∀ i, IntegrableOn F (s i) μ := by
    intro i
    refine (integrableOn_const (by rw [hC_one]; exact ENNReal.one_ne_top)).congr_fun
      (fun g hg => (hF_on i hg).symm) (hs_meas i)
  have hs_val : ∀ i, ∫ g in s i, F g ∂μ = f i := by
    intro i
    rw [setIntegral_congr_fun (hs_meas i) (hF_on i), setIntegral_const]
    simp [Measure.real, hs_def, hC_one]
  have hs_norm : ∀ i, ∫ g in s i, ‖F g‖ ∂μ = ‖f i‖ := by
    intro i
    rw [setIntegral_congr_fun (hs_meas i) (fun g hg => congrArg norm (hF_on i hg)), setIntegral_const]
    simp [Measure.real, hs_def, hC_one]
  have hU : IntegrableOn F (⋃ i, s i) μ := by
    refine integrableOn_iUnion_of_summable_integral_norm hs_int ?_
    simp only [hs_norm]
    exact hZ.summable.norm.subtype _
  have hout : ∀ g, g ∉ ⋃ i, s i → F g = 0 := by
    intro g hg
    by_contra hne
    apply hg
    have hmem : QuotientGroup.mk g ∈ Function.support f := by
      rw [Function.mem_support, ← hFf g]
      exact hne
    exact Set.mem_iUnion.2 ⟨⟨_, hmem⟩, rfl⟩
  have hint : Integrable F μ := hU.integrable_of_forall_notMem_eq_zero hout
  refine ⟨hint, ?_⟩
  have hsum := hasSum_integral_iUnion hs_meas hs_disj hU
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout] at hsum
  simp only [hs_val] at hsum
  exact (hasSum_subtype_support.1 hsum).unique hZ

end GlobalTheory.CompanionTheory.InertZeta
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetIntegral' : CosetIntegral := by
  atlas_forward_decl GlobalTheory.CompanionTheory.InertZeta.cosetIntegral
end

section
section
noncomputable section

open Formalism.UG GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertZeta

variable {G : Type} [Group G] {K : Subgroup G}

def cosetsIn (hK : IsCommensurated K) (g : G) : Finset (G ⧸ K) :=
  (P.finite_cosets_in_doset hK g).toFinset

theorem mem_cosetsIn {hK : IsCommensurated K} {g : G} {x : G ⧸ K} :
    x ∈ cosetsIn hK g ↔ x.out ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by
  rw [cosetsIn, Set.Finite.mem_toFinset, DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, a.2, b, b.2, h⟩
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩

theorem hAct_dosetInd (hK : IsCommensurated K) (g : G) (f : G → ℂ) :
    hAct K (dosetInd ℂ K g) f 1 = ∑ x ∈ cosetsIn hK g, f x.out := by
  unfold hAct
  rw [finsum_eq_sum_of_support_subset (s := cosetsIn hK g)]
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hm : x.out ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := mem_cosetsIn.mp hx
    simp [dosetInd, Set.indicator_apply, hm]
  · intro x hx
    rw [Function.mem_support] at hx
    rw [Finset.mem_coe, mem_cosetsIn]
    by_contra hm
    apply hx
    simp [dosetInd, Set.indicator_apply, hm]

theorem eq_of_mem_cosetsIn {hK : IsCommensurated K} {f : G → ℂ} (hf : IsBiInv K f) {g : G} {x : G ⧸ K}
    (hx : x ∈ cosetsIn hK g) : f x.out = f g := by
  obtain ⟨a, ha, b, hb, h⟩ := DoubleCoset.mem_doubleCoset.mp (mem_cosetsIn.mp hx)
  rw [h]
  exact hf ⟨a, ha⟩ ⟨b, hb⟩ g

def dosetOf (x : G ⧸ K) : Set G := DoubleCoset.doubleCoset x.out (K : Set G) (K : Set G)

theorem dosetOf_eq_iff {hK : IsCommensurated K} {x y : G ⧸ K} : dosetOf y = dosetOf x ↔ y ∈ cosetsIn hK x.out := by
  rw [mem_cosetsIn]
  unfold dosetOf
  constructor
  · intro h
    rw [← h]
    exact DoubleCoset.mem_doubleCoset_self K K y.out
  · intro h
    exact DoubleCoset.doubleCoset_eq_of_mem h

theorem tsum_fiber {M : Type} [AddCommMonoid M] [TopologicalSpace M] (hK : IsCommensurated K) (x : G ⧸ K)
    (h : G ⧸ K → M) : ∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, h c = ∑ y ∈ cosetsIn hK x.out, h y := by
  rw [← Finset.tsum_subtype (cosetsIn hK x.out) h]
  exact (Equiv.subtypeEquivRight
    (fun y => (dosetOf_eq_iff (hK := hK) (x := x) (y := y)))).tsum_eq (fun c => h c.1)

theorem finite_fiber (hK : IsCommensurated K) (q : Set G) : Finite {y : G ⧸ K // dosetOf y = q} := by
  by_cases hne : ∃ y : G ⧸ K, dosetOf y = q
  · obtain ⟨x, rfl⟩ := hne
    exact Finite.of_equiv _ (Equiv.subtypeEquivRight
      (fun y => (dosetOf_eq_iff (hK := hK) (x := x) (y := y)))).symm
  · haveI : IsEmpty {y : G ⧸ K // dosetOf y = q} := ⟨fun c => hne ⟨c.1, c.2⟩⟩
    infer_instance

theorem fiber_compare (hK : IsCommensurated K) {F w φ : G → ℂ} (hF : IsBiInv K F) (hw : IsBiInv K w)
    (h : ∀ g, hAct K (dosetInd ℂ K g) w 1 = hAct K (dosetInd ℂ K g) φ 1) (q : Set G) :
    ∑' c : {y : G ⧸ K // dosetOf y = q}, F c.1.out * φ c.1.out = ∑' c : {y : G ⧸ K // dosetOf y = q}, F c.1.out * w c.1.out ∧
    ∑' c : {y : G ⧸ K // dosetOf y = q}, ‖F c.1.out * w c.1.out‖ ≤
      ∑' c : {y : G ⧸ K // dosetOf y = q}, ‖F c.1.out * φ c.1.out‖ := by
  by_cases hne : ∃ y : G ⧸ K, dosetOf y = q
  · obtain ⟨x, rfl⟩ := hne
    have t1 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, F c.1.out * φ c.1.out) =
        ∑ y ∈ cosetsIn hK x.out, F y.out * φ y.out := tsum_fiber hK x (fun y => F y.out * φ y.out)
    have t2 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, F c.1.out * w c.1.out) =
        ∑ y ∈ cosetsIn hK x.out, F y.out * w y.out := tsum_fiber hK x (fun y => F y.out * w y.out)
    have t3 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, ‖F c.1.out * w c.1.out‖) =
        ∑ y ∈ cosetsIn hK x.out, ‖F y.out * w y.out‖ := tsum_fiber hK x (fun y => ‖F y.out * w y.out‖)
    have t4 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, ‖F c.1.out * φ c.1.out‖) =
        ∑ y ∈ cosetsIn hK x.out, ‖F y.out * φ y.out‖ := tsum_fiber hK x (fun y => ‖F y.out * φ y.out‖)
    rw [t1, t2, t3, t4]
    have hF' : ∀ y ∈ cosetsIn hK x.out, F y.out = F x.out := fun y hy => eq_of_mem_cosetsIn hF hy
    have hW' : ∀ y ∈ cosetsIn hK x.out, w y.out = w x.out := fun y hy => eq_of_mem_cosetsIn hw hy
    have hsum : ∑ y ∈ cosetsIn hK x.out, φ y.out = ∑ y ∈ cosetsIn hK x.out, w y.out := by
      rw [← hAct_dosetInd hK, ← hAct_dosetInd hK, h]
    have e1 : ∑ y ∈ cosetsIn hK x.out, F y.out * φ y.out = F x.out * ∑ y ∈ cosetsIn hK x.out, φ y.out := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y hy => by rw [hF' y hy]
    have e2 : ∑ y ∈ cosetsIn hK x.out, F y.out * w y.out = F x.out * ∑ y ∈ cosetsIn hK x.out, w y.out := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y hy => by rw [hF' y hy]
    have e4 : ∑ y ∈ cosetsIn hK x.out, F y.out * w y.out = ∑ y ∈ cosetsIn hK x.out, F y.out * φ y.out := by
      rw [e1, e2, hsum]
    have hc : ∀ y ∈ cosetsIn hK x.out, F y.out * w y.out = F x.out * w x.out := fun y hy => by
      rw [hF' y hy, hW' y hy]
    have e3 : ∑ y ∈ cosetsIn hK x.out, ‖F y.out * w y.out‖ = ‖∑ y ∈ cosetsIn hK x.out, F y.out * w y.out‖ := by
      rw [Finset.sum_congr rfl hc, Finset.sum_congr rfl (fun y hy => congrArg (‖·‖) (hc y hy))]
      simp only [Finset.sum_const, nsmul_eq_mul, norm_mul, Complex.norm_natCast]
    refine ⟨e4.symm, ?_⟩
    rw [e3, e4]
    exact norm_sum_le _ _
  · haveI : IsEmpty {y : G ⧸ K // dosetOf y = q} := ⟨fun c => hne ⟨c.1, c.2⟩⟩
    simp only [tsum_empty, le_refl, and_self]

theorem dosetSwap : DosetSwap := by
  intro G _ K hK F w φ Z hF hw h ha
  let e : (Σ q : Set G, {y : G ⧸ K // dosetOf y = q}) ≃ G ⧸ K := Equiv.sigmaFiberEquiv dosetOf
  have haN : Summable fun x : G ⧸ K => ‖F x.out * φ x.out‖ := summable_norm_iff.mpr ha.summable
  have haN' : Summable fun p => ‖F (e p).out * φ (e p).out‖ :=
    (e.summable_iff (f := fun x : G ⧸ K => ‖F x.out * φ x.out‖)).mpr haN
  have hbN' : Summable fun p => ‖F (e p).out * w (e p).out‖ := by
    rw [summable_sigma_of_nonneg (fun p => norm_nonneg _)]
    refine ⟨fun q => ?_, ?_⟩
    · haveI := finite_fiber hK q
      exact Summable.of_finite
    · have hA := ((summable_sigma_of_nonneg (fun p => norm_nonneg _)).mp haN').2
      refine Summable.of_nonneg_of_le (fun q => tsum_nonneg fun _ => norm_nonneg _) (fun q => ?_) hA
      exact (fiber_compare hK hF hw h q).2
  have hbN : Summable fun x : G ⧸ K => ‖F x.out * w x.out‖ :=
    (e.summable_iff (f := fun x : G ⧸ K => ‖F x.out * w x.out‖)).mp hbN'
  have hbS : Summable fun x : G ⧸ K => F x.out * w x.out := hbN.of_norm
  have hbS' : Summable fun p => F (e p).out * w (e p).out :=
    (e.summable_iff (f := fun x : G ⧸ K => F x.out * w x.out)).mpr hbS
  have haS' : Summable fun p => F (e p).out * φ (e p).out :=
    (e.summable_iff (f := fun x : G ⧸ K => F x.out * φ x.out)).mpr ha.summable
  have key : ∑' x : G ⧸ K, F x.out * w x.out = ∑' x : G ⧸ K, F x.out * φ x.out := by
    calc ∑' x : G ⧸ K, F x.out * w x.out = ∑' p, F (e p).out * w (e p).out :=
          (e.tsum_eq (fun x => F x.out * w x.out)).symm
      _ = ∑' q, ∑' c : {y : G ⧸ K // dosetOf y = q}, F c.1.out * w c.1.out := hbS'.tsum_sigma
      _ = ∑' q, ∑' c : {y : G ⧸ K // dosetOf y = q}, F c.1.out * φ c.1.out :=
          tsum_congr fun q => ((fiber_compare hK hF hw h q).1).symm
      _ = ∑' p, F (e p).out * φ (e p).out := haS'.tsum_sigma.symm
      _ = ∑' x : G ⧸ K, F x.out * φ x.out := e.tsum_eq (fun x => F x.out * φ x.out)
  have hb := hbS.hasSum
  rwa [key, ha.tsum_eq] at hb

end GlobalTheory.CompanionTheory.InertZeta
end
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_coset_swap : DosetSwap := by
  atlas_forward_decl GlobalTheory.CompanionTheory.InertZeta.dosetSwap
end

section
section
open GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertGenFun

theorem hasSum_counts (q N c : ℕ) (X : ℂ) (h : ‖(q : ℂ) ^ (N + 1) * X‖ < 1) :
    HasSum (fun j : ℕ => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : ℂ) * X ^ j)
      (c * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2)) := by
  set y : ℂ := (q : ℂ) ^ (N + 1) * X with hy
  set F : ℕ → ℂ := fun j => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : ℂ) * X ^ j with hF
  have hy2 : ‖y ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg y]
  have hg := hasSum_geometric_of_norm_lt_one hy2
  have hev : HasSum (fun m : ℕ => F (2 * m)) (c * (1 - y ^ 2)⁻¹) := by
    have hfun : (fun m : ℕ => F (2 * m)) = fun m => (c : ℂ) * (y ^ 2) ^ m := by
      funext m
      simp only [hF]
      rw [Nat.mul_div_cancel_left m (by norm_num : 0 < 2), hy]
      push_cast
      ring
    rw [hfun]
    exact hg.mul_left _
  have hodd : HasSum (fun m : ℕ => F (2 * m + 1)) (c * q * X * (1 - y ^ 2)⁻¹) := by
    have hfun : (fun m : ℕ => F (2 * m + 1)) = fun m => (c * q * X : ℂ) * (y ^ 2) ^ m := by
      funext m
      simp only [hF]
      rw [show (2 * m + 1) / 2 = m by omega, hy]
      push_cast
      ring
    rw [hfun]
    exact hg.mul_left _
  have hne : (1 : ℂ) - y ^ 2 ≠ 0 := by
    intro h0
    have : ‖y ^ 2‖ = 1 := by
      rw [show y ^ 2 = 1 by linear_combination -h0]
      simp
    linarith
  have hval : (c : ℂ) * (1 + q * X) / (1 - y ^ 2) = c * (1 - y ^ 2)⁻¹ + c * q * X * (1 - y ^ 2)⁻¹ := by
    field_simp
  rw [hval]
  exact HasSum.even_add_odd hev hodd

theorem hasSum_of_counts {ι : Type} (g : ι → ℕ) (A : ℕ → ℕ) (hA : ∀ j, A j ≠ 0)
    (hc : ∀ j, Nat.card {i // g i ≤ j} = A j) (X s : ℂ)
    (hT : HasSum (fun j : ℕ => (A j : ℂ) * X ^ j) s) :
    HasSum (fun i => X ^ g i) ((1 - X) * s) := by
  have hfinle : ∀ j, Finite {i // g i ≤ j} := fun j =>
    Nat.finite_of_card_ne_zero (by rw [hc j]; exact hA j)
  have hfin : ∀ j, Finite {i // g i = j} := fun j =>
    Finite.of_injective (fun c : {i // g i = j} => (⟨c.1, c.2.le⟩ : {i // g i ≤ j}))
      (fun a b h => Subtype.ext (congrArg Subtype.val h :))
  have hcard : ∀ j, Nat.card {i // g i = j} + (if j = 0 then 0 else A (j - 1)) = A j := by
    intro j
    rcases j with _ | k
    · simp only [if_true, add_zero, ← hc 0]
      exact Nat.card_congr (Equiv.subtypeEquivRight (fun i => by omega))
    · have : ∀ i, g i ≤ k + 1 ↔ g i ≤ k ∨ g i = k + 1 := fun i => by omega
      have e := (Equiv.subtypeEquivRight this).trans
        (subtypeOrEquiv (fun i => g i ≤ k) (fun i => g i = k + 1)
          (Pi.disjoint_iff.2 fun i => Prop.disjoint_iff.2 (by omega)))
      rw [← hc (k + 1), Nat.card_congr e, Nat.card_sum, if_neg (Nat.succ_ne_zero k),
        Nat.add_sub_cancel, ← hc k, add_comm]
  have hfib : ∀ (j : ℕ) {M : Type} [AddCommMonoid M] [TopologicalSpace M] (F : ℕ → M),
      HasSum (fun c : {i // g i = j} => F (g c)) (Nat.card {i // g i = j} • F j) := by
    intro j M _ _ F
    have := hfin j
    have : Fintype {i // g i = j} := Fintype.ofFinite _
    convert hasSum_fintype (fun c : {i // g i = j} => F (g c)) using 1
    rw [Finset.sum_congr rfl (fun c _ => by rw [c.2]), Finset.sum_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hle : ∀ j, Nat.card {i // g i = j} ≤ A j := fun j => by
    have := hcard j
    omega
  have hnorm : Summable (fun j : ℕ => (A j : ℝ) * ‖X‖ ^ j) := by
    have := hT.summable.norm
    simpa [norm_mul, norm_pow] using this
  have hsum : Summable (fun i => X ^ g i) := by
    apply Summable.of_norm
    rw [← (Equiv.sigmaFiberEquiv g).summable_iff]
    show Summable fun p : (Σ j : ℕ, {i // g i = j}) => ‖X ^ g (p.2 : ι)‖
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun j => (hfib j (fun n => ‖X ^ n‖)).summable, ?_⟩
    refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun _ => norm_nonneg _) (fun j => ?_) hnorm
    have h1 := (hfib j (fun n => ‖X ^ n‖)).tsum_eq
    rw [h1, nsmul_eq_mul, norm_pow]
    gcongr
    exact_mod_cast hle j
  obtain ⟨t, ht⟩ := hsum
  have hsig := ((Equiv.sigmaFiberEquiv g).hasSum_iff.2 ht).sigma
    (fun j => hfib j (fun n => X ^ n))
  have hshift : HasSum (fun j : ℕ => ((if j = 0 then 0 else A (j - 1) : ℕ) : ℂ) * X ^ j) (s * X) := by
    have h0 : HasSum (fun n : ℕ => ((if n + 1 = 0 then 0 else A (n + 1 - 1) : ℕ) : ℂ) * X ^ (n + 1))
        (s * X) := by
      have hfun : (fun n : ℕ => ((if n + 1 = 0 then 0 else A (n + 1 - 1) : ℕ) : ℂ) * X ^ (n + 1)) =
          fun n => (A n : ℂ) * X ^ n * X := by
        funext n
        rw [if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel, pow_succ]
        ring
      rw [hfun]
      exact hT.mul_right X
    have h1 := (hasSum_nat_add_iff
      (f := fun j : ℕ => ((if j = 0 then 0 else A (j - 1) : ℕ) : ℂ) * X ^ j) 1).1 h0
    simp only [Finset.sum_range_one, ↓reduceIte, Nat.cast_zero, zero_mul, add_zero] at h1
    exact h1
  have hdiff := hT.sub hshift
  have heq : (fun j : ℕ => (A j : ℂ) * X ^ j - ((if j = 0 then 0 else A (j - 1) : ℕ) : ℂ) * X ^ j) =
      fun j => Nat.card {i // g i = j} • X ^ j := by
    funext j
    rw [nsmul_eq_mul, ← hcard j]
    push_cast
    ring
  rw [heq] at hdiff
  have := hsig.unique hdiff
  rw [this] at ht
  rwa [show (1 - X) * s = s - s * X by ring]

theorem genFun : GenFun := by
  intro ι f l c q N X hc hq hf hcount hX
  have hA : ∀ j, c * q ^ (2 * N * (j / 2) + j) ≠ 0 := fun j =>
    Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
  have hcg : ∀ j, Nat.card {i // f i - l ≤ j} = c * q ^ (2 * N * (j / 2) + j) := by
    intro j
    rw [← hcount j]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun i => by have := hf i; omega))
  have h := hasSum_of_counts (fun i => f i - l) (fun j => c * q ^ (2 * N * (j / 2) + j)) hA hcg X _
    (hasSum_counts q N c X hX)
  have key : (fun i => X ^ f i) = fun i => X ^ l * X ^ (f i - l) := by
    funext i
    rw [← pow_add]
    congr 1
    have := hf i
    omega
  rw [key, show (c : ℂ) * X ^ l * jFac q N X =
    X ^ l * ((1 - X) * (c * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2))) by unfold jFac; ring]
  exact h.mul_left _

end GlobalTheory.CompanionTheory.InertGenFun
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generating_function_identity : GenFun := by
  atlas_forward_decl GlobalTheory.CompanionTheory.InertGenFun.genFun
end

section
noncomputable section

open Formalism.UG Matrix MeasureTheory GlobalTheory.SatakeWeyl GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables GlobalTheory GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertZetaTop

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {q n : ℕ}

theorem v_det_mat (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (g : GU σ n) : Valued.v (mat g).det = 1 := by
  have h : cT σ (mat g) * antiJ L n * mat g = antiJ L n := g.2
  have h1 := congrArg (fun M => Valued.v (det M)) h
  have hJ : IsInt (antiJ L n) := fun i j => by
    unfold antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  simp only [det_mul, map_mul, cT, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hσ,
    v_det_eq_one hJ hJ GlobalTheory.UnitarySwap.antiJ_mul_self, mul_one] at h1
  exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 (by rw [sq, h1])

theorem secVal_pow {ϖ : Lˣ} (hU : IsUnramInv (ϖ : L) σ q) (χ : Lˣ →* ℂˣ) (s : ℂ) (k : ℕ) :
    secVal q χ (s + (n : ℂ) / 2) (ϖ ^ k) = varX q n (χ ϖ) s ^ k := by
  have h := P.fSatake_ord_zpow hU.2.2.2.1 (k : ℤ)
  rw [zpow_natCast] at h
  rw [secVal, Units.val_pow_eq_pow_val, h, map_pow, Units.val_pow_eq_pow_val, varX, mul_pow, ← Complex.cpow_nat_mul]
  congr 2
  push_cast
  ring

theorem section_eq (hC : Completion) {ϖ : Lˣ} (hU : IsUnramInv (ϖ : L) σ q) {χ : Lˣ →* ℂˣ} (hχ : IsUnr χ) {s : ℂ}
    {Φ : GD σ n → ℂ} (hΦ : IsSphSec σ q n χ s Φ) (g : GU σ n) {l : ℕ} (h : HasLen (mat g) l) :
    Φ (io1 σ n g) = varX q n (χ ϖ) s ^ l := by
  obtain ⟨U, V, C, hfr, hdet⟩ := h
  obtain ⟨k, hk, hk', hx⟩ := hC L ϖ σ q n hU g U V C hfr
  have hq : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  have hK : (⟨k, hk⟩ : GD σ n) ∈ KD σ n := ⟨hk, hk'⟩
  have hp : ∀ x : Fin n → L, ((GD σ n).subtype (io1 σ n g * ⟨k, hk⟩)).1 *ᵥ pairVec finSumFinEquiv x x =
      pairVec finSumFinEquiv ((mat g * C) *ᵥ x) ((mat g * C) *ᵥ x) := fun x => by
    change (blkMat finSumFinEquiv (mat g) 1 * k.1) *ᵥ _ = _
    rw [← mulVec_mulVec, hx, blkMat_mulVec, mulVec_mulVec, one_mulVec]
  have hP : io1 σ n g * ⟨k, hk⟩ ∈ PD σ n := mem_siegelOf.2 (keepsDiag_of_mulVec fun w hw => by
    obtain ⟨x, rfl⟩ := (mem_diagSub _).1 hw
    rw [hp, pairVec_mem_diagSub])
  have hlev : leviMat finSumFinEquiv ((GD σ n).subtype (io1 σ n g * ⟨k, hk⟩)).1 = mat g * C := by
    refine Matrix.ext_of_mulVec_single fun j => funext fun i => ?_
    have := congrFun ((mem_siegelOf.1 hP).mulVec_diag (Pi.single j 1)) (finSumFinEquiv (.inl i))
    rw [hp, pairVec_inl, pairVec_inl] at this
    exact this.symm
  have h1 := hΦ ⟨_, hP⟩ _ (inv_mem hK)
  rw [mul_inv_cancel_right] at h1
  have h2 : Valued.v ((aD σ n ⟨_, hP⟩ * (ϖ ^ l)⁻¹ : Lˣ) : L) = 1 := by
    have hϖ : Valued.v (ϖ : L) = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
    rw [Units.val_mul, val_aOf, hlev, det_mul, map_mul, map_mul, v_det_mat hU.2.1, hdet, one_mul,
      Units.val_inv_eq_inv_val, map_inv₀, Units.val_pow_eq_pow_val, map_pow, hϖ, ← WithZero.exp_nsmul,
      ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  rw [h1, ← inv_mul_cancel_right (aD σ n ⟨_, hP⟩) (ϖ ^ l), secVal_mul hq, secVal_unit q hχ _ h2, one_mul, secVal_pow hU]

theorem closedForm_eq {q : ℕ} (hq : q ≠ 0) (n m : ℕ) (ε s : ℂ) (α : Fin (n / 2) → ℂˣ) (hε : ε = (-1) ^ m) :
    closedForm q n (varX q n ε s) (varY q ε s) α = stdL q n α ε (s + 1 / 2) / dFac q n m s := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have h1 : ε * ((q ^ 2 : ℕ) : ℂ) ^ (-(s + 1 / 2)) = varY q ε s := by
    rw [varY, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
    congr 2
    push_cast
    ring
  have h2 : (dFac q n m s)⁻¹ = ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * varX q n ε s) := by
    rw [dFac, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [etaL, inv_inv, varX, hε, show -(2 * s + n - j) = (j : ℂ) + -(2 * s + n) by ring, Complex.cpow_add _ _ hq0,
      Complex.cpow_natCast, neg_pow (q : ℂ), pow_add]
    ring
  rw [div_eq_mul_inv, h2, stdL, h1, closedForm, GlobalTheory.LGrp.bcParam, GlobalTheory.LFun.eulerFac_add, GlobalTheory.LFun.eulerFac_add,
    GlobalTheory.LFun.eulerFac_map, GlobalTheory.LFun.eulerFac_map, Finset.prod_mul_distrib]
  simp only [Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm (varY q ε s)]
  rcases Nat.even_or_odd n with h | h
  · rw [if_neg (Nat.not_odd_iff_even.2 h), Nat.even_iff.1 h]
    simp only [Multiset.replicate_zero, GlobalTheory.LFun.eulerFac_zero]
    ring
  · rw [if_pos h, Nat.odd_iff.1 h]
    simp only [Multiset.replicate_one, GlobalTheory.LFun.eulerFac_singleton, Units.val_one, one_mul]
    ring

theorem unramDoublingInert : UnramDoublingInert := by
  intro L _ _ _ ϖ σ q n hU _ _ μ _ hμ χ hχ s Φ hΦ α w hw
  have hq : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hF : FracExists := GlobalTheory.T.fraction_exists_of_smith GlobalTheory.T.smith_normal_form_exists
  have hsec : (fun g => Φ (io1 σ n g) * w g) = fun g => varX q n (χ ϖ) s ^ len (mat g) * w g := funext fun g => by
    rw [section_eq GlobalTheory.T.completion_exists hU hχ hΦ g (hF L ϖ n hU.2.2.2.1 _ (det_mat_ne_zero g))]
  have hint : ∀ Z, HasSum (fun x : GU σ n ⧸ KU σ n => varX q n (χ ϖ) s ^ len (mat x.out) * w x.out) Z →
      Integrable (fun g => Φ (io1 σ n g) * w g) μ ∧ ∫ g, Φ (io1 σ n g) * w g ∂μ = Z := fun Z hZ => by
    rw [hsec]
    refine GlobalTheory.T.cosetIntegral' _ μ (KU σ n) (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU).1 hμ _ Z (fun g k hk => ?_) hZ
    have h1 := hw.1 1 ⟨k, hk⟩ g
    have h2 := len_mat_mul (one_mem _) hk g
    simp only [OneMemClass.coe_one, one_mul] at h1 h2
    rw [h1, h2]
  refine ⟨fun hD => ?_, fun hn => hint 1 (hasSum_small GlobalTheory.T.small_rank_bound hU hn (fun g => varX q n (χ ϖ) s ^ len (mat g) * w g)
    fun k hk => ?_)⟩
  · obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExistsU L ϖ σ q n (n / 2) hU (by omega) (by omega) (fun i => (α i : ℂ))
      fun i => (α i).ne_zero
    have h2 := hasSum_spherical hF (GlobalTheory.T.pointwise_of_span_heisenberg GlobalTheory.T.additive_vector_exists GlobalTheory.T.dual_pairing_exists GlobalTheory.T.span_equality GlobalTheory.T.heisenberg_matrix_facts)
      (GlobalTheory.T.count_of_heisenberg_index GlobalTheory.T.heisenberg_matrix_facts (GlobalTheory.T.lattice_index_of_smith GlobalTheory.T.smith_normal_form_exists) GlobalTheory.T.trace_index_formula) (GlobalTheory.T.small_corner_of_heisenberg_dual GlobalTheory.T.heisenberg_matrix_facts GlobalTheory.T.dual_pairing_exists) GlobalTheory.T.generating_function_identity (GlobalTheory.T.coset_surjective_of_levi GlobalTheory.T.levi_decomposition_exists)
      GlobalTheory.T.coset_injective GlobalTheory.T.levi_decomposition_exists (GlobalTheory.T.spherical_transitive_of_levi GlobalTheory.T.levi_decomposition_exists) GlobalTheory.T.small_rank_bound GlobalTheory.T.recursion_identity hU (n / 2) n (by omega) (by omega)
      (fun i => (α i : ℂ)) (varX q n (χ ϖ) s) (varY q (χ ϖ) s) φ (fun i => (α i).ne_zero) (by
        rw [varX, varY, neg_add, neg_add, Complex.cpow_add _ _ hq0, Complex.cpow_add _ _ hq0, Complex.cpow_neg_one,
          Complex.cpow_neg _ (n : ℂ), Complex.cpow_natCast]
        field_simp) hD.1 hD.2 hφ h1
    have h3 := hint _ (GlobalTheory.T.double_coset_swap _ (KU σ n) (P.isCommensurated_integral_unitary_of_unramified hU n) (fun g => varX q n (χ ϖ) s ^ len (mat g)) w φ _
      (fun a b g => by simp only [len_mat_mul a.2 b.2]) hw.1 (fun g => by
        rw [hw.2.2 _ (Final.DosetIndMem _ _ ℂ g), Final.SatakeInert L ϖ σ q n (n / 2) hU (by omega) (by omega) _
          (fun i => (α i).ne_zero) _ (Final.DosetIndMem _ _ ℂ g) φ hφ, Pi.smul_apply, h1, smul_eq_mul, mul_one]) h2)
    exact ⟨h3.1, h3.2, fun m hm => h3.2.trans (closedForm_eq hq n m _ s α hm)⟩
  · have h1 := hw.1 1 ⟨k, hk⟩ 1
    simp only [OneMemClass.coe_one, one_mul] at h1
    rw [len_of_mem hk, h1, hw.2.1, pow_zero, mul_one]

end GlobalTheory.CompanionTheory.InertZetaTop

end
end
