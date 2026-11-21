import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledLatticePrimitiveIsotropicFrameCompletion
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularRowLatticeTriangularBasis
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryHeisenbergRadicalCoordinates
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviRadicalProductLengthOfLatticeSteps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLatticeInverseIndexOfElementaryDivisors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceZeroIntegersModUniformizerCardOfCardSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIntegersModUniformizerEqQSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRadicalCosetCountOfHeisenberg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallerUnitaryGroupEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBlockTriangularLeviPartUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLeviNormalizesUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightInvariantEqSumOpenSubgroupCosetsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BiInvariantReplaceSameDoubleCosetSums

section
section
noncomputable section

open Formalism.UG Matrix

namespace GlobalTheory.InertZeta

theorem elementaryDivisors_exist_discretely_valued : Smith := by
  intro L _ _ ϖ n hϖ g hg
  have hv0 : Valued.v ϖ ≠ 0 := by rw [hϖ]; exact WithZero.exp_ne_zero
  have hϖ0 : ϖ ≠ 0 := fun h => hv0 (by rw [h, map_zero])
  have hnt : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, hv0, by rw [hϖ]; decide⟩
  let A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hA : IsDiscreteValuationRing A := Valuation.valuationSubring_isDiscreteValuationRing _
  have : IsPrincipalIdealRing (intL L) := inferInstanceAs (IsPrincipalIdealRing A)
  let G : GL (Fin n) L := Matrix.nonsingInvUnit g (isUnit_iff_ne_zero.2 hg)
  obtain ⟨c, hc0, hcg, -⟩ := P.glint_exists_denom (n := Fin n) A G
  obtain ⟨d, -, k₁, h₁, k₂, h₂, e⟩ := P.cartan_decomp_gen (intL L) Valued.v (fun _ => Iff.rfl) ϖ hϖ0
    (fun x hx => by
      have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
      refine ⟨-WithZero.log (Valued.v x), ?_⟩
      rw [hϖ, ← WithZero.exp_zsmul]
      simp [WithZero.exp_log hx']) G c hc0 hcg
  refine ⟨d, k₁, (k₁⁻¹ : GL (Fin n) L), k₂, (k₂⁻¹ : GL (Fin n) L), P.cartan_entries_of_mem _ _ h₁,
    P.cartan_entries_of_mem _ _ (inv_mem h₁), P.cartan_entries_of_mem _ _ h₂,
    P.cartan_entries_of_mem _ _ (inv_mem h₂), k₁.inv_mul, k₂.mul_inv, ?_⟩
  exact e

end GlobalTheory.InertZeta

end
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementaryDivisors_exist_discretelyValued : Smith := by
  atlas_forward_decl GlobalTheory.InertZeta.elementaryDivisors_exist_discretely_valued
end

section
section
open GlobalTheory.InertZeta

noncomputable section
open Matrix Formalism.UG

namespace GlobalTheory.InertZeta

theorem prod_exp_eq {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, WithZero.exp (f i) = WithZero.exp (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, WithZero.exp_add]

theorem isInt_diagonal {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {f : Fin n → L}
    (hf : ∀ i, f i ∈ intL L) : IsInt (Matrix.diagonal f) := fun i j => by
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · subst h; exact hf i
  · exact zero_mem _

theorem hasLen_diagonal_zpow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {ϖ : L}
    (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (d : Fin n → ℤ) :
    HasLen (Matrix.diagonal (fun i => ϖ ^ d i)) (∑ i, (-d i).toNat) := by
  have h0 : ϖ ≠ 0 := fun h => by rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hpow : ∀ m : ℕ, ϖ ^ m ∈ intL L := fun m => by
    show Valued.v (ϖ ^ m) ≤ 1
    rw [map_pow, hϖ]
    exact pow_le_one' (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num) m
  refine ⟨Matrix.diagonal (fun i => if 0 ≤ d i then 1 else 0), Matrix.diagonal (fun i => if 0 ≤ d i then 0 else 1),
    Matrix.diagonal (fun i => ϖ ^ (-d i).toNat), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact isInt_diagonal fun i => by split_ifs <;> first | exact one_mem _ | exact zero_mem _
  · exact isInt_diagonal fun i => by split_ifs <;> first | exact one_mem _ | exact zero_mem _
  · exact isInt_diagonal fun i => hpow _
  · rw [Matrix.diagonal_mul_diagonal]
    refine isInt_diagonal fun i => ?_
    have : ϖ ^ d i * ϖ ^ (-d i).toNat = ϖ ^ (d i).toNat := by
      rw [← zpow_natCast, ← zpow_add₀ h0, ← zpow_natCast]
      congr 1
      omega
    rw [this]; exact hpow _
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h : 0 ≤ d i
    · simp [h, Int.toNat_eq_zero.2 (by omega : -d i ≤ 0)]
    · simp only [h, if_false, zero_mul, zero_add, one_mul]
      rw [← zpow_natCast, ← zpow_add₀ h0]
      rw [show d i + (((-d i).toNat : ℕ) : ℤ) = 0 by omega, zpow_zero]
  · rw [Matrix.det_diagonal, map_prod]
    simp only [map_pow, hϖ]
    rw [Finset.prod_congr rfl (fun i _ => (WithZero.exp_nsmul _ _).symm), prod_exp_eq]
    congr 1
    push_cast
    simp

theorem fracExists_of_smith : Smith → FracExists := by
  intro hS L _ _ ϖ n hϖ g hg
  obtain ⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, rfl⟩ := hS L ϖ n hϖ g hg
  have h := (hasLen_diagonal_zpow hϖ d).mul_mul ha ha' hb hb' ea eb
  rw [h.len_eq]
  exact h

end GlobalTheory.InertZeta
end
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixLengthExists_of_elementaryDivisors : Smith → FracExists := by
  atlas_forward_decl GlobalTheory.InertZeta.fracExists_of_smith
end

section
section
noncomputable section

open Matrix

namespace GlobalTheory.InertZeta

theorem smul_mem_integral_submodule_of_valuation_le_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    {P : Submodule (Formalism.UG.intL L) (Fin n → L)} {x : L} (hx : Valued.v x ≤ 1) {w : Fin n → L} (hw : w ∈ P) :
    x • w ∈ P :=
  P.smul_mem (⟨x, hx⟩ : Formalism.UG.intL L) hw

theorem addVec : AddVec := by
  intro L _ _ n M k ρ e hM hρ he
  rcases he with rfl | ⟨i₀, hi₀⟩
  · refine ⟨M, by simpa using hM, ?_⟩
    refine sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 (mem_rowLat.2 ⟨ρ, fun i => ?_, rfl⟩))
    exact (by simpa using hρ i : Valued.v (ρ i) ≤ 1)
  · have h0 : ρ i₀ ≠ 0 := fun h => by rw [h, map_zero] at hi₀; exact WithZero.exp_ne_zero hi₀.symm
    refine ⟨M.updateRow i₀ (ρ ᵥ* M), ?_, ?_⟩
    · rw [Matrix.vecMul_eq_sum, Matrix.det_updateRow_sum, smul_eq_mul, map_mul, hi₀, hM, ← WithZero.exp_add, add_comm]
    · apply le_antisymm
      · refine sup_le (rowLat_le.2 fun i => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
        · by_cases hi : i = i₀
          · subst hi
            have hs : ρ ᵥ* M = ρ i • M i + ∑ j ∈ Finset.univ.erase i, ρ j • M j := by
              rw [Matrix.vecMul_eq_sum]; exact (Finset.add_sum_erase _ (fun j => ρ j • M j) (Finset.mem_univ _)).symm
            have : M i = (ρ i)⁻¹ • (M.updateRow i (ρ ᵥ* M)) i -
                ∑ j ∈ Finset.univ.erase i, ((ρ i)⁻¹ * ρ j) • (M.updateRow i (ρ ᵥ* M)) j := by
              rw [Matrix.updateRow_self, hs, smul_add, smul_smul, inv_mul_cancel₀ h0, one_smul, Finset.smul_sum]
              rw [add_sub_assoc, ← Finset.sum_sub_distrib]
              rw [Finset.sum_eq_zero, add_zero]
              intro j hj
              rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hj), smul_smul, sub_self]
            rw [this]
            have hv : Valued.v (ρ i)⁻¹ = WithZero.exp (-(e : ℤ)) := by rw [map_inv₀, hi₀, WithZero.exp_neg]
            refine Submodule.sub_mem _ (smul_mem_integral_submodule_of_valuation_le_one ?_ (row_mem_rowLat _ _)) (Submodule.sum_mem _ fun j _ => smul_mem_integral_submodule_of_valuation_le_one ?_ (row_mem_rowLat _ _))
            · rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
            · rw [map_mul, hv]
              calc WithZero.exp (-(e : ℤ)) * Valued.v (ρ j) ≤ WithZero.exp (-(e : ℤ)) * WithZero.exp (e : ℤ) :=
                    mul_le_mul' le_rfl (hρ j)
                _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
          · have := row_mem_rowLat (M.updateRow i₀ (ρ ᵥ* M)) i
            rwa [Matrix.updateRow_ne hi] at this
        · have := row_mem_rowLat (M.updateRow i₀ (ρ ᵥ* M)) i₀
          rwa [Matrix.updateRow_self] at this
      · refine rowLat_le.2 fun i => ?_
        by_cases hi : i = i₀
        · subst hi
          rw [Matrix.updateRow_self]
          exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
        · rw [Matrix.updateRow_ne hi]
          exact Submodule.mem_sup_left (row_mem_rowLat _ _)

end GlobalTheory.InertZeta
end
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_add_vector_det_valuation : AddVec := by
  atlas_forward_decl GlobalTheory.InertZeta.addVec
end

section
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta.DualLat

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}

def tw (σ : L →+* L) (x : Fin N → L) : Fin N → L := fun j => σ (x j.rev)

def IntT (t : L) (x : Fin N → L) : Prop := ∀ i, t * x i ∈ intL L

theorem IntT.add {t : L} {x y : Fin N → L} (hx : IntT t x) (hy : IntT t y) : IntT t (x + y) := fun i => by
  simp only [Pi.add_apply, mul_add]; exact add_mem (hx i) (hy i)

theorem IntT.neg {t : L} {x : Fin N → L} (hx : IntT t x) : IntT t (-x) := fun i => by
  simp only [Pi.neg_apply, mul_neg]; exact neg_mem (hx i)

theorem IntT.sub {t : L} {x y : Fin N → L} (hx : IntT t x) (hy : IntT t y) : IntT t (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem IntT.mulVec {t : L} {M : Matrix (Fin N) (Fin N) L} {x : Fin N → L} (hM : IsInt M) (hx : IntT t x) :
    IntT t (M *ᵥ x) := fun i => by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Subring.sum_mem _ fun k _ => by
    rw [mul_left_comm]; exact mul_mem (hM i k) (hx k)

theorem IntT.vecMul {t : L} {M : Matrix (Fin N) (Fin N) L} {x : Fin N → L} (hx : IntT t x) (hM : IsInt M) :
    IntT t (x ᵥ* M) := fun j => by
  simp only [Matrix.vecMul, dotProduct, Finset.mul_sum]
  exact Subring.sum_mem _ fun k _ => by
    rw [← mul_assoc]; exact mul_mem (hx k) (hM k j)

theorem IntT.twist {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {t : L} {x : Fin N → L} (hx : IntT t x) :
    IntT t (tw σ x) := fun j => by
  show Valued.v (t * σ (x j.rev)) ≤ 1
  rw [map_mul, hσ, ← map_mul]; exact hx j.rev

theorem tw_tw {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) (x : Fin N → L) : tw σ (tw σ x) = x := by
  ext j; simp [tw, hσσ]

theorem tw_add (σ : L →+* L) (x y : Fin N → L) : tw σ (x + y) = tw σ x + tw σ y := by
  ext j; simp [tw]

theorem tw_neg (σ : L →+* L) (x : Fin N → L) : tw σ (-x) = -tw σ x := by
  ext j; simp [tw]

theorem tw_vecMul {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) (g : GU σ N) (x : Fin N → L) :
    tw σ x ᵥ* mat g = tw σ (mat g⁻¹ *ᵥ x) := by
  ext j
  simp only [tw, Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, map_mul, mat_inv_apply, hσσ, Fin.rev_rev]
  refine (Equiv.sum_comp Fin.revPerm _).symm.trans ?_
  simp [mul_comm]

end GlobalTheory.InertZeta.DualLat

namespace GlobalTheory.InertZeta

open DualLat

theorem dual_inter_eq_sum : Dual := by
  intro L _ _ ϖ σ q N hU g U V C hF r b t hr
  obtain ⟨hσσ, hσ, -⟩ := hU
  obtain ⟨hUi, hVi, hCi, hgC, e⟩ := hF
  have e' : C * (U + V * mat g) = 1 := mul_eq_one_comm.1 e
  have hr' : r = -tw σ b := by ext j; simp [tw, hr]
  have m1 : C * V * mat g = 1 - C * U := by
    rw [Matrix.mul_assoc, ← e', Matrix.mul_add]; abel
  have m2 : C * V * mat g * mat g⁻¹ = C * V := by rw [Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one]
  have hCU : C * U = 1 - C * V * mat g := by rw [m1]; abel
  have m3 : mat g * C * U * mat g⁻¹ = 1 - mat g * C * V := by
    rw [Matrix.mul_assoc (mat g) C U, hCU]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc, mat_mul_inv]
  change IntT t (r ᵥ* C) ↔ IntT t ((C * V * mat g) *ᵥ b) ∧ IntT t ((mat g * C * U) *ᵥ b)
  constructor
  · intro hρ
    have h1 : r = (r ᵥ* C) ᵥ* U + ((r ᵥ* C) ᵥ* V) ᵥ* mat g := by
      rw [Matrix.vecMul_vecMul (r ᵥ* C) V, ← Matrix.vecMul_add, Matrix.vecMul_vecMul, e', Matrix.vecMul_one]
    have hl₁ : IntT t (-tw σ ((r ᵥ* C) ᵥ* U)) := ((hρ.vecMul hUi).twist hσ).neg
    have hl₂ : IntT t (-tw σ ((r ᵥ* C) ᵥ* V)) := ((hρ.vecMul hVi).twist hσ).neg
    have htw : tw σ (-tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V)) = -r := by
      rw [tw_add, ← tw_vecMul hσσ, tw_neg, tw_neg, tw_tw hσσ, tw_tw hσσ, Matrix.neg_vecMul]
      conv_rhs => rw [h1]
      abel
    have hb : b = -tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V) := by
      calc b = tw σ (tw σ b) := (tw_tw hσσ b).symm
        _ = tw σ (tw σ (-tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V))) := by
          rw [htw, hr', neg_neg]
        _ = _ := tw_tw hσσ _
    rw [hb]
    constructor
    · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, m2, m1, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact (hl₁.sub (IntT.mulVec (hCi.mul hUi) hl₁)).add (IntT.mulVec (hCi.mul hVi) hl₂)
    · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, m3, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact (IntT.mulVec (hgC.mul hUi) hl₁).add (hl₂.sub (IntT.mulVec (hgC.mul hVi) hl₂))
  · rintro ⟨h1, h2⟩
    have hb : b = (C * V * mat g) *ᵥ b + (C * U) *ᵥ b := by
      rw [← Matrix.add_mulVec, m1, sub_add_cancel, Matrix.one_mulVec]
    have key : ∀ b₁ b₂ : Fin N → L,
        -tw σ (b₁ + b₂) ᵥ* C = -(tw σ b₁ ᵥ* C) - tw σ (mat g *ᵥ b₂) ᵥ* (mat g * C) := by
      intro b₁ b₂
      rw [← Matrix.vecMul_vecMul, tw_vecMul hσσ, Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec, tw_add,
        Matrix.neg_vecMul, Matrix.add_vecMul]
      abel
    have h2' : IntT t (mat g *ᵥ ((C * U) *ᵥ b)) := by
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]; exact h2
    rw [hr', hb, key]
    exact ((h1.twist hσ).vecMul hCi).neg.sub ((h2'.twist hσ).vecMul hgC)

end GlobalTheory.InertZeta

end
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_inter_eq_sum' : Dual := by
  atlas_forward_decl GlobalTheory.InertZeta.dual_inter_eq_sum
end

section
section
noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem traceIndex : TraceIndex := by
  intro L _ _ ϖ σ q f hU
  have hq := traceZeroIndex_of_intIndex intIndex L ϖ σ q hU
  obtain ⟨-, -, hϖ, h4, -, -, -⟩ := hU
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h4
    exact WithZero.zero_ne_coe h4
  have hϖO : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [h4, ← WithZero.coe_one, WithZero.coe_le_coe]
    show (-1 : ℤ) ≤ 0
    omega
  set T := (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker with hT
  have memT : ∀ y, y ∈ T ↔ y ∈ intL L ∧ σ y + y = 0 := fun y => Iff.rfl
  have hinj : ∀ e : ℕ, Function.Injective (AddMonoidHom.mulLeft (ϖ ^ e)) := fun e =>
    mul_right_injective₀ (pow_ne_zero e h0)
  have hmap : ∀ e : ℕ, (traceZero σ (ϖ ^ e)).map (AddMonoidHom.mulLeft (ϖ ^ e)) = T := fun e => by
    ext x
    rw [AddSubgroup.mem_map, memT]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_traceZero] at hy
      refine ⟨hy.1, ?_⟩
      rw [AddMonoidHom.coe_mulLeft, map_mul, map_pow, hϖ]
      linear_combination ϖ ^ e * hy.2
    · rintro ⟨hx, hx0⟩
      refine ⟨(ϖ ^ e)⁻¹ * x, ?_, ?_⟩
      · rw [mem_traceZero, mul_inv_cancel_left₀ (pow_ne_zero e h0)]
        refine ⟨hx, ?_⟩
        rw [map_mul, map_inv₀, map_pow, hϖ]
        linear_combination (ϖ ^ e)⁻¹ * hx0
      · rw [AddMonoidHom.coe_mulLeft, mul_inv_cancel_left₀ (pow_ne_zero e h0)]
  have h1 : traceZero σ 1 = T := by
    ext x
    rw [mem_traceZero, memT, one_mul]
  have hmulle : ∀ e : ℕ, T.map (AddMonoidHom.mulLeft (ϖ ^ e)) ≤ T := by
    rintro e _ ⟨y, hy, rfl⟩
    have hy : y ∈ T := hy
    rw [memT] at hy ⊢
    refine ⟨(intL L).mul_mem (pow_mem hϖO e) hy.1, ?_⟩
    rw [AddMonoidHom.coe_mulLeft, map_mul, map_pow, hϖ]
    linear_combination ϖ ^ e * hy.2
  rw [← AddSubgroup.relIndex_map_map_of_injective (traceZero σ 1) (traceZero σ (ϖ ^ f)) (hinj f), hmap f, h1]
  induction f with
  | zero =>
    have : T.map (AddMonoidHom.mulLeft (ϖ ^ 0)) = T := by
      ext x
      simp [AddSubgroup.mem_map]
    rw [this]
    simp
  | succ e ih =>
    have hcomp : T.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1))) =
        (T.map (AddMonoidHom.mulLeft ϖ)).map (AddMonoidHom.mulLeft (ϖ ^ e)) := by
      ext x
      simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨o, ho, rfl⟩
        exact ⟨ϖ * o, ⟨o, ho, rfl⟩, by rw [pow_succ, mul_assoc]⟩
      · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
        exact ⟨o, ho, by rw [pow_succ, mul_assoc]⟩
    have hstep : (T.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1)))).relIndex
        (T.map (AddMonoidHom.mulLeft (ϖ ^ e))) = q := by
      rw [hcomp, AddSubgroup.relIndex_map_map_of_injective _ _ (hinj e)]
      exact hq
    have hle1 : T.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1))) ≤ T.map (AddMonoidHom.mulLeft (ϖ ^ e)) := by
      rw [hcomp]
      exact AddSubgroup.map_mono (by simpa using hmulle 1)
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 (hmulle e), hstep, ih]
    exact (pow_succ' _ _).symm

end GlobalTheory.InertZeta

end
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceZero_integers_index_in_uniformizer_multiples : TraceIndex := by
  atlas_forward_decl GlobalTheory.InertZeta.traceIndex
end

section
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

section Herm

variable {L : Type} [Field L] {N : ℕ}

def hermJ (σ : L →+* L) (x y : Fin N → L) : L := ∑ i, σ (x i) * y i.rev

theorem hermJ_add_left (σ : L →+* L) (x x' y : Fin N → L) :
    hermJ σ (x + x') y = hermJ σ x y + hermJ σ x' y := by
  simp only [hermJ, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hermJ_add_right (σ : L →+* L) (x y y' : Fin N → L) :
    hermJ σ x (y + y') = hermJ σ x y + hermJ σ x y' := by
  simp only [hermJ, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem map_hermJ {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) (x y : Fin N → L) :
    σ (hermJ σ x y) = hermJ σ y x := by
  simp only [hermJ, map_sum, map_mul, hσσ]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, mul_comm]

theorem dotProduct_eq_neg_hermJ {σ : L →+* L} (r b w : Fin N → L) (h : ∀ j, r j = -σ (b j.rev)) :
    r ⬝ᵥ w = -hermJ σ b w := by
  rw [hermJ, ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, h, neg_mul]

end Herm

section Unitary

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem hermJ_mulVec (g : GU σ N) (x y : Fin N → L) :
    hermJ σ (mat g *ᵥ x) (mat g *ᵥ y) = hermJ σ x y := by
  have hconj : ∀ i k : Fin N, σ (mat g i k) = mat g⁻¹ k.rev i.rev := fun i k => by
    rw [mat_inv_apply, Fin.rev_rev, Fin.rev_rev]
  have hinner : ∀ k l : Fin N, ∑ i : Fin N, mat g⁻¹ k.rev i.rev * mat g i.rev l = (1 : Matrix (Fin N) (Fin N) L) k.rev l := by
    intro k l
    rw [← mat_inv_mul g, Matrix.mul_apply]
    exact Fintype.sum_equiv Fin.revPerm _ _ fun i => rfl
  calc hermJ σ (mat g *ᵥ x) (mat g *ᵥ y)
      = ∑ k : Fin N, ∑ l : Fin N, σ (x k) * y l * ∑ i : Fin N, mat g⁻¹ k.rev i.rev * mat g i.rev l := by
        simp only [hermJ, Matrix.mulVec, dotProduct, map_sum, map_mul, hconj, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ k : Fin N, σ (x k) * y k.rev := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hinner, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
          if_true]

theorem sigma_mem_intL {x : L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (h : x ∈ intL L) : σ x ∈ intL L := by
  change Valued.v (σ x) ≤ 1
  rw [hσ]
  exact h

theorem hermJ_int {ϖ : L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (hϖ : σ ϖ = ϖ) (e : ℕ) (x : Fin N → L)
    (h : ∀ i, ϖ ^ e * x i ∈ intL L) : ϖ ^ (2 * e) * hermJ σ x x ∈ intL L := by
  have hsum : ϖ ^ (2 * e) * hermJ σ x x = ∑ i, σ (ϖ ^ e * x i) * (ϖ ^ e * x i.rev) := by
    simp only [hermJ, Finset.mul_sum, map_mul, map_pow, hϖ]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (sigma_mem_intL hσ (h i)) (h i.rev)

end Unitary

theorem smallCorner_of_heis_dual : Heis → Dual → SmallCorner := by
  intro hH hD
  unfold SmallCorner
  intro L _ _ ϖ σ q N hU g₀ U V C hF e f r hef hr
  have hU' := hU
  unfold IsUnramInv at hU'
  obtain ⟨hσσ, hσv, hϖσ, hϖv, -⟩ := hU'

  obtain ⟨b, hb⟩ : ∃ b : Fin N → L, b = fun i => -σ (r i.rev) := ⟨_, rfl⟩
  have hrb : ∀ j, r j = -σ (b j.rev) := fun j => by
    rw [hb]
    simp only [Fin.rev_rev, map_neg, hσσ, neg_neg]
  obtain ⟨b₁, hb₁⟩ : ∃ x : Fin N → L, x = (C * V * mat g₀) *ᵥ b := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ x : Fin N → L, x = (C * U) *ᵥ b := ⟨_, rfl⟩
  have hsplit : b₁ + b₂ = b := by
    have hCinv : C * (U + V * mat g₀) = 1 := mul_eq_one_comm.mp hF.2.2.2.2
    rw [hb₁, hb₂, ← Matrix.add_mulVec, add_comm, Matrix.mul_assoc, ← Matrix.mul_add, hCinv,
      Matrix.one_mulVec]
  obtain ⟨τ, hτint, hτ⟩ := exists_trace_one hU
  obtain ⟨s, hs⟩ : ∃ s : L, s = hermJ σ b₁ b₁ - hermJ σ b₂ b₂ := ⟨_, rfl⟩
  have hσs : σ s = s := by rw [hs, map_sub, map_hermJ hσσ, map_hermJ hσσ]
  have hrb₁ : r ⬝ᵥ b₁ = -hermJ σ b b₁ := dotProduct_eq_neg_hermJ r b b₁ hrb
  have hnorm : -∑ j, r j * σ (r j.rev) = -hermJ σ b b := by
    rw [← dotProduct_eq_neg_hermJ r b b hrb, hb]
    simp only [dotProduct, mul_neg, Finset.sum_neg_distrib]
  have hc : r ⬝ᵥ b₁ + τ * s + σ (r ⬝ᵥ b₁ + τ * s) = -∑ j, r j * σ (r j.rev) := by
    rw [hnorm, hrb₁, map_add, map_mul, map_neg, map_hermJ hσσ, hσs, ← hsplit]
    simp only [hermJ_add_left, hermJ_add_right]
    linear_combination s * hτ + hs
  obtain ⟨hHrad, -, hHex⟩ := hH L ϖ σ q N hU
  obtain ⟨u, hu, hur, huc⟩ := hHex r (r ⬝ᵥ b₁ + τ * s) hc
  have hcol : colOf u = b := by
    funext i
    have hi := (hHrad u hu).1 i.rev
    rw [hur, Fin.rev_rev] at hi
    rw [hb]
    simp only [hi, map_neg, hσσ, neg_neg]
  obtain ⟨h₁, h₂⟩ := (hD L ϖ σ q N hU g₀ U V C hF r b (ϖ ^ e) hrb).1 hr
  refine ⟨u, hu, hur, ?_, ?_⟩
  · rw [hur]
    exact hr
  · rw [hur, hcol, huc, ← hb₁, add_sub_cancel_left]
    have hϖint : ϖ ∈ intL L := by
      change Valued.v ϖ ≤ 1
      rw [hϖv]
      exact WithZero.coe_le_one.mpr (by decide)
    have i₁ : ϖ ^ (2 * e) * hermJ σ b₁ b₁ ∈ intL L :=
      hermJ_int hσv hϖσ e b₁ (by rw [hb₁]; exact h₁)
    have hg : mat g₀ *ᵥ b₂ = (mat g₀ * C * U) *ᵥ b := by
      rw [hb₂, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have i₂ : ϖ ^ (2 * e) * hermJ σ b₂ b₂ ∈ intL L := by
      rw [← hermJ_mulVec g₀ b₂ b₂, hg]
      exact hermJ_int hσv hϖσ e _ h₂
    have hf : ϖ ^ f = ϖ ^ (f - 2 * e) * ϖ ^ (2 * e) := by rw [← pow_add, Nat.sub_add_cancel hef]
    have hsplit' : ϖ ^ f * (τ * s) =
        τ * ϖ ^ (f - 2 * e) * (ϖ ^ (2 * e) * hermJ σ b₁ b₁ - ϖ ^ (2 * e) * hermJ σ b₂ b₂) := by
      rw [hf, hs]
      ring
    rw [hsplit']
    exact Subring.mul_mem _ (Subring.mul_mem _ hτint (Subring.pow_mem _ hϖint _)) (Subring.sub_mem _ i₁ i₂)

end GlobalTheory.InertZeta
end
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_corner_of_heisenberg_duality : Heis → Dual → SmallCorner := by
  atlas_forward_decl GlobalTheory.InertZeta.smallCorner_of_heis_dual
end

section
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem _root_.GlobalTheory.InertZeta.leviExists : _root_.GlobalTheory.InertZeta.LeviExists := by
  intro L _ _ ϖ σ q N hq a g₀
  obtain ⟨-, -, hσϖ, hv, -⟩ := hq
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    simp at hv
  obtain ⟨ι, hι⟩ := _root_.GlobalTheory.SatakeWeyl.embExists L σ (N + 2) N _root_.GlobalTheory.InertZeta.mid
    _root_.GlobalTheory.InertZeta.mid_injective _root_.GlobalTheory.InertZeta.mid_rev
  obtain ⟨h1, h2⟩ := hι g₀
  set d : Fin (N + 2) → L := fun i => if i = 0 then ϖ ^ a else if i = Fin.last (N + 1) then ϖ ^ (-a) else 1
  have hd : ∀ i, σ (d i) * d i.rev = 1 := by
    intro i
    rcases _root_.GlobalTheory.InertZeta.idx_cases i with rfl | ⟨k, rfl⟩ | rfl
    · simp [d, _root_.GlobalTheory.InertZeta.last_ne_zero, map_zpow₀, hσϖ, mul_inv_cancel₀ (zpow_ne_zero a hϖ)]
    · simp [d, ← _root_.GlobalTheory.InertZeta.mid_rev, _root_.GlobalTheory.InertZeta.mid_ne_zero,
        _root_.GlobalTheory.InertZeta.mid_ne_last]
    · simp [d, _root_.GlobalTheory.InertZeta.last_ne_zero, map_zpow₀, hσϖ, inv_mul_cancel₀ (zpow_ne_zero a hϖ)]
  obtain ⟨D, hD⟩ := _root_.GlobalTheory.SatakeWeyl.exists_mat (σ := σ) (Matrix.diagonal d) (by
    ext i j
    unfold _root_.Formalism.UG.cT
    rw [Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_diagonal,
      Matrix.diagonal_mul, _root_.Formalism.UG.P.fIwasawa_antiJ]
    split_ifs with h
    · subst h
      simpa using hd i
    · simp)
  have h0 : (0 : Fin (N + 2)) ∉ Set.range _root_.GlobalTheory.InertZeta.mid :=
    fun ⟨k, hk⟩ => _root_.GlobalTheory.InertZeta.mid_ne_zero k hk
  have hl : Fin.last (N + 1) ∉ Set.range _root_.GlobalTheory.InertZeta.mid :=
    fun ⟨k, hk⟩ => _root_.GlobalTheory.InertZeta.mid_ne_last k hk
  have hm : _root_.GlobalTheory.SatakeWeyl.mat (D * ι g₀) =
      Matrix.diagonal d * _root_.GlobalTheory.SatakeWeyl.mat (ι g₀) := by
    rw [← hD]
    rfl
  refine ⟨D * ι g₀, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    rw [hm, Matrix.diagonal_mul]
    have hne : i ≠ j := fun h => hij (h ▸ rfl)
    by_cases hi : i ∈ Set.range _root_.GlobalTheory.InertZeta.mid
    · by_cases hj : j ∈ Set.range _root_.GlobalTheory.InertZeta.mid
      · obtain ⟨k, rfl⟩ := hi
        obtain ⟨l, rfl⟩ := hj
        simp [_root_.GlobalTheory.InertZeta.blk_mid] at hij
      · rw [h2 i j (Or.inr hj), Matrix.one_apply_ne hne, mul_zero]
    · rw [h2 i j (Or.inl hi), Matrix.one_apply_ne hne, mul_zero]
  · rw [hm, Matrix.diagonal_mul, h2 0 0 (Or.inl h0), Matrix.one_apply_eq, mul_one]
    simp [d]
  · rw [hm, Matrix.diagonal_mul, h2 _ _ (Or.inl hl), Matrix.one_apply_eq, mul_one]
    simp [d, _root_.GlobalTheory.InertZeta.last_ne_zero]
  · intro i j
    rw [hm, Matrix.diagonal_mul, h1]
    simp [d, _root_.GlobalTheory.InertZeta.mid_ne_zero, _root_.GlobalTheory.InertZeta.mid_ne_last]

end GlobalTheory.InertZeta
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_block_diagonal_levi_element : LeviExists := by
  atlas_forward_decl GlobalTheory.InertZeta.leviExists
end

section
section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem rev_zero_eq_last {N : ℕ} : (0 : Fin (N + 2)).rev = Fin.last (N + 1) := by ext; simp [Fin.val_rev]

theorem rev_last_eq_zero {N : ℕ} : (Fin.last (N + 1)).rev = (0 : Fin (N + 2)) := by ext; simp [Fin.val_rev]

theorem blk_rev_of_eq {N : ℕ} (a b : Fin (N + 2)) (h : blk N a = blk N b) : blk N a.rev = blk N b.rev := by
  rcases idx_cases a with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases b with rfl | ⟨j, rfl⟩ | rfl <;>
    simp [rev_zero_eq_last, rev_last_eq_zero, ← mid_rev] at h ⊢

theorem lt_of_blk_lt {N : ℕ} {a b : Fin (N + 2)} (h : blk N a < blk N b) : a < b := by
  rcases idx_cases a with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases b with rfl | ⟨j, rfl⟩ | rfl <;>
    simp [Fin.lt_def] at h ⊢

theorem cosetSurj_of_leviExists : LeviExists → CosetSurj := by
  intro _ L _ _ ϖ σ q N hU g
  have hσσ : ∀ x, σ (σ x) = x := hU.1
  have hσv : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  have hσϖ : σ ϖ = ϖ := hU.2.2.1
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  obtain ⟨b, k, hb, hk, rfl⟩ := P.fIwasawa_iwasawa σ hσσ hσv g
  have hbT : (mat b).BlockTriangular (blk N) := fun i j h => hb i j (lt_of_blk_lt h)
  obtain ⟨m', hm'L, hm'e, hu'⟩ := leviPart L σ (N + 2) (blk N) blk_rev_of_eq b hbT
  set M₀ : Matrix (Fin N) (Fin N) L := Matrix.of fun i j => mat m' (mid i) (mid j) with hM₀
  have hM₀U : cT σ M₀ * antiJ L N * M₀ = antiJ L N := by
    have h1 : cT σ (mat m') * antiJ L (N + 2) * mat m' = antiJ L (N + 2) := m'.2
    ext i j
    have h2 := congrFun (congrFun h1 (mid i)) (mid j)
    rw [Matrix.mul_apply, sum_idx] at h2
    have e0 : mat m' 0 (mid j) = 0 := hm'L _ _ (by simp)
    have eL : mat m' (Fin.last (N + 1)) (mid j) = 0 := hm'L _ _ (by simp)
    rw [e0, eL, mul_zero, mul_zero, zero_add, add_zero] at h2
    have hJ : antiJ L (N + 2) (mid i) (mid j) = antiJ L N i j := by
      simp only [antiJ]
      exact if_congr (by simp only [val_mid]; omega) rfl rfl
    rw [hJ] at h2
    rw [← h2, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [P.fSatake_cTJ, P.fSatake_cTJ, ← mid_rev]
    rfl
  obtain ⟨g₀, hg₀⟩ := exists_mat M₀ hM₀U
  obtain ⟨⟨k₀, hk₀⟩, hout⟩ := QuotientGroup.mk_out_eq_mul (KU σ N) g₀
  have hxL : σ (mat m' 0 0) * mat m' (Fin.last (N + 1)) (Fin.last (N + 1)) = 1 := by
    rw [hm'e 0 0 rfl, hm'e _ _ rfl]
    have := P.fSatake_unit_diag hb 0
    rwa [rev_zero_eq_last] at this
  have hx0 : mat m' 0 0 ≠ 0 := by
    intro h; rw [h, map_zero, zero_mul] at hxL; exact zero_ne_one hxL
  have hvx0 : Valued.v (mat m' 0 0) ≠ 0 := by simpa using hx0
  have hvx : Valued.v (mat m' 0 0) = WithZero.exp (-(-(Valued.v (mat m' 0 0)).log)) := by
    rw [neg_neg, WithZero.exp_log hvx0]
  refine ⟨-(Valued.v (mat m' 0 0)).log, (g₀ : GU σ N ⧸ KU σ N), fun m hm => ?_⟩
  obtain ⟨hmL, hm0, hmLL, hmM⟩ := hm
  generalize -(Valued.v (mat m' 0 0)).log = a at hvx hm0 hmLL
  have hmiL : m⁻¹ ∈ leviU σ (blk N) := inv_mem hmL
  have hcL : m⁻¹ * m' ∈ leviU σ (blk N) := mul_mem hmiL hm'L
  have hcK : m⁻¹ * m' ∈ KU σ (N + 2) := by
    rw [mem_KU_iff hσv]
    intro i j
    by_cases hij : blk N i = blk N j
    swap
    · rw [hcL i j hij]; exact zero_mem _
    rw [mat_mul, Matrix.mul_apply, sum_idx]
    rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
      simp at hij
    · rw [Finset.sum_eq_zero (fun l _ => by rw [hmiL 0 (mid l) (by simp), zero_mul]),
        hmiL 0 (Fin.last _) (by simp), zero_mul, add_zero, add_zero, mat_inv_apply, rev_zero_eq_last, hmLL,
        map_zpow₀, hσϖ]
      rw [intL, Valuation.mem_integer_iff]
      rw [map_mul, map_zpow₀, hϖ, hvx, ← WithZero.exp_zsmul, ← WithZero.exp_add,
        show (-a) • (-1 : ℤ) + -a = 0 by rw [smul_eq_mul]; ring, WithZero.exp_zero]
    · rw [hmiL (mid i) 0 (by simp), zero_mul, zero_add, hmiL (mid i) (Fin.last _) (by simp), zero_mul, add_zero]
      have e : ∑ l, mat m⁻¹ (mid i) (mid l) * mat m' (mid l) (mid j) = mat ((g₀ * k₀)⁻¹ * g₀) i j := by
        rw [mat_mul, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [mat_inv_apply, mat_inv_apply, ← mid_rev, ← mid_rev, hmM, hout, hg₀]
        rfl
      rw [e, show (g₀ * k₀)⁻¹ * g₀ = k₀⁻¹ by group]
      exact P.fSatake_K_int (inv_mem hk₀) i j
    · rw [Finset.sum_eq_zero (fun l _ => by rw [hmiL (Fin.last _) (mid l) (by simp), zero_mul]),
        hmiL (Fin.last _) 0 (by simp), zero_mul, zero_add, zero_add, mat_inv_apply, rev_last_eq_zero, hm0,
        map_zpow₀, hσϖ, eq_inv_of_mul_eq_one_right hxL, intL, Valuation.mem_integer_iff, map_mul, map_inv₀, hσv,
        map_zpow₀, hϖ, hvx, ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add,
        show a • (-1 : ℤ) + -(-a) = 0 by rw [smul_eq_mul]; ring, WithZero.exp_zero]
  obtain ⟨hr, -⟩ := leviRad L σ (N + 2) (blk N) hσv (m⁻¹ * m') hcL (m'⁻¹ * b) hu'
  exact ⟨(m⁻¹ * m') * (m'⁻¹ * b) * (m⁻¹ * m')⁻¹, hr, (m⁻¹ * m') * k, mul_mem hcK hk, by group⟩

end GlobalTheory.InertZeta
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryIwasawaCosetSurj_of_leviElementExists : LeviExists → CosetSurj := by
  atlas_forward_decl GlobalTheory.InertZeta.cosetSurj_of_leviExists
end

section
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem blk_eq_zero_iff {l : Fin (N + 2)} : blk N l = 0 ↔ l = 0 := by
  rcases idx_cases l with rfl | ⟨j, rfl⟩ | rfl
  · simp
  · simp [mid_ne_zero]
  · simp [last_ne_zero]

theorem blk_eq_two_iff {l : Fin (N + 2)} : blk N l = 2 ↔ l = Fin.last (N + 1) := by
  rcases idx_cases l with rfl | ⟨j, rfl⟩ | rfl
  · simp [(last_ne_zero (N := N)).symm]
  · simp [mid_ne_last]
  · simp

theorem levi_mul_apply_zero {x : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) (M : Matrix (Fin (N + 2)) (Fin (N + 2)) L)
    (j : Fin (N + 2)) : (mat x * M) 0 j = mat x 0 0 * M 0 j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single 0]
  · intro l _ hl
    rw [hx 0 l (by rw [blk_zero]; exact fun h => hl (blk_eq_zero_iff.1 h.symm)), zero_mul]
  · simp

theorem levi_mul_apply_last {x : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) (M : Matrix (Fin (N + 2)) (Fin (N + 2)) L)
    (j : Fin (N + 2)) : (mat x * M) (Fin.last (N + 1)) j = mat x (Fin.last (N + 1)) (Fin.last (N + 1)) * M (Fin.last (N + 1)) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last (N + 1))]
  · intro l _ hl
    rw [hx _ l (by rw [blk_last]; exact fun h => hl (blk_eq_two_iff.1 h.symm)), zero_mul]
  · simp

theorem levi_mul_apply_mid {x : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) (M : Matrix (Fin (N + 2)) (Fin (N + 2)) L)
    (i j : Fin (N + 2)) (k : Fin N) (hi : i = mid k) :
    (mat x * M) i j = ∑ l, mat x i (mid l) * M (mid l) j := by
  subst hi
  rw [Matrix.mul_apply, sum_idx (fun l => mat x (mid k) l * M l j), hx (mid k) 0 (by simp), hx (mid k) _ (by simp)]
  simp

end

theorem cosetInj : CosetInj := by
  intro L _ _ ϖ σ q N hU a a' g₀ g₀' m m' hm hm' u hu u' hu' hK
  have hσ : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have hϖ0 : ϖ ≠ 0 := fun h => by rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hvz : ∀ k : ℤ, Valued.v (ϖ ^ k) = WithZero.exp (-k) := fun k => by
    rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; simp
  set n := m⁻¹ * m' with hn_def
  have hnL : n ∈ leviU σ (blk N) := mul_mem (inv_mem hm.1) hm'.1
  have hconj : n⁻¹ * u⁻¹ * n⁻¹⁻¹ ∈ radQ σ N :=
    (leviRad L σ (N + 2) (blk N) hσ n⁻¹ (inv_mem hnL) u⁻¹ (inv_mem hu)).1
  have he : (m * u)⁻¹ * (m' * u') = n * ((n⁻¹ * u⁻¹ * n⁻¹⁻¹) * u') := by
    rw [hn_def]; group
  have hnK : n ∈ KU σ (N + 2) :=
    (leviRad L σ (N + 2) (blk N) hσ n hnL _ (mul_mem hconj hu')).2 (he ▸ hK)
  have hint : ∀ i j, mat n i j ∈ intL L := (mem_KU_iff hσ n).1 hnK
  have hmn : mat m * mat n = mat m' := by rw [← mat_mul, hn_def, mul_inv_cancel_left]
  have h0 : ϖ ^ a * mat n 0 0 = ϖ ^ a' := by
    rw [← hm.2.1, ← hm'.2.1, ← hmn, levi_mul_apply_zero hm.1]
  have hl : ϖ ^ (-a) * mat n (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a') := by
    rw [← hm.2.2.1, ← hm'.2.2.1, ← hmn, levi_mul_apply_last hm.1]
  have hv0 := hint 0 0
  have hvl := hint (Fin.last (N + 1)) (Fin.last (N + 1))
  have e0 : mat n 0 0 = ϖ ^ (a' - a) := by
    rw [zpow_sub₀ hϖ0, ← h0]; field_simp
  have el : mat n (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (a - a') := by
    rw [show a - a' = -a' - -a by ring, zpow_sub₀ hϖ0, ← hl]; field_simp
  change Valued.v (mat n 0 0) ≤ 1 at hv0
  change Valued.v (mat n (Fin.last (N + 1)) (Fin.last (N + 1))) ≤ 1 at hvl
  rw [e0, hvz, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv0
  rw [el, hvz, ← WithZero.exp_zero, WithZero.exp_le_exp] at hvl
  refine ⟨by omega, ?_⟩
  rw [mem_KU_iff hσ]
  have hmid : mat g₀ * Matrix.of (fun i j => mat n (mid i) (mid j)) = mat g₀' := by
    ext i j
    rw [← hm'.2.2.2, ← hmn, levi_mul_apply_mid hm.1 _ _ _ i rfl, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [hm.2.2.2]; rfl
  intro i j
  rw [mat_mul, ← hmid, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
  exact hint _ _

end GlobalTheory.InertZeta
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwasawa_cells_disjoint : CosetInj := by
  atlas_forward_decl GlobalTheory.InertZeta.cosetInj
end

section
section
noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem blk_mono {i j : Fin (N + 2)} (h : j ≤ i) : blk N j ≤ blk N i := by
  rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;> simp
  all_goals first
    | (rw [Fin.le_iff_val_le_val] at h; have := i'.2; simp at h; omega)
    | (rw [Fin.le_iff_val_le_val] at h; simp at h; done)
    | (rw [Fin.le_iff_val_le_val] at h; simp at h; omega)

theorem levi_ext {ϖ : L} {a : ℤ} {g₀ : GU σ N} {m m' : GU σ (N + 2)} (h : IsLeviElt ϖ a g₀ m)
    (h' : IsLeviElt ϖ a g₀ m') : m = m' := by
  apply mat_injective
  funext i j
  by_cases hij : blk N i = blk N j
  · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;>
      simp at hij
    · rw [h.2.1, h'.2.1]
    · rw [h.2.2.2 i' j', h'.2.2.2 i' j']
    · rw [h.2.2.1, h'.2.2.1]
  · rw [h.1 i j hij, h'.1 i j hij]

theorem levi_mul {ϖ : L} (hϖ : ϖ ≠ 0) {a a' : ℤ} {g g' : GU σ N} {m m' : GU σ (N + 2)} (h : IsLeviElt ϖ a g m)
    (h' : IsLeviElt ϖ a' g' m') : IsLeviElt ϖ (a + a') (g * g') (m * m') := by
  have e : ∀ i j, mat (m * m') i j = mat m i 0 * mat m' 0 j + ∑ l, mat m i (mid l) * mat m' (mid l) j +
      mat m i (Fin.last (N + 1)) * mat m' (Fin.last (N + 1)) j := fun i j => by
    rw [mat_mul, Matrix.mul_apply, sum_idx (fun l => mat m i l * mat m' l j)]
  have z : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := h.1
  have z' : ∀ i j, blk N i ≠ blk N j → mat m' i j = 0 := h'.1
  refine ⟨mul_mem h.1 h'.1, ?_, ?_, fun i j => ?_⟩
  · rw [e, h.2.1, h'.2.1, z 0 (Fin.last (N + 1)) (by simp), zero_mul, add_zero,
      Finset.sum_eq_zero (fun l _ => by rw [z 0 (mid l) (by simp), zero_mul]), add_zero, zpow_add₀ hϖ]
  · rw [e, h.2.2.1, h'.2.2.1, z (Fin.last (N + 1)) 0 (by simp), zero_mul, zero_add,
      Finset.sum_eq_zero (fun l _ => by rw [z (Fin.last (N + 1)) (mid l) (by simp), zero_mul]), zero_add,
      neg_add, zpow_add₀ hϖ]
  · rw [e, z (mid i) 0 (by simp), z (mid i) (Fin.last (N + 1)) (by simp), zero_mul, zero_mul, zero_add, add_zero,
      mat_mul, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h.2.2.2, h'.2.2.2]

end

theorem sphTrans (hL : LeviExists) : SphTrans := by
  intro L _ _ ϖ σ q N r hU hr α φ φ₀ hα hsph h1 hsph₀ h10 a g₀ m hm u hu
  have hϖ : ϖ ≠ 0 := by
    intro h; have := hU.2.2.2.1; rw [h, Valuation.map_zero] at this; exact WithZero.zero_ne_coe this
  obtain ⟨b₀, k₀, hb₀, hk₀, rfl⟩ := P.fIwasawa_iwasawa σ hU.1 hU.2.1 g₀
  obtain ⟨mb, hmb⟩ := hL L ϖ σ q N hU a b₀
  obtain ⟨mk, hmk⟩ := hL L ϖ σ q N hU 0 k₀
  have hm' : m = mb * mk := by
    have := levi_mul hϖ hmb hmk
    rw [add_zero] at this
    exact levi_ext hm this
  subst hm'

  have hmkK : mk ∈ KU σ (N + 2) := by
    rw [mem_KU_iff hU.2.1]
    intro i j
    by_cases hij : blk N i = blk N j
    · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;>
        simp at hij
      · rw [hmk.2.1, zpow_zero]; exact one_mem _
      · rw [hmk.2.2.2 i' j']; exact P.fSatake_K_int hk₀ i' j'
      · rw [hmk.2.2.1, neg_zero, zpow_zero]; exact one_mem _
    · rw [hmk.1 i j hij]; exact zero_mem _
  set v := mk * u * mk⁻¹ with hv
  have hvR : v ∈ radQ σ N := (leviRad L σ (N + 2) (blk N) hU.2.1 mk hmk.1 u hu).1
  have hdiag : ∀ i j, blk N j ≤ blk N i → mat (mb * v) i j = mat mb i j :=
    fun i j h => levi_mul_rad_apply hmb.1 hvR h
  have hB : IsBorelU (mb * v) := by
    intro i j hji
    show mat (mb * v) i j = 0
    rw [hdiag i j (blk_mono hji.le)]
    by_cases hij : blk N i = blk N j
    · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;>
        simp at hij
      · exact absurd hji (lt_irrefl _)
      · rw [hmb.2.2.2 i' j']
        exact hb₀ i' j' (by rw [Fin.lt_iff_val_lt_val] at hji ⊢; simpa using hji)
      · exact absurd hji (lt_irrefl _)
    · exact hmb.1 i j hij
  have e1 : mb * mk * u = (mb * v) * 1 * mk := by rw [hv]; group
  have hφ : φ (mb * mk * u) = chiDeltaU q α (mb * v) := by
    rw [e1, hsph _ _ _ hB hmkK, h1, mul_one]
  have hφ₀ : φ₀ (b₀ * k₀) = chiDeltaU q (Fin.tail α) b₀ := by
    have := hsph₀ b₀ 1 k₀ hb₀ hk₀
    rwa [mul_one, h10, mul_one] at this
  rw [hφ, hφ₀]
  unfold chiDeltaU
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [dif_pos (by simp)]
    have e0 : (⟨(0 : Fin (r + 1)).val, by simp⟩ : Fin (N + 2)) = 0 := rfl
    rw [e0]
    show α 0 ^ ordL (mat (mb * v) 0 0) * (q : ℂ) ^ (-ordL (mat (mb * v) 0 0) * (((N + 2 : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ))) = _
    rw [hdiag 0 0 le_rfl, hmb.2.1, P.fSatake_ord_zpow hU.2.2.2.1]
    congr 2
    push_cast
    ring
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hiN : i.val < N := by have := i.2; omega
    rw [dif_pos (by simp; omega), dif_pos hiN]
    have ei : (⟨(Fin.succ i).val, by simp; omega⟩ : Fin (N + 2)) = mid ⟨i.val, hiN⟩ := by
      ext; simp
    rw [ei]
    show α i.succ ^ ordL (mat (mb * v) (mid ⟨i.val, hiN⟩) (mid ⟨i.val, hiN⟩)) *
      (q : ℂ) ^ (-ordL (mat (mb * v) (mid ⟨i.val, hiN⟩) (mid ⟨i.val, hiN⟩)) *
        (((N + 2 : ℕ) : ℤ) - 1 - 2 * ((i.succ.val : ℕ) : ℤ))) = _
    rw [hdiag _ _ le_rfl, hmb.2.2.2]
    show _ = Fin.tail α i ^ ordL (mat b₀ ⟨i.val, hiN⟩ ⟨i.val, hiN⟩) *
      (q : ℂ) ^ (-ordL (mat b₀ ⟨i.val, hiN⟩ ⟨i.val, hiN⟩) * ((N : ℤ) - 1 - 2 * ((i.val : ℕ) : ℤ)))
    congr 2
    simp only [Fin.val_succ]
    push_cast
    ring

end GlobalTheory.InertZeta

end
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalInductionTransitivity_of_leviExists : LeviExists → SphTrans := by
  atlas_forward_decl GlobalTheory.InertZeta.sphTrans
end

section
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem smallRank : SmallRank := by
  intro L _ _ ϖ σ q n hU hn g

  set A : Matrix (Fin n) (Fin n) L := ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hAdef
  set B : Matrix (Fin n) (Fin n) L := (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
    with hBdef
  have hAB : A * B = 1 := (g : GL (Fin n) L).mul_inv
  have hBA : B * A = 1 := (g : GL (Fin n) L).inv_mul

  have hherm : (A.map σ)ᵀ * antiJ L n * A = antiJ L n := g.2

  have key : ∀ i j, Valued.v (A i j) = 1 ∧ Valued.v (B i j) = 1 := by
    intro i j
    obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · exact i.elim0
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      have h1 : σ (A 0 0) * A 0 0 = 1 := by
        simpa [Matrix.mul_apply, antiJ] using congrFun (congrFun hherm 0) 0
      have h2 : B 0 0 * A 0 0 = 1 := by
        simpa [Matrix.mul_apply] using congrFun (congrFun hBA 0) 0
      have hsq : Valued.v (A 0 0) * Valued.v (A 0 0) = 1 := by
        have := congrArg Valued.v h1
        rwa [map_mul, map_one, hU.2.1] at this
      have hle : Valued.v (A 0 0) ≤ 1 := by
        by_contra hlt
        have hgt : 1 < Valued.v (A 0 0) := not_le.1 hlt
        have : Valued.v (A 0 0) * 1 ≤ Valued.v (A 0 0) * Valued.v (A 0 0) := by gcongr
        rw [mul_one, hsq] at this
        exact hlt this
      have hA1 : Valued.v (A 0 0) = 1 := by
        refine le_antisymm hle ?_
        have : Valued.v (A 0 0) * Valued.v (A 0 0) ≤ Valued.v (A 0 0) * 1 := by gcongr
        rwa [mul_one, hsq] at this
      refine ⟨hA1, ?_⟩
      have := congrArg Valued.v h2
      rwa [map_mul, map_one, hA1, mul_one] at this
  have hint : ∀ x : L, Valued.v x = 1 → x ∈ intL L := fun x hx => by
    unfold intL
    exact (Valuation.mem_integer_iff _ _).2 hx.le

  let A' : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨A i j, hint _ (key i j).1⟩
  let B' : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨B i j, hint _ (key i j).2⟩
  have hinj : Function.Injective
      ((intL L).subtype.mapMatrix : Matrix (Fin n) (Fin n) (intL L) → Matrix (Fin n) (Fin n) L) :=
    fun X Y h => by
      ext i j
      exact congrFun (congrFun h i) j
  have eA : (intL L).subtype.mapMatrix A' = A := rfl
  have eB : (intL L).subtype.mapMatrix B' = B := rfl
  unfold KU
  rw [Subgroup.mem_subgroupOf]
  unfold intPts
  rw [Subgroup.mem_inf, MonoidHom.mem_range]
  refine ⟨g.2, ⟨A', B', hinj ?_, hinj ?_⟩, ?_⟩
  · rw [map_mul, eA, eB, map_one, hAB]
  · rw [map_mul, eA, eB, map_one, hBA]
  · unfold bc
    exact Units.ext eA

end GlobalTheory.InertZeta

end
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_rank_le_one_integral_points : SmallRank := by
  atlas_forward_decl GlobalTheory.InertZeta.smallRank
end

section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biInvariant_replace_same_double_coset_sums : DosetSwap := by
  first | exact @GlobalTheory.InertZeta.dosetSwap | exact GlobalTheory.InertZeta.dosetSwap | (intros; apply GlobalTheory.InertZeta.dosetSwap <;> assumption)
end

section
section
open GlobalTheory.InertZeta

noncomputable section

namespace GlobalTheory.InertZeta

theorem genFun_counts_hasSum {𝕜 : Type} [NormedField 𝕜] [CompleteSpace 𝕜] (c q N : ℕ) (x : 𝕜)
    (hx : ‖(q : 𝕜) ^ (N + 1) * x‖ < 1) :
    HasSum (fun j : ℕ => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : 𝕜) * x ^ j)
      (c * (1 + q * x) / (1 - ((q : 𝕜) ^ (N + 1) * x) ^ 2)) := by
  set y := (q : 𝕜) ^ (N + 1) * x with hy
  have hy2 : ‖y ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg y]
  have hg := hasSum_geometric_of_norm_lt_one hy2
  have fe : (fun k : ℕ => ((c * q ^ (2 * N * ((2 * k) / 2) + 2 * k) : ℕ) : 𝕜) * x ^ (2 * k)) =
      fun k => (c : 𝕜) * (y ^ 2) ^ k := by
    funext k
    rw [Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
    push_cast
    rw [hy]; ring
  have fo : (fun k : ℕ => ((c * q ^ (2 * N * ((2 * k + 1) / 2) + (2 * k + 1)) : ℕ) : 𝕜) * x ^ (2 * k + 1)) =
      fun k => ((c : 𝕜) * q * x) * (y ^ 2) ^ k := by
    funext k
    rw [show (2 * k + 1) / 2 = k by omega]
    push_cast
    rw [hy]; ring
  have he := hg.mul_left (c : 𝕜)
  have ho := hg.mul_left ((c : 𝕜) * q * x)
  rw [← fe] at he
  rw [← fo] at ho
  have := HasSum.even_add_odd (f := fun j : ℕ => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : 𝕜) * x ^ j) he ho
  rw [show (c : 𝕜) * (1 + q * x) / (1 - y ^ 2) = c * (1 - y ^ 2)⁻¹ + c * q * x * (1 - y ^ 2)⁻¹ by
    rw [div_eq_mul_inv]; ring]
  exact this

theorem genFun_diff_hasSum {𝕜 : Type} [NormedField 𝕜] (C d : ℕ → ℕ) (x S : 𝕜)
    (h0 : d 0 = C 0) (hs : ∀ j, C (j + 1) = C j + d (j + 1))
    (hA : HasSum (fun j => (C j : 𝕜) * x ^ j) S) :
    HasSum (fun j => (d j : 𝕜) * x ^ j) ((1 - x) * S) := by
  let h : ℕ → 𝕜 := fun j => if j = 0 then 0 else (C (j - 1) : 𝕜) * x ^ j
  have hsh : (fun n => h (n + 1)) = fun n => x * ((C n : 𝕜) * x ^ n) := by
    funext n
    simp only [h, Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero n)]
    ring
  have h1 : HasSum (fun n => h (n + 1)) (x * S) := by rw [hsh]; exact hA.mul_left x
  have hh : HasSum h (x * S) := by
    have := (hasSum_nat_add_iff (f := h) 1).1 h1
    simpa [h] using this
  have hd : (fun j => (d j : 𝕜) * x ^ j) = fun j => (C j : 𝕜) * x ^ j - h j := by
    funext j
    rcases j with _ | j
    · simp [h, h0]
    · simp only [h, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel, hs j]
      push_cast; ring
  rw [hd, show (1 - x) * S = S - x * S by ring]
  exact hA.sub hh

theorem genFun_fibre_hasSum {ι 𝕜 : Type} [NormedField 𝕜] (f : ι → ℕ) (l j : ℕ) (x : 𝕜)
    (hfin : Set.Finite {i | f i - l = j}) (hl : ∀ i, l ≤ f i) :
    HasSum (fun y : {i // f i - l = j} => x ^ f y.1) ((Set.ncard {i | f i - l = j} : 𝕜) * x ^ (l + j)) := by
  haveI : Finite {i // f i - l = j} := hfin.to_subtype
  haveI : Fintype {i // f i - l = j} := Fintype.ofFinite _
  have hc : ∀ y : {i // f i - l = j}, x ^ f y.1 = x ^ (l + j) := fun y => by
    have := hl y.1; have := y.2
    rw [show f y.1 = l + j by omega]
  have e : Nat.card {i // f i - l = j} = Set.ncard {i | f i - l = j} := Nat.card_coe_set_eq _
  have h := hasSum_fintype (fun y : {i // f i - l = j} => x ^ f y.1)
  rw [Finset.sum_congr rfl (fun y _ => hc y), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, e] at h
  exact h

theorem genFun_holds : GenFun := by
  intro ι f l c q N X hc hq hl hcard hX
  let C : ℕ → ℕ := fun j => c * q ^ (2 * N * (j / 2) + j)
  let g : ι → ℕ := fun i => f i - l
  have hCpos : ∀ j, C j ≠ 0 := fun j =>
    Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
  have hle : ∀ j, {i | g i ≤ j} = {i | f i ≤ l + j} := fun j => by
    ext i; simp only [Set.mem_setOf_eq, g]; have := hl i; omega
  have hcum : ∀ j, Set.ncard {i | g i ≤ j} = C j := fun j => by
    rw [hle, ← Nat.card_coe_set_eq]; exact hcard j
  have hfin : ∀ j, Set.Finite {i | g i ≤ j} := fun j => by
    apply Set.finite_of_ncard_ne_zero; rw [hcum]; exact hCpos j
  have hfin' : ∀ j, Set.Finite {i | f i - l = j} := fun j =>
    (hfin j).subset fun i hi => by simp only [Set.mem_setOf_eq, g] at hi ⊢; omega
  let d : ℕ → ℕ := fun j => Set.ncard {i | f i - l = j}
  have h0 : d 0 = C 0 := by
    rw [← hcum 0]
    show Set.ncard {i | f i - l = 0} = _
    congr 1; ext i; simp only [Set.mem_setOf_eq, g]; omega
  have hs : ∀ j, C (j + 1) = C j + d (j + 1) := fun j => by
    have hdis : Disjoint {i | g i ≤ j} {i | f i - l = j + 1} :=
      Set.disjoint_left.2 fun i h1 h2 => by simp only [Set.mem_setOf_eq, g] at h1 h2; omega
    have hun : {i | g i ≤ j + 1} = {i | g i ≤ j} ∪ {i | f i - l = j + 1} := by
      ext i; simp only [Set.mem_setOf_eq, Set.mem_union, g]; omega
    rw [← hcum, ← hcum, hun, Set.ncard_union_eq hdis (hfin j) (hfin' (j + 1))]
  let e := Equiv.sigmaFiberEquiv g
  have hr : ‖(q : ℝ) ^ (N + 1) * ‖X‖‖ < 1 := by
    rw [norm_mul, norm_pow, Real.norm_natCast, norm_norm]
    rwa [norm_mul, norm_pow, Complex.norm_natCast] at hX
  have hRB := (genFun_diff_hasSum C d ‖X‖ _ h0 hs (genFun_counts_hasSum c q N ‖X‖ hr)).mul_left (‖X‖ ^ l)
  have hsumR : Summable (fun i => ‖X‖ ^ f i) := by
    rw [← e.summable_iff]
    refine (summable_sigma_of_nonneg (f := (fun i => ‖X‖ ^ f i) ∘ e) (fun _ => pow_nonneg (norm_nonneg _) _)).2 ⟨fun j => (genFun_fibre_hasSum f l j ‖X‖ (hfin' j) hl).summable, ?_⟩
    refine hRB.summable.congr fun j => ?_
    have ht : ∑' (y : {x // g x = j}), ((fun i => ‖X‖ ^ f i) ∘ e) ⟨j, y⟩ = (d j : ℝ) * ‖X‖ ^ (l + j) :=
      (genFun_fibre_hasSum f l j ‖X‖ (hfin' j) hl).tsum_eq
    rw [ht, pow_add]
    ring
  have hsumC : Summable (fun i => X ^ f i) := Summable.of_norm (by simpa [norm_pow] using hsumR)
  have hB := (genFun_diff_hasSum C d X _ h0 hs (genFun_counts_hasSum c q N X hX)).mul_left (X ^ l)
  have hBC : HasSum (fun j => (d j : ℂ) * X ^ (l + j)) (c * X ^ l * jFac q N X) := by
    have e1 : (fun j => (d j : ℂ) * X ^ (l + j)) = fun j => X ^ l * ((d j : ℂ) * X ^ j) := by
      funext j; rw [pow_add]; ring
    rw [e1, show (c : ℂ) * X ^ l * jFac q N X =
      X ^ l * ((1 - X) * (c * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2))) by unfold jFac; ring]
    exact hB
  have hsig := HasSum.sigma_of_hasSum (f := (fun i => X ^ f i) ∘ e) hBC
    (fun j => genFun_fibre_hasSum f l j X (hfin' j) hl) (e.summable_iff.2 hsumC)
  exact e.hasSum_iff.1 hsig

end GlobalTheory.InertZeta
end
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_count_generating_series_formula : GenFun := by
  atlas_forward_decl GlobalTheory.InertZeta.genFun_holds
end

section
section
open GlobalTheory.InertZeta

namespace GlobalTheory.InertZeta.LeviSum

theorem int_geom (β y₀ : ℂ) (hβ : β ≠ 0) (h1 : ‖y₀ * β‖ < 1) (h2 : ‖y₀ / β‖ < 1) :
    HasSum (fun a : ℤ => β ^ a * y₀ ^ a.natAbs) ((1 - y₀ * β)⁻¹ + y₀ / β * (1 - y₀ / β)⁻¹) := by
  apply HasSum.of_nat_of_neg_add_one
  · have e : ∀ n : ℕ, β ^ (n : ℤ) * y₀ ^ (n : ℤ).natAbs = (y₀ * β) ^ n := fun n => by
      simp [zpow_natCast, mul_pow, mul_comm]
    simp only [e]
    exact hasSum_geometric_of_norm_lt_one h1
  · have e : ∀ n : ℕ, β ^ (-((n : ℤ) + 1)) * y₀ ^ (-((n : ℤ) + 1)).natAbs = y₀ / β * (y₀ / β) ^ n := fun n => by
      rw [show (-((n : ℤ) + 1)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
        show (-((n + 1 : ℕ) : ℤ)).natAbs = n + 1 by omega, div_pow]
      field_simp
      ring
    simp only [e]
    exact (hasSum_geometric_of_norm_lt_one h2).mul_left (y₀ / β)

theorem q_pow (q : ℂ) (hq : q ≠ 0) (N : ℕ) (a : ℤ) :
    q ^ ((2 * N + 2) * a.toNat) * q ^ (-a * ((N : ℤ) + 1)) = (q ^ (N + 1)) ^ a.natAbs := by
  have h : ((a.natAbs : ℕ) : ℤ) = 2 * (a.toNat : ℤ) - a := by omega
  rw [← zpow_natCast, ← zpow_add₀ hq, ← pow_mul, ← zpow_natCast]
  congr 1
  rw [Nat.cast_mul, Nat.cast_mul, h]
  push_cast
  ring

theorem core (Y : Type) (q N : ℕ) (l : Y → ℕ) (ψ : Y → ℂ) (β X₀ Z₀ : ℂ) (hq : 1 ≤ q) (hβ : β ≠ 0)
    (hy : ‖(q : ℂ) ^ (N + 1) * X₀‖ < 1) (h1 : ‖(q : ℂ) ^ (N + 1) * X₀‖ * ‖β‖ < 1)
    (h2 : ‖(q : ℂ) ^ (N + 1) * X₀‖ * ‖β‖⁻¹ < 1)
    (hZ : HasSum (fun b => ((q : ℂ) ^ 2 * X₀) ^ l b * ψ b) Z₀) :
    HasSum (fun p : ℤ × Y => ((q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * X₀ ^ (p.1.natAbs + l p.2) *
      jFac q N X₀) * (β ^ p.1 * (q : ℂ) ^ (-p.1 * ((N : ℤ) + 1)) * ψ p.2))
      ((1 - X₀) * (1 + q * X₀) * ((1 - (q : ℂ) ^ (N + 1) * X₀ * β)⁻¹ * (1 - (q : ℂ) ^ (N + 1) * X₀ / β)⁻¹) * Z₀) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  set y₀ := (q : ℂ) ^ (N + 1) * X₀ with hy₀
  have hA := int_geom β y₀ hβ (by rw [norm_mul]; exact h1) (by rw [norm_div, div_eq_mul_inv]; exact h2)
  have sA : Summable (fun a : ℤ => ‖β ^ a * y₀ ^ a.natAbs‖) := summable_norm_iff.mpr hA.summable
  have sB : Summable (fun b : Y => ‖((q : ℂ) ^ 2 * X₀) ^ l b * ψ b‖) := summable_norm_iff.mpr hZ.summable
  have sAB : Summable (fun p : ℤ × Y => (β ^ p.1 * y₀ ^ p.1.natAbs) * (((q : ℂ) ^ 2 * X₀) ^ l p.2 * ψ p.2)) :=
    summable_mul_of_summable_norm (f := fun a : ℤ => β ^ a * y₀ ^ a.natAbs)
      (g := fun b : Y => ((q : ℂ) ^ 2 * X₀) ^ l b * ψ b) sA sB
  have hprod := (HasSum.mul (f := fun a : ℤ => β ^ a * y₀ ^ a.natAbs)
      (g := fun b : Y => ((q : ℂ) ^ 2 * X₀) ^ l b * ψ b) hA hZ sAB).mul_right (jFac q N X₀)
  have n1 : 1 - y₀ * β ≠ 0 := fun h => by
    have e : ‖y₀ * β‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
    rw [norm_mul] at e; linarith
  have n2 : 1 - y₀ / β ≠ 0 := fun h => by
    have e : ‖y₀ / β‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
    rw [norm_div, div_eq_mul_inv] at e; linarith
  have hβy : β - y₀ ≠ 0 := fun h => n2 (by rw [← sub_eq_zero.mp h, div_self hβ, sub_self])
  have hβy' : -y₀ + β ≠ 0 := by rwa [neg_add_eq_sub]
  have n3 : 1 - y₀ ^ 2 ≠ 0 := fun h => by
    rw [sub_eq_zero] at h
    have := congrArg norm h
    rw [norm_one, norm_pow] at this
    nlinarith [norm_nonneg y₀]
  have ev : ((1 - y₀ * β)⁻¹ + y₀ / β * (1 - y₀ / β)⁻¹) * Z₀ * jFac q N X₀ =
      (1 - X₀) * (1 + q * X₀) * ((1 - y₀ * β)⁻¹ * (1 - y₀ / β)⁻¹) * Z₀ := by
    simp only [jFac]
    rw [← hy₀]
    field_simp
    ring
  rw [← ev]
  convert hprod using 1
  case e'_3 => rfl
  funext p
  obtain ⟨a, b⟩ := p
  simp only
  rw [hy₀, mul_pow, ← q_pow (q : ℂ) hq0 N a, pow_add, pow_add, mul_pow, ← pow_mul]
  ring

end GlobalTheory.InertZeta.LeviSum

namespace GlobalTheory.InertZeta

open LeviSum in

theorem step : Step := by
  intro Y C q N ℓ l φ₀ α X y Z hq hα hy hy1 hyα hyα' H hZ
  subst hy
  have hg := core Y q N l φ₀ α X Z hq hα hy1 hyα hyα' hZ
  have hfib : ∀ ab : ℤ × Y, HasSum (fun c => X ^ ℓ ab.1 ab.2 c *
      (α ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * φ₀ ab.2))
      (((q : ℂ) ^ (2 * l ab.2 + (2 * N + 2) * ab.1.toNat) * X ^ (ab.1.natAbs + l ab.2) * jFac q N X) *
        (α ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * φ₀ ab.2)) :=
    fun ab => (H X hy1 ab.1 ab.2).mul_right _

  have hXn : ‖(q : ℂ) ^ (N + 1) * ((‖X‖ : ℝ) : ℂ)‖ = ‖(q : ℂ) ^ (N + 1) * X‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have hαn : ‖((‖α‖ : ℝ) : ℂ)‖ = ‖α‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have hZn : Summable (fun b => ((q : ℂ) ^ 2 * ((‖X‖ : ℝ) : ℂ)) ^ l b * ((‖φ₀ b‖ : ℝ) : ℂ)) := by
    have := Complex.summable_ofReal.mpr (summable_norm_iff.mpr hZ.summable)
    convert this using 2 with b
    push_cast [norm_mul, norm_pow, Complex.norm_natCast]
    ring
  have hgn := core Y q N l (fun b => ((‖φ₀ b‖ : ℝ) : ℂ)) ((‖α‖ : ℝ) : ℂ) ((‖X‖ : ℝ) : ℂ) _ hq
    (by exact_mod_cast norm_ne_zero_iff.mpr hα) (hXn ▸ hy1) (by rw [hXn, hαn]; exact hyα)
    (by rw [hXn, hαn]; exact hyα') hZn.hasSum
  have hfibn : ∀ ab : ℤ × Y, HasSum (fun c => ((‖X‖ : ℝ) : ℂ) ^ ℓ ab.1 ab.2 c *
      (((‖α‖ : ℝ) : ℂ) ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * ((‖φ₀ ab.2‖ : ℝ) : ℂ)))
      (((q : ℂ) ^ (2 * l ab.2 + (2 * N + 2) * ab.1.toNat) * ((‖X‖ : ℝ) : ℂ) ^ (ab.1.natAbs + l ab.2) *
        jFac q N ((‖X‖ : ℝ) : ℂ)) *
        (((‖α‖ : ℝ) : ℂ) ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * ((‖φ₀ ab.2‖ : ℝ) : ℂ))) :=
    fun ab => (H _ (hXn ▸ hy1) ab.1 ab.2).mul_right _
  have hnorm : ∀ p : (ℤ × Y) × C,
      ((‖X ^ ℓ p.1.1 p.1.2 p.2 * (α ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * φ₀ p.1.2)‖ : ℝ) : ℂ) =
      ((‖X‖ : ℝ) : ℂ) ^ ℓ p.1.1 p.1.2 p.2 *
        (((‖α‖ : ℝ) : ℂ) ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * ((‖φ₀ p.1.2‖ : ℝ) : ℂ)) := by
    intro p
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_zpow, norm_zpow, Complex.norm_natCast]
    push_cast
    rfl
  have hsum : Summable (fun p : (ℤ × Y) × C =>
      X ^ ℓ p.1.1 p.1.2 p.2 * (α ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * φ₀ p.1.2)) := by
    rw [← summable_norm_iff, summable_prod_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun ab => ?_, ?_⟩
    · rw [← Complex.summable_ofReal]
      exact (funext fun c => (hnorm (ab, c)).symm) ▸ (hfibn ab).summable
    · rw [← Complex.summable_ofReal]
      refine hgn.summable.congr fun ab => ?_
      rw [Complex.ofReal_tsum]
      exact ((funext fun c => (hnorm (ab, c)).symm) ▸ (hfibn ab)).tsum_eq.symm
  rw [hg.unique (hsum.hasSum.prod_fiberwise hfib)]
  exact hsum.hasSum

end GlobalTheory.InertZeta
end

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_levi_summation_geometric_series : Step := by
  atlas_forward_decl GlobalTheory.InertZeta.step
end

section
noncomputable section

open Formalism.UG Matrix MeasureTheory GlobalTheory.SatakeWeyl GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables

namespace GlobalTheory.InertZeta

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
  have hF : FracExists := T.matrixLengthExists_of_elementaryDivisors T.elementaryDivisors_exist_discretelyValued
  have hsec : (fun g => Φ (io1 σ n g) * w g) = fun g => varX q n (χ ϖ) s ^ len (mat g) * w g := funext fun g => by
    rw [section_eq T.doubledLattice_primitive_isotropic_frame_completion hU hχ hΦ g (hF L ϖ n hU.2.2.2.1 _ (det_mat_ne_zero g))]
  have hint : ∀ Z, HasSum (fun x : GU σ n ⧸ KU σ n => varX q n (χ ϖ) s ^ len (mat x.out) * w x.out) Z →
      Integrable (fun g => Φ (io1 σ n g) * w g) μ ∧ ∫ g, Φ (io1 σ n g) * w g ∂μ = Z := fun Z hZ => by
    rw [hsec]
    refine T.integral_right_invariant_eq_sum_open_subgroup_cosets _ μ (KU σ n) (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU).1 hμ _ Z (fun g k hk => ?_) hZ
    have h1 := hw.1 1 ⟨k, hk⟩ g
    have h2 := len_mat_mul (one_mem _) hk g
    simp only [OneMemClass.coe_one, one_mul] at h1 h2
    rw [h1, h2]
  refine ⟨fun hD => ?_, fun hn => hint 1 (hasSum_small T.unitary_rank_le_one_integral_points hU hn (fun g => varX q n (χ ϖ) s ^ len (mat g) * w g)
    fun k hk => ?_)⟩
  · obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExistsU L ϖ σ q n (n / 2) hU (by omega) (by omega) (fun i => (α i : ℂ))
      fun i => (α i).ne_zero
    have h2 := hasSum_spherical hF (T.leviRadicalProductLength_of_lattice_steps T.lattice_add_vector_det_valuation T.dual_inter_eq_sum' T.blockTriangular_row_lattice_triangular_basis T.unitary_heisenberg_radical_coordinates)
      (T.smallRadicalCosetCount_of_heisenberg T.unitary_heisenberg_radical_coordinates (T.integralLatticeInverseIndex_of_elementaryDivisors T.elementaryDivisors_exist_discretelyValued) T.traceZero_integers_index_in_uniformizer_multiples) (T.small_corner_of_heisenberg_duality T.unitary_heisenberg_radical_coordinates T.dual_inter_eq_sum') T.length_count_generating_series_formula (T.unitaryIwasawaCosetSurj_of_leviElementExists T.exists_unitary_block_diagonal_levi_element)
      T.unitary_iwasawa_cells_disjoint T.exists_unitary_block_diagonal_levi_element (T.sphericalInductionTransitivity_of_leviExists T.exists_unitary_block_diagonal_levi_element) T.unitary_rank_le_one_integral_points T.unitary_levi_summation_geometric_series hU (n / 2) n (by omega) (by omega)
      (fun i => (α i : ℂ)) (varX q n (χ ϖ) s) (varY q (χ ϖ) s) φ (fun i => (α i).ne_zero) (by
        rw [varX, varY, neg_add, neg_add, Complex.cpow_add _ _ hq0, Complex.cpow_add _ _ hq0, Complex.cpow_neg_one,
          Complex.cpow_neg _ (n : ℂ), Complex.cpow_natCast]
        field_simp) hD.1 hD.2 hφ h1
    have h3 := hint _ (T.biInvariant_replace_same_double_coset_sums _ (KU σ n) (P.isCommensurated_integral_unitary_of_unramified hU n) (fun g => varX q n (χ ϖ) s ^ len (mat g)) w φ _
      (fun a b g => by simp only [len_mat_mul a.2 b.2]) hw.1 (fun g => by
        rw [hw.2.2 _ (Final.DosetIndMem _ _ ℂ g), Final.SatakeInert L ϖ σ q n (n / 2) hU (by omega) (by omega) _
          (fun i => (α i).ne_zero) _ (Final.DosetIndMem _ _ ℂ g) φ hφ, Pi.smul_apply, h1, smul_eq_mul, mul_one]) h2)
    exact ⟨h3.1, h3.2, fun m hm => h3.2.trans (closedForm_eq hq n m _ s α hm)⟩
  · have h1 := hw.1 1 ⟨k, hk⟩ 1
    simp only [OneMemClass.coe_one, one_mul] at h1
    rw [len_of_mem hk, h1, hw.2.1, pow_zero, mul_one]

end GlobalTheory.InertZeta

end
end
