import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffFrob
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupFormalChartOfConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDimAddFinrankDualLieEqHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusMatrixQuasiLogarithmBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedInOfQuasiLogarithm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallModMaximalOfFrobeniusImageSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusNilpotentModMaximalConnectedPDivGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilDualFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogarithmOfDualCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueAddSmulMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHasPAdicPowerSeriesValueOfDiffCoeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryOneMapEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePeriodQuasiLogarithmPDivGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPeriodFrobeniusTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupFormalChartEvNatMultipleEqConvPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEvaluationSubstCompatibleThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffNmul
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsSinglePair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSumElimPowerSeriesSwapVariableGroups
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftQuasiLogarithmAlongPdThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmBasisLiftPdThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameReflTransGenCyclicChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvSubstNatMultiplePrimePowConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallInvariantDifferentialDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupChartIntegralAdditiveSeriesEqZero

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.SmallFirst

theorem coeff_single_frob {Q : Type} [CommRing Q] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {d : ℕ}
    (f : MvPowerSeries (Fin d) Q) (i : Fin d) :
    coeff (Finsupp.single i p) (frob p s f) = s (lin f i) := by
  have h1 : frob p s f = expand p hp (map s f) := by
    rw [frob, expand, substAlgHom_apply]
  have h2 : (Finsupp.single i p : Fin d →₀ ℕ) = p • Finsupp.single i 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h1, h2, coeff_expand_smul, coeff_map, lin]

theorem coeff_comb {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ ι : Type} [Fintype ι]
    (b : ι → B) (e : ι → MvPowerSeries σ Q) (α : σ →₀ ℕ) :
    coeff α (comb b e) = ∑ l, algebraMap B Q (b l) * coeff α (e l) := by
  unfold comb
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [MvPowerSeries.coeff_smul]

end GlobalTheory.QLog.SmallFirst

theorem GlobalTheory.QLog.small_first_of_frob : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ w : Fin d ⊕ Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ (w j)) l))) → ∀ i, ¬IsUnit (F.θ (w (Sum.inl i))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hmap k e hbas hadp U hU w hw i
  classical
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsLocalRing O := ValuationRing.isLocalRing O
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set J : Ideal F.B := Ideal.comap F.θ (IsLocalRing.maximalIdeal O) with hJ
  have memJ : ∀ x, x ∈ J ↔ ¬IsUnit (F.θ x) := fun x => by
    rw [hJ, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hpJ : (p : F.B) ∈ J := by
    rw [memJ, map_natCast]; exact Fact.out
  haveI hJp : J.IsPrime := Ideal.IsPrime.comap F.θ
  set α : Fin d →₀ ℕ := Finsupp.single i p with hα

  have hc : ∀ l, ∃ cl : F.B, (p : F.Q) * coeff α (e l) = algebraMap F.B F.Q cl := by
    intro l
    obtain ⟨b, -, hb⟩ := GlobalTheory.QLogDiff.dIn_of_QL p F.B O F.Q F.θ F.frame d μ' hlift ⊤ (e l) (hbas.1 l) α i
    refine ⟨b, ?_⟩
    rw [← hb, hα, Finsupp.single_eq_same]
  choose cc hcc using hc
  have key : ∀ m, algebraMap F.B F.Q (∑ l, U l m * cc l) =
      (p : F.Q) * ∑ l, algebraMap F.B F.Q (U l m) * coeff α (e l) := by
    intro m
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, ← hcc]; ring
  have hcol : ∀ m l, (U * blk d k (p : F.B) 1) l m = U l m * Sum.elim (fun _ => (p : F.B)) (fun _ => 1) m := by
    intro m l
    rw [blk, Matrix.mul_diagonal]
  have hR : ∀ m, (∑ l, U l m * cc l) - (if m = Sum.inl i then 1 else 0) ∈ J := by
    intro m
    cases m with
    | inl i' =>
      obtain ⟨t, ht, hteq⟩ := (hU (Sum.inl i')).2 i' rfl α
      obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton'.1 ht
      rw [map_sub, SmallFirst.coeff_single_frob p hp0, (hadp i').2, SmallFirst.coeff_comb] at hteq
      have hs : F.s (Pi.single (M := fun _ : Fin d => F.Q) i' 1 i) =
          algebraMap F.B F.Q (if (Sum.inl i' : Fin d ⊕ Fin k) = Sum.inl i then 1 else 0) := by
        by_cases h : i' = i
        · subst h; simp
        · have h' : i ≠ i' := Ne.symm h
          simp [Pi.single_apply, h', h]
      have hsum : ∑ l, algebraMap F.B F.Q ((U * blk d k (p : F.B) 1) l (Sum.inl i')) * coeff α (e l) =
          algebraMap F.B F.Q (∑ l, U l (Sum.inl i') * cc l) := by
        rw [key, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hcol, Sum.elim_inl, map_mul, map_natCast]; ring
      rw [hs, hsum, ← map_sub] at hteq
      have := F.frame.inj hteq
      have h2 : (∑ l, U l (Sum.inl i') * cc l) - (if (Sum.inl i' : Fin d ⊕ Fin k) = Sum.inl i then 1 else 0)
          = -(t' * p) := by rw [← this]; ring
      rw [h2]
      exact J.neg_mem (J.mul_mem_left _ hpJ)
    | inr j =>
      obtain ⟨b, -, hb⟩ := (hbas.1 (Sum.inr j)).2.1 i
      obtain ⟨t, -, hteq⟩ := (hU (Sum.inr j)).1 α
      rw [map_sub, SmallFirst.coeff_single_frob p hp0, hb, F.s_alg, SmallFirst.coeff_comb] at hteq
      have hsum : ∑ l, algebraMap F.B F.Q ((U * blk d k (p : F.B) 1) l (Sum.inr j)) * coeff α (e l) =
          ∑ l, algebraMap F.B F.Q (U l (Sum.inr j)) * coeff α (e l) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hcol, Sum.elim_inr, mul_one]
      rw [hsum] at hteq
      have h3 : algebraMap F.B F.Q (∑ l, U l (Sum.inr j) * cc l) =
          algebraMap F.B F.Q ((p : F.B) * (F.σ b - t)) := by
        rw [key, map_mul, map_sub, map_natCast, ← hteq]; ring
      have h4 := F.frame.inj h3
      have hne : (Sum.inr j : Fin d ⊕ Fin k) ≠ Sum.inl i := Sum.inr_ne_inl
      rw [if_neg hne, sub_zero, h4]
      exact J.mul_mem_right _ hpJ

  have hW : ∑ m, F.σ (w m) * ∑ l, U l m * cc l ∈ J := by
    have : ∑ m, F.σ (w m) * ∑ l, U l m * cc l = ∑ l, U.mulVec (fun j => F.σ (w j)) l * cc l := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [this]
    exact J.sum_mem fun l _ => J.mul_mem_right _ ((memJ _).2 (hw l))
  have hD : ∑ m, F.σ (w m) * ((∑ l, U l m * cc l) - (if m = Sum.inl i then 1 else 0)) ∈ J :=
    J.sum_mem fun m _ => J.mul_mem_left _ (hR m)
  have hσ : F.σ (w (Sum.inl i)) ∈ J := by
    have : F.σ (w (Sum.inl i)) = (∑ m, F.σ (w m) * ∑ l, U l m * cc l) -
        ∑ m, F.σ (w m) * ((∑ l, U l m * cc l) - (if m = Sum.inl i then 1 else 0)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      ring
    rw [this]
    exact J.sub_mem hW hD
  obtain ⟨z, hz⟩ := F.σ_pow (w (Sum.inl i))
  have hpow : w (Sum.inl i) ^ p ∈ J := by
    have : w (Sum.inl i) ^ p = F.σ (w (Sum.inl i)) - p * z := by rw [← hz]; ring
    rw [this]
    exact J.sub_mem hσ (J.mul_mem_right _ hpJ)
  exact (memJ _).1 (hJp.mem_of_pow_mem p hpow)
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLog_first_block_small_of_frobenius : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ w : Fin d ⊕ Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ (w j)) l))) → ∀ i, ¬IsUnit (F.θ (w (Sum.inl i))) := by
  atlas_forward_decl GlobalTheory.QLog.small_first_of_frob
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FrobUnit

theorem isUnit_of_isUnit_map {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q] [CommRing O]
    [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) (b : B) (hb : IsUnit (θ b)) : IsUnit b := by
  obtain ⟨u, hu⟩ := hb
  obtain ⟨b', hb'⟩ := hF.surj (↑u⁻¹ : O)
  have hx0 : θ (b * b' - 1) = 0 := by
    rw [map_sub, map_mul, hb', ← hu, map_one, Units.mul_inv, sub_self]
  obtain ⟨y, -, hy⟩ := hF.pd _ hx0
  haveI := hF.complete
  have hj : (p : B) * y ∈ (⊥ : Ideal B).jacobson :=
    IsAdicComplete.le_jacobson_bot _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton (p : B))))
  have hu1 := (Ideal.mem_jacobson_bot.1 hj) (-(-1) ^ p)
  have hgeom := mul_neg_geom_sum (-(b * b' - 1)) p
  have h2 : (1 - -(b * b' - 1)) * ∑ i ∈ Finset.range p, (-(b * b' - 1)) ^ i =
      (p : B) * y * (-(-1) ^ p) + 1 := by
    rw [hgeom, neg_pow, hy]; ring
  have h3 : IsUnit (1 - -(b * b' - 1)) := isUnit_of_mul_isUnit_left (h2 ▸ hu1)
  have h4 : (1 - -(b * b' - 1)) = b * b' := by ring
  rw [h4] at h3
  exact isUnit_of_mul_isUnit_left h3

theorem exists_pow_eq {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C]
    {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) (a : O) :
    ∃ r : O, r ^ p = a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C a) (Fact.out : p.Prime).pos
  have h1 : v z ≤ 1 := by
    have := hv.map_le_one a
    rw [← hz, map_pow] at this
    exact (pow_le_one_iff_of_nonneg zero_le' (Fact.out : p.Prime).ne_zero).1 this
  obtain ⟨r, hr⟩ := hv.exists_of_le_one h1
  exact ⟨r, hv.hom_inj (by rw [map_pow, hr, hz])⟩

theorem frob_matrix_isUnit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsUnit U := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hL hμ k e hB hA U hU
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hm : ∀ x : O, ¬IsUnit x ↔ x ∈ IsLocalRing.maximalIdeal O := fun x =>
    (IsLocalRing.mem_maximalIdeal x).symm
  have hpm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := (hm _).1 (Fact.out)
  have hσ : ∀ b, ∃ z, F.σ b = b ^ p + (p : F.B) * z := fun b => by
    obtain ⟨z, hz⟩ := F.σ_pow b
    exact ⟨z, by rw [← hz]; ring⟩
  have hσm : ∀ b, F.θ b ∈ IsLocalRing.maximalIdeal O → F.θ (F.σ b) ∈ IsLocalRing.maximalIdeal O := by
    intro b hb
    obtain ⟨z, hz⟩ := hσ b
    rw [hz, map_add, map_pow, map_mul, map_natCast]
    exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ hb _ (Fact.out : p.Prime).pos)
      (Ideal.mul_mem_right _ _ hpm)
  have key : ∀ w : Fin d ⊕ Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ (w j)) l))) →
      ∀ l, ¬IsUnit (F.θ (w l)) := by
    intro w hw
    have h1 := GlobalTheory.T.quasiLog_first_block_small_of_frobenius p C v O hv ε hε F G d c μ' hL hμ k e hB hA U hU w hw
    have h2 := GlobalTheory.T.small_mod_maximal_of_frobenius_image_small p C v O hv ε hε F G d c μ' hL hμ k e hB hA U hU (fun j => w (Sum.inr j)) (by
      intro l
      rw [hm]
      have hsplit : U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) (fun j => w (Sum.inr j)) :
          Fin d ⊕ Fin k → F.B) j)) l = U.mulVec (fun j => F.σ (w j)) l -
          ∑ m, U l m * F.σ ((Sum.elim (fun i => w (Sum.inl i)) (fun _ => 0) :
            Fin d ⊕ Fin k → F.B) m) := by
        simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, ← mul_sub]
        refine Finset.sum_congr rfl fun m _ => ?_
        congr 1
        cases m <;> simp
      rw [hsplit, map_sub]
      refine Ideal.sub_mem _ ((hm _).1 (hw l)) ?_
      rw [map_sum]
      refine Ideal.sum_mem _ fun m _ => ?_
      rw [map_mul]
      refine Ideal.mul_mem_left _ _ (hσm _ ?_)
      cases m with
      | inl i => simpa using (hm _).1 (h1 i)
      | inr j => simp)
    intro l
    cases l with
    | inl i => exact h1 i
    | inr j => exact h2 j
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_of_isUnit_map F.frame
  rw [RingHom.map_det]
  by_contra hdet
  set M := (U.map F.θ).map (IsLocalRing.residue O) with hMdef
  have hM : M.det = 0 := by
    rw [show M = (IsLocalRing.residue O).mapMatrix (F.θ.mapMatrix U) from rfl, ← RingHom.map_det]
    exact (IsLocalRing.residue_eq_zero_iff _).2 ((hm _).1 hdet)
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hM
  have hlift : ∀ l, ∃ b : F.B, IsLocalRing.residue O (F.θ b) ^ p = x l := by
    intro l
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (x l)
    obtain ⟨r, hr⟩ := exists_pow_eq (p := p) hv a
    obtain ⟨b, hb⟩ := F.frame.surj r
    exact ⟨b, by rw [hb, ← map_pow, hr, ha]⟩
  choose w hw using hlift
  have hres : ∀ b, IsLocalRing.residue O (F.θ (F.σ b)) = IsLocalRing.residue O (F.θ b) ^ p := by
    intro b
    obtain ⟨z, hz⟩ := hσ b
    rw [hz, map_add, map_pow, map_mul, map_natCast, map_add, map_pow, map_mul,
      (IsLocalRing.residue_eq_zero_iff _).2 hpm, zero_mul, add_zero]
  have hk := key w (by
    intro l
    rw [hm, ← IsLocalRing.residue_eq_zero_iff]
    have := congrFun hx l
    simp only [Matrix.mulVec, dotProduct, hMdef, Matrix.map_apply, Pi.zero_apply] at this ⊢
    rw [map_sum, map_sum]
    simpa [hres, hw] using this)
  apply hx0
  funext l
  rw [← hw l, (IsLocalRing.residue_eq_zero_iff _).2 ((hm _).1 (hk l)), zero_pow (Fact.out : p.Prime).ne_zero,
    Pi.zero_apply]

end GlobalTheory.FrobUnit
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_matrix_isUnit_adapted_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsUnit U := by
  atlas_forward_decl GlobalTheory.FrobUnit.frob_matrix_isUnit
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem lift_topNil {p : ℕ} [Fact p.Prime] {O B Q : Type} [CommRing O] [CommRing B] [CommRing Q]
    [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) {G : PDivGroup p O} {d : ℕ} (c : Chart G d)
    (t : G.Tate) (n : ℕ) (z : Fin d → B) (hz : ∀ i, θ (z i) = t.pt n (c.x n i)) :
    ∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N := by
  intro i
  obtain ⟨N, a, ha⟩ := c.nil n i
  obtain ⟨a', ha'⟩ := hF.surj (t.pt n a)
  have hw : θ (z i ^ N - p * a') = 0 := by
    rw [map_sub, map_pow, hz, map_mul, map_natCast, ha', ← map_pow, ha, map_mul, map_natCast, sub_self]
  obtain ⟨w, -, hw'⟩ := hF.pd _ hw
  refine ⟨N * p, ?_⟩
  have h1 : (p : B) * a' ∣ (z i ^ N) ^ p - (z i ^ N - p * a') ^ p := by
    have := sub_dvd_pow_sub_pow (z i ^ N) (z i ^ N - p * a') p
    simpa using this
  rw [pow_mul]
  have h2 : (p : B) ∣ (z i ^ N) ^ p - (z i ^ N - p * a') ^ p := dvd_trans (dvd_mul_right _ _) h1
  have h3 : (p : B) ∣ (z i ^ N - p * a') ^ p := hw' ▸ dvd_mul_right _ _
  have := dvd_add h2 h3
  simpa using this

end GlobalTheory.QLog

namespace GlobalTheory.QLog

theorem val_integral {p : ℕ} {σ B Q : Type} [Fintype σ] [DecidableEq σ] [CommRing B] [CommRing Q]
    [Algebra B Q] (z : σ → B) (s : MvPowerSeries σ B) (q : Q)
    (h : HasVal p z (map (algebraMap B Q) s) q) : ∃ b : B, q = algebraMap B Q b := by
  obtain ⟨N, hN⟩ := h 0
  obtain ⟨b, hb⟩ := hN N le_rfl
  have hE : (MvPolynomial.eval fun i => algebraMap B Q (z i))
      (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => N) (map (algebraMap B Q) s)) =
      algebraMap B Q (MvPolynomial.eval z (trunc' B (Finsupp.equivFunOnFinite.symm fun _ => N) s)) := by
    rw [trunc'_map, MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_comp_left]
    rfl
  refine ⟨MvPolynomial.eval z (trunc' B (Finsupp.equivFunOnFinite.symm fun _ => N) s) + b, ?_⟩
  rw [hE, pow_zero, one_mul, sub_eq_iff_eq_add'] at hb
  rw [hb, map_add]

end GlobalTheory.QLog

namespace GlobalTheory.QLog

theorem hasPeriod_add_smul {p : ℕ} [Fact p.Prime] {O B Q : Type} [CommRing O] [CommRing B]
    [CommRing Q] [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) {G : PDivGroup p O} {d : ℕ}
    (c : Chart G d) (t : G.Tate) {f g : MvPowerSeries (Fin d) Q} {y y' : B} (b : B)
    (hf : c.HasPeriod θ t f y) (hg : c.HasPeriod θ t g y') :
    c.HasPeriod θ t (f + algebraMap B Q b • g) (y + b * y') := by
  rw [c.hasPeriod_iff hF] at hf hg ⊢
  intro n z hz
  obtain ⟨q, hq, b1, hb1⟩ := hf n z hz
  obtain ⟨r, hr, b2, hb2⟩ := hg n z hz
  have h1 := (GlobalTheory.QLog.ValLin.hasVal_add_smul_map p B O Q θ hF (Fin d) z g g r r hr).2.1 (algebraMap B Q b)
  have h2 := (GlobalTheory.QLog.ValLin.hasVal_add_smul_map p B O Q θ hF (Fin d) z _ _ q _ hq).1 h1
  refine ⟨_, h2, b1 + b * b2, ?_⟩
  have e : (p : Q) ^ n * (q + algebraMap B Q b * r) =
      (p : Q) ^ n * q + algebraMap B Q b * ((p : Q) ^ n * r) := by ring
  rw [e, hb1, hb2, ← map_mul, ← map_add]
  congr 1
  ring

theorem hasPeriod_integral {p : ℕ} [Fact p.Prime] {O B Q : Type} [CommRing O] [CommRing B]
    [CommRing Q] [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) {G : PDivGroup p O} {d : ℕ}
    (c : Chart G d) (t : G.Tate) (s : MvPowerSeries (Fin d) B) :
    c.HasPeriod θ t (map (algebraMap B Q) s) 0 := by
  rw [c.hasPeriod_iff hF]
  intro n z hz
  have hD : DIn (⊤ : Ideal B) (map (algebraMap B Q) s) := fun α i =>
    ⟨(α i : B) * coeff α s, trivial, by rw [coeff_map, map_mul, map_natCast]⟩
  obtain ⟨q, hq, -⟩ := GlobalTheory.QLog.existsUnique_hasVal_of_dIn p B O Q θ hF (Fin d) z (lift_topNil hF c t n z hz) _ hD
  obtain ⟨e, he⟩ := val_integral z s q hq
  exact ⟨q, hq, e, by rw [he, zero_add, map_mul, map_pow, map_natCast]⟩

open MvPowerSeries in
private lemma exists_pow_dvd_of_theta_eq_of_isFrame {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] {θ : B →+* O} (hθ : _root_.GlobalTheory.QLog.IsFrame p Q θ)
    {z : B} {a : O} (hza : θ z = a) {N : ℕ} (ha : (p : O) ∣ a ^ N) :
    ∃ M, (p : B) ∣ z ^ M := by
  obtain ⟨w, hw⟩ := ha
  obtain ⟨b, hb⟩ := hθ.surj w
  obtain ⟨y, -, hy⟩ := hθ.pd (z ^ N - p * b)
    (by simp [hza, hb, hw])
  refine ⟨N * p, ?_⟩
  have h1 : (p : B) ∣ (z ^ N) ^ p - (z ^ N - p * b) ^ p :=
    (dvd_mul_right (p : B) b).trans (by simpa using sub_dvd_pow_sub_pow (z ^ N) (z ^ N - p * b) p)
  have h2 : (z ^ N) ^ p = ((z ^ N) ^ p - (z ^ N - p * b) ^ p) + p * y := by rw [← hy]; ring
  rw [pow_mul, h2]
  exact dvd_add h1 (dvd_mul_right _ _)

open MvPowerSeries in
private lemma eval_algebraMap_trunc'_map_eq_algebraMap_eval {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]
    {d : ℕ} (s : MvPowerSeries (Fin d) B) (z : Fin d → B) (N : ℕ) :
    MvPolynomial.eval (fun i ↦ algebraMap B Q (z i))
        (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ ↦ N) (map (algebraMap B Q) s)) =
      algebraMap B Q (MvPolynomial.eval z (trunc' B (Finsupp.equivFunOnFinite.symm fun _ ↦ N) s)) := by
  rw [MvPowerSeries.trunc'_map, MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  rfl

open MvPowerSeries in

theorem _root_.GlobalTheory.QLog.hasPeriod_linear : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : _root_.GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), ∀ F : _root_.GlobalTheory.QLog.BFrame ε, ∀ (G : _root_.GlobalTheory.PDivGroup p O) (d : ℕ) (c : _root_.GlobalTheory.QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), _root_.GlobalTheory.QLog.IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f g : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y y' b : F.B), c.HasPeriod F.θ t f y → c.HasPeriod F.θ t g y' → c.HasPeriod F.θ t (f + algebraMap F.B F.Q b • g) (y + b * y') ∧ (∀ s : MvPowerSeries (Fin d) F.B, constantCoeff s = 0 → c.HasPeriod F.θ t (map (algebraMap F.B F.Q) s) 0) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F G d c μ' _ _ f g t y y' b hf hg
  have hF := F.frame
  rw [c.hasPeriod_iff hF] at hf hg
  refine ⟨?_, ?_⟩
  · rw [c.hasPeriod_iff hF]
    intro n z hz
    obtain ⟨q, hq, b₁, hb₁⟩ := hf n z hz
    obtain ⟨r, hr, b₂, hb₂⟩ := hg n z hz
    have hbr := (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ F.θ hF (Fin d) z g f
      r q hr).2.1 (algebraMap _ _ b)
    refine ⟨q + algebraMap _ _ b * r,
      (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ F.θ hF (Fin d) z f _ q _
        hq).1 hbr, b₁ + b * b₂, ?_⟩
    simp only [map_add, map_mul, map_pow, map_natCast] at hb₁ hb₂ ⊢
    linear_combination hb₁ + algebraMap _ _ b * hb₂
  · intro s _
    rw [c.hasPeriod_iff hF]
    intro n z hz
    have hz' : ∀ i, ∃ M, (p : F.B) ∣ z i ^ M := fun i => by
      obtain ⟨N, hN⟩ := c.nil n i
      refine exists_pow_dvd_of_theta_eq_of_isFrame hF (hz i) (N := N) ?_
      simpa [map_pow, map_natCast] using map_dvd (t.pt n) hN
    have hd : _root_.GlobalTheory.QLog.DIn (⊤ : Ideal F.B)
        (map (algebraMap F.B F.Q) s) := by
      intro α i
      exact ⟨(α i : F.B) * coeff α s, Submodule.mem_top, by simp⟩
    obtain ⟨q, hq, -⟩ := _root_.GlobalTheory.QLog.existsUnique_hasVal_of_dIn p _ O _
      F.θ hF (Fin d) z hz' _ hd
    have hq' := hq
    unfold _root_.GlobalTheory.QLog.HasVal at hq'
    obtain ⟨N, hN⟩ := hq' 0
    obtain ⟨e, he⟩ := hN N le_rfl
    refine ⟨q, hq, MvPolynomial.eval z
      (trunc' F.B (Finsupp.equivFunOnFinite.symm fun _ ↦ N) s) + e, ?_⟩
    rw [eval_algebraMap_trunc'_map_eq_algebraMap_eval, pow_zero, one_mul] at he
    have hq2 : q = algebraMap _ F.Q (MvPolynomial.eval z
        (trunc' F.B (Finsupp.equivFunOnFinite.symm fun _ ↦ N) s) + e) := by
      rw [map_add, ← he]
      ring
    rw [hq2, zero_add, map_mul, map_pow, map_natCast]

end GlobalTheory.QLog
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalChart_hasPeriod_linear_integral : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f g : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y y' b : F.B), c.HasPeriod F.θ t f y → c.HasPeriod F.θ t g y' → c.HasPeriod F.θ t (f + algebraMap F.B F.Q b • g) (y + b * y') ∧ (∀ s : MvPowerSeries (Fin d) F.B, constantCoeff s = 0 → c.HasPeriod F.θ t (map (algebraMap F.B F.Q) s) 0) := by
  atlas_forward_decl GlobalTheory.QLog.hasPeriod_linear
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

open MvPowerSeries in

theorem _root_.GlobalTheory.QLog.hasPeriod_reduce : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : _root_.GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), ∀ F : _root_.GlobalTheory.QLog.BFrame ε, ∀ (G : _root_.GlobalTheory.PDivGroup p O) (d : ℕ) (c : _root_.GlobalTheory.QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), _root_.GlobalTheory.QLog.IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (E : Type) [CommRing E] [Algebra O E], _root_.GlobalTheory.QLog.IsFrame p E (RingHom.id O) → ∀ Θ : F.Q →+* E, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O E (F.θ b)) → ∀ (f : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y : F.B), _root_.GlobalTheory.QLog.QL μ' ⊤ f → c.HasPeriod F.θ t f y → c.HasPeriod (RingHom.id O) t (map Θ f) (F.θ y) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F G d c μ' _ _ E _ _ hE Θ hΘ f t y _ hy
  have hF := F.frame
  rw [_root_.GlobalTheory.QLog.Chart.hasPeriod_iff c hF] at hy
  rw [_root_.GlobalTheory.QLog.Chart.hasPeriod_iff c hE]
  intro n z hz
  choose w hw using fun i => hF.surj (z i)
  obtain ⟨q, hq, b, hb⟩ := hy n w (fun i => by rw [hw]; exact hz i)
  refine ⟨Θ q, ?_, F.θ b, ?_⟩
  · have hmap := (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ F.θ hF _ w f f q q
      hq).2.2 O E F.θ Θ hΘ
    simpa [hw] using hmap
  · have h2 := congrArg Θ hb
    rw [map_mul, map_pow, map_natCast, hΘ, map_add, map_mul, map_pow, map_natCast] at h2
    exact h2

end GlobalTheory.QLog
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasPeriod_reduce_along_theta_to_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ Θ : F.Q →+* E, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O E (F.θ b)) → ∀ (f : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y : F.B), QL μ' ⊤ f → c.HasPeriod F.θ t f y → c.HasPeriod (RingHom.id O) t (map Θ f) (F.θ y) := by
  atlas_forward_decl GlobalTheory.QLog.hasPeriod_reduce
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogPeriod

variable {p : ℕ} {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type} [Fintype σ]
  [DecidableEq σ]

open MvPowerSeries in
set_option autoImplicit false in
private theorem pderiv_map_algebraMap {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q]
    (k : σ) (g : MvPowerSeries σ B) :
    pderiv Q k (map (algebraMap B Q) g) = map (algebraMap B Q) (pderiv B k g) := by
  ext n
  simp [coeff_pderiv, coeff_map]

open MvPowerSeries in
set_option autoImplicit false in
private theorem subst_zero_eq_C_constantCoeff_divisor {σ τ Q : Type} [CommRing Q] [Finite σ] (h : MvPowerSeries σ Q) :
    subst (fun _ : σ => (0 : MvPowerSeries τ Q)) h = C (constantCoeff h) := by
  classical
  ext e
  rw [coeff_subst (hasSubst_of_constantCoeff_zero (fun _ => by simp))]
  rw [finsum_eq_single _ 0]
  · by_cases he : e = 0 <;> simp [coeff_C, coeff_one, he]
  · intro k hk
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hk
    have : (k.prod fun s n => (0 : MvPowerSeries τ Q) ^ n) = 0 := by
      apply Finset.prod_eq_zero (i := s)
      · simpa using hs
      · simp [zero_pow (by simpa using hs)]
    simp [this]

open MvPowerSeries in
set_option autoImplicit false in
private theorem dIn_univ_of_QL_of_isLaw {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : _root_.GlobalTheory.Katz.IsLaw μ)
    {f : MvPowerSeries (Fin d) Q} (hf : _root_.GlobalTheory.QLog.QL μ ⊤ f) :
    _root_.GlobalTheory.QLog.DIn (B := B) ⊤ f := by
  classical
  obtain ⟨hf0, hlin, hcob⟩ := hf
  obtain ⟨hμ0, hunit, hswap, -⟩ := hμ
  let μQ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) Q := fun j => map (algebraMap B Q) (μ j)
  have hμQ : _root_.GlobalTheory.QLog.up Q μ = μQ := rfl
  have hμQ0 : ∀ j, constantCoeff (μQ j) = 0 := fun j => by simp [μQ, constantCoeff_map, hμ0 j]
  have hsμ : HasSubst μQ := hasSubst_of_constantCoeff_zero hμQ0
  let e : Fin d ⊕ Fin d → MvPowerSeries (Fin d) Q := Sum.elim (fun i => X i) (fun _ => 0)
  have he : HasSubst e := hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp [e])
  let eB : Fin d ⊕ Fin d → MvPowerSeries (Fin d) B := Sum.elim (fun i => X i) (fun _ => 0)
  have heB : HasSubst eB := hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp [eB])
  have hmape : (fun s => map (algebraMap B Q) (eB s)) = e := by
    funext s; rcases s with i | i <;> simp [e, eB]
  have hunitB : ∀ j, subst eB (μ j) = X j := by
    intro j
    have := congrFun hunit j
    simpa [_root_.GlobalTheory.Katz.op, _root_.GlobalTheory.Katz.at2, eB] using this
  have hunitQ : ∀ j, subst e (μQ j) = X j := by
    intro j
    have := congrArg (map (algebraMap B Q)) (hunitB j)
    rw [map_subst heB, hmape, map_X] at this
    exact this
  have hρμ : ∀ h : MvPowerSeries (Fin d) Q, subst e (subst μQ h) = h := by
    intro h
    rw [subst_comp_subst_apply hsμ he]
    simp only [hunitQ]
    exact congrFun subst_self h
  have hlinμ : ∀ i j, coeff (Finsupp.single (Sum.inr i) 1) (μ j) = if i = j then 1 else 0 := by
    intro i j
    have hs1 : HasSubst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) B)) fun k : Fin d => X k) :=
      hasSubst_of_constantCoeff_zero (by rintro (k | k) <;> simp)
    have hs2 : HasSubst (Sum.elim (fun k => (X (Sum.inr k) : MvPowerSeries (Fin d ⊕ Fin d) B))
        fun k => X (Sum.inl k)) :=
      hasSubst_of_constantCoeff_zero (by rintro (k | k) <;> simp)
    have hsw := congrArg (subst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) B)) fun k : Fin d => X k)) (hswap j)
    unfold _root_.GlobalTheory.Katz.swap _root_.GlobalTheory.Katz.at2 at hsw
    rw [subst_comp_subst_apply hs2 hs1] at hsw
    have hfun : (fun s => subst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) B)) fun k : Fin d => X k)
        (Sum.elim (fun k => (X (Sum.inr k) : MvPowerSeries (Fin d ⊕ Fin d) B)) (fun k => X (Sum.inl k)) s)) = eB := by
      funext s
      rcases s with k | k <;> simp [eB, subst_X hs1]
    rw [hfun, hunitB] at hsw
    have hc := (_root_.GlobalTheory.coeff_subst_restrict_sum (μ j)).2 (Finsupp.single i 1)
    rw [← hsw, Finsupp.mapDomain_single, coeff_X] at hc
    rw [← hc]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Finsupp.single_left_inj]
  let M : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) B) :=
    fun j i => subst eB (pderiv B (Sum.inr i) (μ j))
  have hM : ∀ i j, constantCoeff (M i j) = if i = j then 1 else 0 := by
    intro i j
    rw [← coeff_zero_eq_constantCoeff_apply]
    have := (_root_.GlobalTheory.coeff_subst_restrict_sum (pderiv B (Sum.inr j) (μ i))).1 0
    simp only [M, eB]
    rw [this, Finsupp.mapDomain_zero, coeff_pderiv, zero_add, hlinμ j i]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  have hmapsub : ∀ g : MvPowerSeries (Fin d ⊕ Fin d) B,
      subst e (map (algebraMap B Q) g) = map (algebraMap B Q) (subst eB g) := by
    intro g
    rw [map_subst heB, hmape]
  have hchain : ∀ i, ∑ j, pderiv Q j f * map (algebraMap B Q) (M j i) =
      subst e (pderiv Q (Sum.inr i) (subst μQ f)) := by
    intro i
    rw [_root_.GlobalTheory.PSChain.pderiv_subst_chain μQ hμQ0 f (Sum.inr i), ← coe_substAlgHom he, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, coe_substAlgHom, hρμ]
    simp only [M, μQ]
    rw [pderiv_map_algebraMap, hmapsub]
  have hg : ∀ i, _root_.GlobalTheory.QLog.In (B := B) ⊤
      (subst e (pderiv Q (Sum.inr i) (subst μQ f))) := by
    intro i
    obtain ⟨s₀, hs₀⟩ := _root_.GlobalTheory.QLog.In.top_iff.1 hcob
    have hdec : subst μQ f = map (algebraMap B Q) s₀ + _root_.GlobalTheory.Katz.inL f +
        _root_.GlobalTheory.Katz.inR f := by
      rw [hs₀]
      unfold _root_.GlobalTheory.Katz.cob1
      rw [hμQ]
      ring
    have hleft : pderiv Q (Sum.inr i) (_root_.GlobalTheory.Katz.inL f) = 0 := by
      unfold _root_.GlobalTheory.Katz.inL
      rw [_root_.GlobalTheory.PSChain.pderiv_subst_chain _ (fun k => by simp) f (Sum.inr i)]
      simp [pderiv_X]
    have hright : pderiv Q (Sum.inr i) (_root_.GlobalTheory.Katz.inR f) =
        subst (fun k => (X (Sum.inr k) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (pderiv Q i f) := by
      unfold _root_.GlobalTheory.Katz.inR
      rw [_root_.GlobalTheory.PSChain.pderiv_subst_chain _ (fun k => by simp) f (Sum.inr i)]
      simp [pderiv_X, Pi.single_apply]
    obtain ⟨b, -, hb⟩ := hlin i
    have hX : HasSubst (fun k => (X (Sum.inr k) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
      hasSubst_of_constantCoeff_zero (fun k => by simp)
    have hrr : subst e (subst (fun k => (X (Sum.inr k) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (pderiv Q i f)) =
        map (algebraMap B Q) (C b) := by
      rw [subst_comp_subst_apply hX he]
      have hz : (fun k : Fin d => subst e (X (Sum.inr k) : MvPowerSeries (Fin d ⊕ Fin d) Q)) =
          fun _ => 0 := by
        funext k
        rw [subst_X he]
        rfl
      rw [hz, subst_zero_eq_C_constantCoeff_divisor, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
      unfold _root_.GlobalTheory.Katz.lin at hb
      simp [hb]
    rw [_root_.GlobalTheory.QLog.In.top_iff]
    refine ⟨subst eB (pderiv B (Sum.inr i) s₀) + C b, ?_⟩
    rw [hdec]
    simp only [map_add]
    rw [hleft, hright, add_zero, ← coe_substAlgHom he, map_add, coe_substAlgHom, hrr,
      pderiv_map_algebraMap, hmapsub]
  have hsol := _root_.GlobalTheory.InvSolve.solve ⊤ M hM (fun j => pderiv Q j f)
    (fun i => subst e (pderiv Q (Sum.inr i) (subst μQ f))) hchain hg
  intro α i
  by_cases hα : α i = 0
  · exact ⟨0, Submodule.mem_top, by simp [hα]⟩
  · obtain ⟨b, -, hb⟩ := hsol i (α - Finsupp.single i 1)
    refine ⟨b, Submodule.mem_top, ?_⟩
    have hαe : α - Finsupp.single i 1 + Finsupp.single i 1 = α := by
      ext k
      by_cases hk : k = i
      · subst hk; simp; omega
      · simp [Finsupp.single_apply, Ne.symm hk]
    have hαi : (((α - Finsupp.single i 1 : Fin d →₀ ℕ) i : ℕ) : Q) + 1 = (α i : Q) := by
      have : (α - Finsupp.single i 1 : Fin d →₀ ℕ) i + 1 = α i := by simp; omega
      rw [← this]
      push_cast
      ring
    rw [← hb, coeff_pderiv, hαe, hαi, mul_comm]

open MvPowerSeries in
set_option autoImplicit false in
private theorem constantCoeff_nmul_eq_zero {d : ℕ} {R : Type} [CommRing R]
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.QLog.nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [_root_.GlobalTheory.QLog.nmul]
  | succ k ih =>
    have hstep : _root_.GlobalTheory.QLog.nmul μ (k + 1) i =
        _root_.GlobalTheory.Katz.at2 (μ i) (_root_.GlobalTheory.QLog.nmul μ k) (fun j => X j) := by
      unfold _root_.GlobalTheory.QLog.nmul
      rw [Function.iterate_succ_apply']
      rfl
    rw [hstep]
    unfold _root_.GlobalTheory.Katz.at2
    have ha : ∀ j : Fin d ⊕ Fin d,
        constantCoeff (Sum.elim (_root_.GlobalTheory.QLog.nmul μ k) (fun j => (X j : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact ih j
      · simp
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha (hμ i)

open MvPowerSeries in
set_option autoImplicit false in
private theorem hasVal_zero_of_constantCoeff_eq_zero {p : ℕ} {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ}
    {f : MvPowerSeries (Fin d) Q} (hf : constantCoeff f = 0) :
    _root_.GlobalTheory.QLog.HasVal p (fun _ : Fin d => (0 : B)) f 0 := by
  intro m
  refine ⟨0, fun N _ => ⟨0, ?_⟩⟩
  have h0 : (fun i : Fin d => (algebraMap B Q) ((fun _ : Fin d => (0 : B)) i)) = 0 := by
    funext i; simp
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at hf
  rw [h0, MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq, MvPowerSeries.coeff_trunc']
  simp [hf]

open MvPowerSeries in
set_option autoImplicit false in

theorem _root_.GlobalTheory.QLogPeriod.hasPeriod_hodgeTate : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : _root_.GlobalTheory.PDivGroup p O) (d : ℕ) (c : _root_.GlobalTheory.QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], _root_.GlobalTheory.QLog.IsFrame p E (RingHom.id O) → ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), _root_.GlobalTheory.QLog.QL c.μ ⊤ f → c.IsLie f l → ∀ t : G.Tate, c.HasPeriod (RingHom.id O) t f (l (G.hodgeTate t)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF f l hQL hLie t
  have hF' := hF
  obtain ⟨-, hinj, -, hpunit, -, -, -, -⟩ := hF'
  rw [c.hasPeriod_iff hF]
  intro n z hz
  obtain ⟨s, hs, hsl⟩ := (c.isLie_iff hinj f l).1 hLie n
  obtain ⟨b₀, hb₀⟩ := hsl (G.hodgeTate t) (WithConv.toConv (t.pt n).toLinearMap)
    (G.hodgeTate_val t n).symm
  have hz' : ∀ i, z i = (t.pt n) (c.x n i) := hz
  have hznil : ∀ i, ∃ N, (p : O) ∣ z i ^ N := by
    intro i
    obtain ⟨N, a, ha⟩ := c.5 n i
    exact ⟨N, (t.pt n) a, by rw [hz', ← map_pow, ha, map_mul, map_natCast]⟩
  let Ez : MvPowerSeries (Fin d) O →ₐ[O] O := (t.pt n).comp (c.ev n)
  have hEz : _root_.GlobalTheory.QLog.IsEval p z Ez := by
    obtain ⟨hX, hc⟩ := c.6 n
    refine ⟨fun i => ?_, fun m => ?_⟩
    · simp [Ez, hX, hz']
    · obtain ⟨N, hN⟩ := hc m
      refine ⟨N, fun g hg => ?_⟩
      obtain ⟨a, ha⟩ := hN g hg
      exact ⟨(t.pt n) a, by simp [Ez, ha, map_mul, map_pow, map_natCast]⟩
  have hval_s := _root_.GlobalTheory.hasVal_map_of_isEval p O O E (RingHom.id O) hF
    (Fin d) z hznil Ez hEz s
  rw [hs] at hval_s
  have hdiff : _root_.GlobalTheory.QLog.DIn (B := O) ⊤ f := dIn_univ_of_QL_of_isLaw c.12 hQL
  have hu0 : ∀ j, constantCoeff (_root_.GlobalTheory.QLog.nmul c.μ (p ^ n) j) = 0 :=
    constantCoeff_nmul_eq_zero c.12.1 (p ^ n)
  have hEu : (fun j => Ez (_root_.GlobalTheory.QLog.nmul c.μ (p ^ n) j)) = fun _ => (0 : O) := by
    funext j
    simp only [Ez, AlgHom.comp_apply]
    rw [_root_.GlobalTheory.NMul.ev_nmul p C v O hv G d c n (p ^ n) j, G.mulBy_pow_self,
      c.9 n j, map_zero, map_zero]
  have hval_sub := _root_.GlobalTheory.QLog.hasVal_subst p O O E (RingHom.id O) hF (Fin d) z hznil
    Ez hEz (Fin d) (_root_.GlobalTheory.QLog.nmul c.μ (p ^ n)) f 0 hu0 hdiff
    (by rw [hEu]; exact hasVal_zero_of_constantCoeff_eq_zero hQL.1)
  have hsum := (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p O O E (RingHom.id O) hF (Fin d) z _ _ _ _
    hval_s).1 hval_sub
  set u := (hpunit.pow n).unit with hu
  have hsm := (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p O O E (RingHom.id O) hF (Fin d) z _ 0 _ 0
    hsum).2.1 (↑u⁻¹ : E)
  have hpu : ((p : E)) ^ n = ↑u := (IsUnit.unit_spec _).symm
  have hser : (↑u⁻¹ : E) • (_root_.GlobalTheory.QLog.defect c.μ (p ^ n) f +
      subst (_root_.GlobalTheory.QLog.up E (_root_.GlobalTheory.QLog.nmul c.μ (p ^ n))) f) = f := by
    unfold _root_.GlobalTheory.QLog.defect
    rw [sub_add_cancel, smul_smul]
    have hcast : (((p ^ n : ℕ)) : E) = ↑u := by rw [← hpu]; push_cast; rfl
    rw [hcast, Units.inv_mul, one_smul]
  rw [hser] at hsm
  refine ⟨_, hsm, -b₀, ?_⟩
  have hE : Ez s = l (G.hodgeTate t) + (p : O) ^ n * -b₀ := by
    have h : Ez s = (WithConv.toConv (t.pt n).toLinearMap).ofConv ((c.ev n) s) := rfl
    rw [h]
    linear_combination -hb₀
  rw [← hE, add_zero, ← mul_assoc, hpu, Units.mul_inv, one_mul]

end GlobalTheory.QLogPeriod
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_period_eq_tangent_hodgeTate : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), QL c.μ ⊤ f → c.IsLie f l → ∀ t : G.Tate, c.HasPeriod (RingHom.id O) t f (l (hodgeTate G t)) := by
  atlas_forward_decl GlobalTheory.QLogPeriod.hasPeriod_hodgeTate
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftLaw

def cmap {σ R S : Type} [CommRing R] [CommRing S] (g : R → S) (f : MvPowerSeries σ R) : MvPowerSeries σ S :=
  fun α => g (coeff α f)

theorem coeff_cmap {σ R S : Type} [CommRing R] [CommRing S] (g : R → S) (f : MvPowerSeries σ R) (α : σ →₀ ℕ) :
    coeff α (cmap g f) = g (coeff α f) := rfl

theorem swap_cmap {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (g : R → S)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) : swap (cmap g c) = cmap g (swap c) := by
  ext α
  obtain ⟨⟨a, e⟩, rfl⟩ := (Finsupp.sumFinsuppEquivProdFinsupp : (Fin d ⊕ Fin d →₀ ℕ) ≃ (Fin d →₀ ℕ) × (Fin d →₀ ℕ)).symm.surjective α
  have h : (Finsupp.sumFinsuppEquivProdFinsupp : (Fin d ⊕ Fin d →₀ ℕ) ≃ (Fin d →₀ ℕ) × (Fin d →₀ ℕ)).symm (a, e) = Finsupp.sumElim a e := rfl
  rw [h, coeff_cmap, SwapCoeff.coeff_swap, SwapCoeff.coeff_swap, coeff_cmap]

theorem coeff_subst_elim_zero {R : Type} [CommRing R] {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (β : Fin d →₀ ℕ) :
    coeff β (subst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun (_ : Fin d) => 0) c) =
      coeff (Finsupp.embDomain (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d) β) c := by
  classical
  have ha : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun (_ : Fin d) => 0) :=
    hasSubst_of_constantCoeff_zero fun s => by rcases s with i | i <;> simp
  have hb : HasSubst (X ∘ (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d) :
      Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) :=
    hasSubst_of_constantCoeff_zero fun s => by simp
  have hr : rename (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d)
      (subst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun (_ : Fin d) => 0) c) =
      subst (fun s : Fin d ⊕ Fin d => if s.isLeft then (X s : MvPowerSeries (Fin d ⊕ Fin d) R) else 0) c := by
    rw [rename_eq_subst, subst_comp_subst_apply ha hb]
    congr 1
    funext s
    rcases s with i | i
    · simp [subst_X hb]
    · simp only [Sum.elim_inr, Sum.isLeft_inr]
      rw [← coe_substAlgHom hb, map_zero]
      rfl
  rw [← coeff_embDomain_rename (Function.Embedding.inl : Fin d ↪ Fin d ⊕ Fin d), hr,
    OnePair.coeff_subst_kill]
  rw [if_pos]
  rintro (i | i) hi
  · simp at hi
  · simp [Finsupp.embDomain_apply]

theorem exists_isLift : ∀ (B O : Type) [CommRing B] [CommRing O] (θ : B →+* O), Function.Surjective θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∃ μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B, IsLift θ μ' ∧ ∀ i, map θ (μ' i) = μ i := by
  intro B O _ _ θ hθ d μ hμ
  classical
  by_cases h1 : (1 : O) = 0
  ·
    haveI : Subsingleton O := subsingleton_of_zero_eq_one h1.symm
    have hm : ∀ i, map θ (addLaw B d i) = μ i := fun i => by
      ext α
      exact Subsingleton.elim _ _
    have ha : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) B)) fun (_ : Fin d) => 0) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with i | i <;> simp
    have hs : HasSubst (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) B))
        fun i => X (Sum.inl i)) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with i | i <;> simp
    refine ⟨addLaw B d, ⟨fun i => by simp [addLaw], ?_, fun i => ?_, ?_⟩, hm⟩
    · funext i
      simp only [op, at2, addLaw]
      rw [subst_add ha, subst_X ha, subst_X ha]
      simp
    · simp only [swap, at2, addLaw]
      rw [subst_add hs, subst_X hs, subst_X hs]
      simp [add_comm]
    · have : (fun i => map θ (addLaw B d i)) = μ := funext hm
      rw [this]
      exact hμ
  ·
    let s : O → B := fun x => if x = 0 then 0 else if x = 1 then 1 else (hθ x).choose
    have hs : ∀ x, θ (s x) = x := fun x => by
      simp only [s]
      split_ifs with h h'
      · rw [map_zero, h]
      · rw [map_one, h']
      · exact (hθ x).choose_spec
    have hs0 : s 0 = 0 := by simp [s]
    have hs1 : s 1 = 1 := by simp [s, h1]
    refine ⟨fun i => cmap s (μ i), ⟨fun i => ?_, ?_, fun i => ?_, ?_⟩, fun i => ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_cmap, coeff_zero_eq_constantCoeff_apply,
        hμ.const i, hs0]
    · funext i
      ext β
      have hu := congrArg (coeff β) (congrFun hμ.unit i)
      simp only [op, at2] at hu ⊢
      rw [coeff_subst_elim_zero] at hu ⊢
      rw [coeff_cmap, hu, coeff_X, coeff_X]
      split_ifs
      · exact hs1
      · exact hs0
    · rw [swap_cmap, hμ.comm i]
    · have : (fun i => map θ (cmap s (μ i))) = μ := funext fun i => by
        ext α
        rw [coeff_map, coeff_cmap, hs]
      rw [this]
      exact hμ
    · ext α
      rw [coeff_map, coeff_cmap, hs]

end GlobalTheory.LiftLaw
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalGroupLawLift_of_surjective : ∀ (B O : Type) [CommRing B] [CommRing O] (θ : B →+* O), Function.Surjective θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∃ μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B, IsLift θ μ' ∧ ∀ i, map θ (μ' i) = μ i := by
  atlas_forward_decl GlobalTheory.LiftLaw.exists_isLift
end

section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_quasiLogarithm_along_pdThickening : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ Θ : Q →+* C, (∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b)) → ∀ (g : MvPowerSeries (Fin d) C) (w : Fin d → B), QL (fun i => map θ (μ i)) ⊤ g → (∀ i, lin g i = algebraMap O C (θ (w i))) → ∃ f : MvPowerSeries (Fin d) Q, QL μ ⊤ f ∧ map Θ f = g ∧ ∀ i, lin f i = algebraMap B Q (w i) := by
  first | exact @GlobalTheory.QLog.KLift.lift_quasiLog | exact GlobalTheory.QLog.KLift.lift_quasiLog | (intros; apply GlobalTheory.QLog.KLift.lift_quasiLog <;> assumption)
end

section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_basis_lift_pdThickening : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ Θ : Q →+* C, (∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b)) → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → IsBasis (fun i => map θ (μ i)) (fun i => map Θ (e i)) → Relation.ReflTransGen (fun N N' : Ideal B => IsStep p θ N' N) ⊤ (Ideal.span {(p : B)}) → IsBasis μ e := by
  first | exact @GlobalTheory.basis_lift | exact GlobalTheory.basis_lift | (intros; apply GlobalTheory.basis_lift <;> assumption)
end

section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainfSquareZeroFrame_reflTransGen_cyclic_chain : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, Relation.ReflTransGen (fun N N' : Ideal F.B => IsStep p F.θ N' N) ⊤ (Ideal.span {(p : F.B)}) := by
  first | exact @GlobalTheory.BChain.reflTransGen_isStep | exact GlobalTheory.BChain.reflTransGen_isStep | (intros; apply GlobalTheory.BChain.reflTransGen_isStep <;> assumption)
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.LiftBasis

theorem exists_lift_isAdapted : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → ∀ (k : ℕ) (e0 : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C), IsBasis c.μ e0 → IsAdapted (RingHom.id O) c.μ e0 → ∃ e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q, (∀ l, map Θ (e l) = e0 l) ∧ IsBasis μ' e ∧ IsAdapted F.θ μ' e := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hμ' hμ Θ hΘ k e0 hB hA
  have hC : IsFrame p C (RingHom.id O) := GlobalTheory.T.isTorsionFreePDThickeningFrame_valuation_integers p C v O hv
  have hF : IsFrame p F.Q F.θ := F.frame
  have hμf : (fun i => map F.θ (μ' i)) = c.μ := funext hμ

  have hw : ∀ l, ∃ w : Fin d → F.B, (∀ i, lin (e0 l) i = algebraMap O C (F.θ (w i))) ∧
      ∀ j, l = Sum.inl j → w = Pi.single j 1 := by
    intro l
    cases l with
    | inl j =>
      refine ⟨Pi.single j 1, fun i => ?_, fun j' h => by cases h; rfl⟩
      rw [(hA j).2]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    | inr j =>
      refine ⟨fun i => Classical.choose (hF.surj (Classical.choose ((hB.1 (Sum.inr j)).2.1 i))),
        fun i => ?_, fun j' h => by cases h⟩
      rw [Classical.choose_spec (hF.surj _)]
      exact (Classical.choose_spec ((hB.1 (Sum.inr j)).2.1 i)).2
  choose w hw1 hw2 using hw
  have hlift : ∀ l, ∃ f : MvPowerSeries (Fin d) F.Q, QL μ' ⊤ f ∧ map Θ f = e0 l ∧
      ∀ i, lin f i = algebraMap F.B F.Q (w l i) := by
    intro l
    refine GlobalTheory.T.lift_quasiLogarithm_along_pdThickening p F.B O F.Q F.θ hF d μ' hμ' C hC Θ hΘ (e0 l) (w l) ?_ (hw1 l)
    rw [hμf]; exact hB.1 l
  choose e he1 he2 he3 using hlift
  refine ⟨e, he2, ?_, ?_⟩
  · refine GlobalTheory.T.quasiLogarithm_basis_lift_pdThickening p F.B O F.Q F.θ hF d μ' hμ' C hC Θ hΘ (Fin d ⊕ Fin k) e he1 ?_
      (GlobalTheory.T.ainfSquareZeroFrame_reflTransGen_cyclic_chain p C v O hv ε hε F)
    rw [hμf]
    have : (fun i => map Θ (e i)) = e0 := funext he2
    rw [this]; exact hB
  · intro i
    refine ⟨fun α => ?_, ?_⟩
    · obtain ⟨b, -, eb⟩ := (he1 (Sum.inl i)).2.2 α
      refine ⟨b, RingHom.mem_ker.2 ?_, eb⟩
      obtain ⟨b', hb', eb'⟩ := (hA i).1 α
      have hb0 : b' = 0 := RingHom.mem_ker.1 hb'
      have hup : up C c.μ = fun j => map Θ (up F.Q μ' j) :=
        funext (WindowMat.up_map F.θ Θ hΘ hμ)
      have key : algebraMap O C (F.θ b) = 0 := by
        rw [← hΘ, ← eb, ← coeff_map, Window.map_formalGroupLawCoboundaryOne_eq Θ _ (Window.constantCoeff_up hμ'.const),
          ← hup, he2, eb', hb0, map_zero]
      exact hC.inj (by rw [key, map_zero])
    · funext j
      rw [he3, hw2 _ i rfl]
      by_cases hij : j = i
      · subst hij; simp
      · simp [Pi.single_apply, hij]

end GlobalTheory.QLog.LiftBasis
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_adapted_basis_quasi_logarithms_frame : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → ∀ (k : ℕ) (e0 : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C), IsBasis c.μ e0 → IsAdapted (RingHom.id O) c.μ e0 → ∃ e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q, (∀ l, map Θ (e l) = e0 l) ∧ IsBasis μ' e ∧ IsAdapted F.θ μ' e := by
  atlas_forward_decl GlobalTheory.QLog.LiftBasis.exists_lift_isAdapted
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieZero

theorem eq_zero_of_pow_dvd {O : Type} [CommRing O] {p : O} [IsHausdorff (Ideal.span {p}) O] (x : O)
    (h : ∀ n : ℕ, p ^ n ∣ x) : x = 0 := by
  refine IsHausdorff.haus (I := Ideal.span {p}) ‹_› x fun n => ?_
  rw [SModEq.sub_mem, sub_zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  exact Ideal.mem_span_singleton.2 (h n)

variable {R : Type} [CommRing R] {d : ℕ}

theorem nmul_succ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (n : ℕ) :
    nmul μ (n + 1) = op μ (nmul μ n) (fun k => X k) := by
  unfold nmul
  rw [Function.iterate_succ_apply']

theorem constantCoeff_nmul (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (i : Fin d) : constantCoeff (nmul μ n i) = 0 := by
  induction n generalizing i with
  | zero => simp [nmul]
  | succ n ih =>
    have hb : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun k => (X k : MvPowerSeries (Fin d) R)) j)
        = 0 := by
      rintro (j | j)
      · exact ih j
      · simp
    rw [nmul_succ]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hb) hb (hμ i)

theorem subst_eq_add_of_cob1_eq_zero {E : Type} [CommRing E] (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) E)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) E) (hf : cob1 μ f = 0)
    {τ : Type} (b : Fin d ⊕ Fin d → MvPowerSeries τ E) (hb : HasSubst b) :
    subst (fun i => subst b (μ i)) f = subst (fun i => b (Sum.inl i)) f + subst (fun i => b (Sum.inr i)) f := by
  have hμs : HasSubst μ := hasSubst_of_constantCoeff_zero hμ
  have hL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) E)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) E)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have h := congrArg (subst b) hf
  unfold cob1 inL inR at h
  rw [subst_sub hb, subst_sub hb, subst_comp_subst_apply hμs hb,
    subst_comp_subst_apply hL hb, subst_comp_subst_apply hR hb, ← coe_substAlgHom hb, map_zero,
    coe_substAlgHom hb] at h
  simp only [subst_X hb] at h
  rw [← sub_eq_zero, ← h, sub_sub]

theorem subst_nmul_of_cob1_eq_zero {O E : Type} [CommRing O] [CommRing E] [Algebra O E]
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) E) (hf : cob1 (up E μ) f = 0) (m : ℕ) :
    subst (up E (nmul μ m)) f = (m : E) • f := by
  have hμ' : ∀ i, constantCoeff (up E μ i) = 0 := fun i => by
    simp [up, constantCoeff_map, hμ i]
  induction m with
  | zero =>
    have h0 : up E (nmul μ 0) = (0 : Fin d → MvPowerSeries (Fin d) E) := by
      funext i; simp [up, nmul]
    rw [h0, Nat.cast_zero, zero_smul]
    have h := subst_eq_add_of_cob1_eq_zero (up E μ) hμ' f hf (0 : Fin d ⊕ Fin d → MvPowerSeries (Fin d) E)
      HasSubst.zero
    have h1 : (fun i => subst (0 : Fin d ⊕ Fin d → MvPowerSeries (Fin d) E) (up E μ i)) = 0 := by
      funext i; exact subst_zero_of_constantCoeff_zero (hμ' i)
    rw [h1] at h
    have h2 : (fun i : Fin d => (0 : Fin d ⊕ Fin d → MvPowerSeries (Fin d) E) (Sum.inl i)) = 0 := rfl
    have h3 : (fun i : Fin d => (0 : Fin d ⊕ Fin d → MvPowerSeries (Fin d) E) (Sum.inr i)) = 0 := rfl
    rw [h2, h3] at h
    linear_combination -h
  | succ m ih =>
    have hc : ∀ j, constantCoeff (Sum.elim (nmul μ m) (fun k => (X k : MvPowerSeries (Fin d) O)) j)
        = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul μ hμ m j
      · simp
    have hc' : ∀ j, constantCoeff (Sum.elim (up E (nmul μ m))
        (fun k => (X k : MvPowerSeries (Fin d) E)) j) = 0 := by
      rintro (j | j)
      · simp [up, constantCoeff_map, constantCoeff_nmul μ hμ m j]
      · simp
    have hs : up E (nmul μ (m + 1)) = fun i => subst (Sum.elim (up E (nmul μ m))
        (fun k => (X k : MvPowerSeries (Fin d) E))) (up E μ i) := by
      funext i
      simp only [up, nmul_succ, op, at2]
      rw [map_subst (hasSubst_of_constantCoeff_zero hc)]
      congr 1
      funext j
      rcases j with j | j <;> simp [up]
    rw [hs, subst_eq_add_of_cob1_eq_zero (up E μ) hμ' f hf _ (hasSubst_of_constantCoeff_zero hc')]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [ih, show (subst (fun k => (X k : MvPowerSeries (Fin d) E)) f) = f from
      congrFun (subst_self (R := E) (σ := Fin d)) f]
    push_cast
    rw [add_smul, one_smul]

theorem lie_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E],
    IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d),
    ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), c.IsLie f l →
    (In (⊤ : Ideal O) f → constantCoeff f = 0 → l = 0) ∧ (cob1 (up E c.μ) f = 0 → l = 0) := by
  intro p _ O E _ _ _ hF G d c f l hl
  haveI : IsAdicComplete (Ideal.span {(p : O)}) O := hF.complete
  unfold Chart.IsLie at hl
  have key : (∀ n, ∃ s : MvPowerSeries (Fin d) O, MvPowerSeries.map (algebraMap O E) s =
      defect c.μ (p ^ n) f ∧ ∃ z, c.ev n s = (p : O) ^ n • z) → l = 0 := by
    intro H
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.zero_apply]
    refine eq_zero_of_pow_dvd (p := (p : O)) _ fun n => ?_
    obtain ⟨s, hs, z, hz⟩ := H n
    obtain ⟨φ, hφ⟩ := (T.dvd_of_forall_invariantDifferential_dvd p O G n 1 0 (fun _ _ _ => one_dvd _)).2 w
    have h1 := hl.2 n w φ s hφ hs
    have h2 : (p : O) ^ n ∣ φ (c.ev n s) := by
      rw [hz]
      simp
    simpa using dvd_add h1 h2
  refine ⟨fun hIn hc0 => key fun n => ?_, fun hcob => key fun n => ?_⟩
  · choose g hg using hIn
    let s0 : MvPowerSeries (Fin d) O := fun α => g α
    have hs0 : MvPowerSeries.map (algebraMap O E) s0 = f := by
      ext α
      rw [coeff_map, (hg α).2]
      rfl
    have hc : constantCoeff s0 = 0 := by
      apply hF.inj
      rw [map_zero, ← constantCoeff_map, hs0, hc0]
    have hsub : HasSubst (nmul c.μ (p ^ n)) :=
      hasSubst_of_constantCoeff_zero (constantCoeff_nmul c.μ c.isLaw.const _)
    refine ⟨(p ^ n) • s0 - subst (nmul c.μ (p ^ n)) s0, ?_, c.ev n s0, ?_⟩
    · rw [map_sub, map_nsmul, map_subst hsub, hs0]
      unfold defect
      rw [Nat.cast_smul_eq_nsmul]
      rfl
    · rw [map_sub, map_nsmul, (T.ev_subst_natMultiple_prime_pow_constant p O G d c n).1 s0, hc, map_zero, sub_zero,
        ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
  · refine ⟨0, ?_, 0, ?_⟩
    · unfold defect
      rw [subst_nmul_of_cob1_eq_zero c.μ c.isLaw.const f hcob, sub_self, map_zero]
    · simp

end GlobalTheory.LieZero
end
end

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory.QLog

theorem defect_sum {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0) (m : ℕ)
    {ι : Type} [Fintype ι] (a : ι → E) (f : ι → MvPowerSeries (Fin d) E) :
    defect μ m (∑ i, a i • f i) = ∑ i, a i • defect μ m (f i) := by
  simp only [defect, ← coe_substAlgHom (hasSubst_up_nmul (Q := E) hμ m), map_sum, map_smul,
    Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem map_sum_smul {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {σ : Type}
    {ι : Type} [Fintype ι] (b : ι → O) (s : ι → MvPowerSeries σ O) :
    map (algebraMap O E) (∑ i, b i • s i) = ∑ i, algebraMap O E (b i) • map (algebraMap O E) (s i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext α
  rw [coeff_map, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, coeff_map]
  simp only [smul_eq_mul, map_mul]

theorem Chart.isLie_comb : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) E) (l : ι → G.dual.Lie) (b : ι → O), (∀ i, QL c.μ ⊤ (e i)) → (∀ i, c.IsLie (e i) (l i)) → c.IsLie (comb b e) (∑ i, b i • l i) := by
  intro p _ O E _ _ _ hF G d c ι _ e l b _ hl
  have hinj : Function.Injective (algebraMap O E) := hF.inj
  rw [c.isLie_iff hinj]
  intro n
  choose s hs hc using fun i => (c.isLie_iff hinj _ _).1 (hl i) n
  refine ⟨∑ i, b i • s i, ?_, fun w φ hφ => ?_⟩
  · rw [map_sum_smul, comb, defect_sum c.isLaw.const]
    exact Finset.sum_congr rfl fun i _ => by rw [hs i]
  · have : (∑ i, b i • l i) w - φ (c.ev n (∑ i, b i • s i)) =
        ∑ i, b i * (l i w - φ (c.ev n (s i))) := by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
        smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    rw [this]
    exact Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right (hc i w φ hφ) _

end GlobalTheory.QLog
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.RedO

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (k : ℕ) (e0 : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C) (lb : Module.Basis (Fin k) O G.dual.Lie), IsBasis c.μ e0 → IsAdapted (RingHom.id O) c.μ e0 → (∀ j, c.IsLie (e0 (Sum.inr j)) (lb j)) → ∀ h : MvPowerSeries (Fin d) C, QL c.μ ⊤ h → cob1 (up C c.μ) h = 0 → ∀ a : Fin d ⊕ Fin k → O, In (⊤ : Ideal O) (h - comb a e0) → (∀ j, a (Sum.inr j) = 0) ∧ ∀ i, lin h i = algebraMap O C (a (Sum.inl i)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c k e0 lb hB hA hL h hh hcob a ha
  have hF : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  have hμ : ∀ i, constantCoeff (up C c.μ i) = 0 := fun i => by
    simp [up, constantCoeff_map, c.isLaw.const i]

  have lie0 : ∀ f : MvPowerSeries (Fin d) C, cob1 (up C c.μ) f = 0 → c.IsLie f 0 := by
    intro f hf
    have hd : ∀ n : ℕ, defect c.μ (p ^ n) f = defect c.μ (p ^ n) (0 : MvPowerSeries (Fin d) C) := fun n => by
      rw [defect, GlobalTheory.LieZero.subst_nmul_of_cob1_eq_zero c.μ c.isLaw.const f hf, sub_self, defect,
        ← coe_substAlgHom (hasSubst_up_nmul c.isLaw.const _), map_zero, smul_zero, sub_zero]
    have e : c.IsLie f 0 ↔ c.IsLie (0 : MvPowerSeries (Fin d) C) 0 := by
      unfold Chart.IsLie
      simp only [hd]
    exact e.2 (c.isLie_zero hv.hom_inj)

  have hcobE : ∀ i, cob1 (up C c.μ) (e0 (Sum.inl i)) = 0 := fun i => by
    ext α
    obtain ⟨b, hb, hb'⟩ := (hA i).1 α
    rw [RingHom.mem_ker, RingHom.id_apply] at hb
    rw [hb', hb, map_zero, map_zero]
  let L : Fin d ⊕ Fin k → G.dual.Lie := Sum.elim (fun _ => 0) lb
  have hLe : ∀ x, c.IsLie (e0 x) (L x) := by
    rintro (i | j)
    · exact lie0 _ (hcobE i)
    · exact hL j

  let e' : Unit ⊕ (Fin d ⊕ Fin k) → MvPowerSeries (Fin d) C := Sum.elim (fun _ => h) e0
  let b' : Unit ⊕ (Fin d ⊕ Fin k) → O := Sum.elim (fun _ => 1) (-a)
  have hcomb : comb b' e' = h - comb a e0 := by
    simp only [comb, Fintype.sum_sum_type, e', b', Sum.elim_inl, Sum.elim_inr, Pi.neg_apply,
      map_neg, neg_smul, Finset.sum_neg_distrib, map_one, one_smul, Finset.univ_unique,
      Finset.sum_singleton]
    abel
  have hQL : ∀ x, QL c.μ ⊤ (e' x) := by
    rintro (_ | x)
    · exact hh
    · exact hB.1 x
  have hLie' : ∀ x, c.IsLie (e' x) (Sum.elim (fun _ => (0 : G.dual.Lie)) L x) := by
    rintro (_ | x)
    · exact lie0 h hcob
    · exact hLe x
  have hs := GlobalTheory.QLog.Chart.isLie_comb p O C hF G d c _ e' _ b' hQL hLie'
  rw [hcomb] at hs
  have hc0 : constantCoeff (h - comb a e0) = 0 := by
    rw [map_sub, hh.1, comb, map_sum]
    simp [← coeff_zero_eq_constantCoeff_apply, coeff_smul,
      coeff_zero_eq_constantCoeff_apply, (hB.1 _).1]
  have hl0 := (GlobalTheory.LieZero.lie_eq_zero p O C hF G d c _ _ hs).1 ha hc0
  simp only [Fintype.sum_sum_type, b', Sum.elim_inl, Sum.elim_inr, smul_zero, Finset.sum_const_zero,
    zero_add, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, neg_eq_zero, L] at hl0
  have hinr : ∀ j, a (Sum.inr j) = 0 :=
    Fintype.linearIndependent_iff.1 lb.linearIndependent (fun j => a (Sum.inr j)) hl0
  refine ⟨hinr, fun i => ?_⟩

  have hcobc : cob1 (up C c.μ) (h - comb a e0) = 0 := by
    have hadd : ∀ f g, cob1 (up C c.μ) (f + g) = cob1 (up C c.μ) f + cob1 (up C c.μ) g :=
      formalCoboundary_add hμ
    let Φ : MvPowerSeries (Fin d) C →+ MvPowerSeries (Fin d ⊕ Fin d) C :=
      AddMonoidHom.mk' (cob1 (up C c.μ)) hadd
    have e1 : cob1 (up C c.μ) (comb a e0) = 0 := by
      change Φ (comb a e0) = 0
      rw [comb, map_sum]
      refine Finset.sum_eq_zero fun x _ => ?_
      change cob1 (up C c.μ) (algebraMap O C (a x) • e0 x) = 0
      rw [formalCoboundary_smul hμ]
      rcases x with i' | j
      · rw [hcobE i', smul_zero]
      · rw [hinr j, map_zero, zero_smul]
    rw [sub_eq_add_neg, ← neg_one_smul C (comb a e0), hadd, formalCoboundary_smul hμ, e1, smul_zero, hcob,
      add_zero]
  obtain ⟨s, hs'⟩ := In.top_iff.1 ha
  have hs0 : s = 0 :=
    GlobalTheory.QLog.IntAdd.eq_zero_of_cob1_eq_zero p C v O hv G d c C hF s (by rw [hs']; exact hcobc)
  rw [hs0, map_zero] at hs'
  have hEq : h = comb a e0 := sub_eq_zero.1 hs'.symm
  rw [hEq]
  simp only [lin, comb, Fintype.sum_sum_type, map_add, map_sum, coeff_smul, smul_eq_mul]
  have h2 : ∀ j, algebraMap O C (a (Sum.inr j)) * coeff (Finsupp.single i 1) (e0 (Sum.inr j)) = 0 :=
    fun j => by rw [hinr j, map_zero, zero_mul]
  have h1 : ∀ i', coeff (Finsupp.single i 1) (e0 (Sum.inl i')) = (Pi.single i' (1 : C) : Fin d → C) i :=
    fun i' => congrFun (hA i').2 i
  simp only [h2, h1, Finset.sum_const_zero, add_zero, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end GlobalTheory.QLog.RedO
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logarithm_integers_adapted_basis_no_lie_components : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (k : ℕ) (e0 : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C) (lb : Module.Basis (Fin k) O G.dual.Lie), IsBasis c.μ e0 → IsAdapted (RingHom.id O) c.μ e0 → (∀ j, c.IsLie (e0 (Sum.inr j)) (lb j)) → ∀ h : MvPowerSeries (Fin d) C, QL c.μ ⊤ h → cob1 (up C c.μ) h = 0 → ∀ a : Fin d ⊕ Fin k → O, In (⊤ : Ideal O) (h - comb a e0) → (∀ j, a (Sum.inr j) = 0) ∧ ∀ i, lin h i = algebraMap O C (a (Sum.inl i)) := by
  atlas_forward_decl GlobalTheory.QLog.RedO.main
end

section
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.LieAdd

variable {R : Type} [CommRing R] {d : ℕ}

theorem subst_zero_of_constantCoeff {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    subst (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) f = 0 := by
  have ha : HasSubst (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  ext e
  rw [coeff_subst ha, map_zero]
  refine finsum_eq_zero_of_forall_eq_zero fun a => ?_
  by_cases h : a = 0
  · subst h
    rw [coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨s, hs⟩ := Finsupp.ne_iff.1 h
    have : (a.prod fun _ k => (0 : MvPowerSeries (Fin d) R) ^ k) = 0 :=
      Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.2 (by simpa using hs))
        (zero_pow (by simpa using hs))
    rw [this, map_zero, smul_zero]

theorem constantCoeff_nmul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (i : Fin d) : constantCoeff (nmul μ n i) = 0 := by
  induction n generalizing i with
  | zero => simp [nmul]
  | succ n ih =>
    rw [nmul, Function.iterate_succ_apply', ← nmul, op, at2]
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
        (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j) <;> simp [ih]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)

theorem subst_nmul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) {f : MvPowerSeries (Fin d) R} (hf0 : constantCoeff f = 0)
    (hf : cob1 μ f = 0) (n : ℕ) : subst (nmul μ n) f = (n : R) • f := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_smul]
    exact subst_zero_of_constantCoeff hf0
  | succ n ih =>
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
        (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j) <;> simp [constantCoeff_nmul hμ]
    have hb := hasSubst_of_constantCoeff_zero hs
    have hm : nmul μ (n + 1) = fun i => subst (Sum.elim (nmul μ n) fun i => X i) (μ i) := by
      rw [nmul, Function.iterate_succ_apply', ← nmul]; rfl
    have hc : subst μ f = inL f + inR f := by
      rw [cob1, sub_sub, sub_eq_zero] at hf; exact hf
    have hl0 : ∀ i, constantCoeff (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
      fun _ => constantCoeff_X _
    have hr0 : ∀ i, constantCoeff (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
      fun _ => constantCoeff_X _
    rw [hm, ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hμ) hb, hc,
      subst_add hb, inL, inR,
      subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hl0) hb,
      subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hr0) hb]
    simp only [subst_X hb, Sum.elim_inl, Sum.elim_inr]
    rw [ih, subst_self, id, Nat.cast_succ, add_smul, one_smul]

theorem nmul_succ {S : Type} [CommRing S] (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S) (n : ℕ) :
    nmul μ (n + 1) = op μ (nmul μ n) fun i => X i := by
  rw [nmul, Function.iterate_succ_apply', ← nmul]

theorem up_nmul {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    up Q (nmul μ n) = nmul (up Q μ) n := by
  induction n with
  | zero => funext i; simp [up, nmul]
  | succ n ih =>
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
        (fun i => (X i : MvPowerSeries (Fin d) B)) j) = 0 := by
      rintro (j | j) <;> simp [constantCoeff_nmul hμ]
    funext i
    rw [nmul_succ, nmul_succ, ← ih]
    simp only [up, op, at2]
    rw [map_subst (hasSubst_of_constantCoeff_zero hs)]
    congr 1
    funext j
    rcases j with j | j <;> simp [map_X, up]

end GlobalTheory.QLog.LieAdd

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem Chart.isLie_zero_of_cob1_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (f : MvPowerSeries (Fin d) C),
    constantCoeff f = 0 → cob1 (up C c.μ) f = 0 → c.IsLie f 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c f hf0 hf
  have hμ := c.isLaw.const
  have hμC : ∀ i, constantCoeff (up C c.μ i) = 0 := fun i => by
    rw [up, constantCoeff_map, hμ, map_zero]
  refine (c.isLie_iff hv.hom_inj f 0).2 fun n => ⟨0, ?_, fun w φ _ => by simp⟩
  rw [map_zero, defect, LieAdd.up_nmul hμ, LieAdd.subst_nmul hμC hf0 hf, sub_self]

end GlobalTheory.QLog
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_eq_zero_of_formalGroupLawCoboundaryOne_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (f : MvPowerSeries (Fin d) C), constantCoeff f = 0 → cob1 (up C c.μ) f = 0 → c.IsLie f 0 := by
  atlas_forward_decl GlobalTheory.QLog.Chart.isLie_zero_of_cob1_eq_zero
end

section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open GlobalTheory.QLog.Window

namespace GlobalTheory.QLog.WindowMat

section Frame

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O) {ε : PreTilt O p}
  (hε : IsPrimitiveSystem ε) (F : BFrame ε) {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)
  {μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B} (hL : IsLift F.θ μ')
  (hμ : ∀ i, map F.θ (μ' i) = c.μ i)
include hv hε hL hμ

theorem hasPeriod_add_smul (t : G.Tate) {f g : MvPowerSeries (Fin d) F.Q} {y y' : F.B} (b : F.B)
    (hg : DIn (⊤ : Ideal F.B) g) (h1 : c.HasPeriod F.θ t f y) (h2 : c.HasPeriod F.θ t g y') :
    c.HasPeriod F.θ t (f + algebraMap F.B F.Q b • g) (y + b * y') := by
  first
  | exact (GlobalTheory.T.formalChart_hasPeriod_linear_integral p C v O hv ε hε F G d c μ' hL hμ f g t y y' b hg h1 h2).1
  | exact (GlobalTheory.T.formalChart_hasPeriod_linear_integral p C v O hv ε hε F G d c μ' hL hμ f g t y y' b h1 h2).1

theorem hasPeriod_map_zero (t : G.Tate) (s : MvPowerSeries (Fin d) F.B) (hs : constantCoeff s = 0) :
    c.HasPeriod F.θ t (map (algebraMap F.B F.Q) s) 0 := by
  have hz := hasPeriod_zero c F.frame t
  have hd : DIn (⊤ : Ideal F.B) (0 : MvPowerSeries (Fin d) F.Q) := din_of_in (in_zero ⊤)
  first
  | exact (GlobalTheory.T.formalChart_hasPeriod_linear_integral p C v O hv ε hε F G d c μ' hL hμ 0 0 t 0 0 0 hd hz hz).2 s hs
  | exact (GlobalTheory.T.formalChart_hasPeriod_linear_integral p C v O hv ε hε F G d c μ' hL hμ 0 0 t 0 0 0 hz hz).2 s hs

theorem hasPeriod_comb (t : G.Tate) {ι : Type} [Fintype ι] (e : ι → MvPowerSeries (Fin d) F.Q)
    (hd : ∀ i, DIn (⊤ : Ideal F.B) (e i)) (y : ι → F.B) (hy : ∀ i, c.HasPeriod F.θ t (e i) (y i))
    (b : ι → F.B) : c.HasPeriod F.θ t (comb b e) (∑ i, b i * y i) := by
  classical
  unfold comb
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using hasPeriod_zero c F.frame t
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, add_comm (b a * y a)]
    exact hasPeriod_add_smul hv hε F c hL hμ t (b a) (hd a) ih (hy a)

theorem hasPeriod_integral (t : G.Tate) {D : MvPowerSeries (Fin d) F.Q}
    (hD : In (⊤ : Ideal F.B) D) (h0 : constantCoeff D = 0) : c.HasPeriod F.θ t D 0 := by
  obtain ⟨s, rfl⟩ := (in_top_iff D).1 hD
  have hs : constantCoeff s = 0 := by
    apply F.frame.inj
    rw [← constantCoeff_map, h0, map_zero]
  exact hasPeriod_map_zero hv hε F c hL hμ t s hs

theorem hasPeriod_unique (t : G.Tate) {f : MvPowerSeries (Fin d) F.Q} {y y' : F.B}
    (h1 : c.HasPeriod F.θ t f y) (h2 : c.HasPeriod F.θ t f y') : y = y' :=
  h1.unique F.frame h2

theorem hasPeriod_of_in (t : G.Tate) {f g : MvPowerSeries (Fin d) F.Q} {y : F.B}
    (hf : c.HasPeriod F.θ t f y) (hfg : In (⊤ : Ideal F.B) (f - g))
    (h0 : constantCoeff (f - g) = 0) : c.HasPeriod F.θ t g y := by
  have h := hasPeriod_add_smul hv hε F c hL hμ t (-1) (din_of_in hfg) hf
    (hasPeriod_integral hv hε F c hL hμ t hfg h0)
  rwa [map_neg, map_one, neg_one_smul, mul_zero, add_zero, neg_sub, add_sub_cancel] at h

end Frame

theorem window_matrices : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, PDivLat.IsConn G → PDivLat.IsConn G.dual → ∀ F : BFrame ε, ∃ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin G.height) F.B) (Gm : Matrix (Fin G.height) (Fin d ⊕ Fin k) F.B) (tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate) (χ : Fin G.height → G.dual.Tate) (w : Module.Basis (Fin d) O G.omega) (lb : Module.Basis (Fin k) O G.dual.Lie), d + k = G.height ∧ IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin G.height) (Fin G.height) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) ∧ (∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0) ∧ (∀ j m, F.θ (Y (Sum.inr j) m) = lb j (hodgeTate G (tb m))) ∧ ∀ m, dlog G (χ m) = ∑ i, F.θ (Gm m (Sum.inl i)) • w i := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG hGd F
  obtain ⟨d, ⟨c⟩⟩ := GlobalTheory.T.exists_pDivGroupFormalChart_of_connected p C v O hv G hG
  have hdk := GlobalTheory.T.chartDim_add_finrank_dual_lie_eq_height p C v O hv G d c
  have hCf := GlobalTheory.T.isTorsionFreePDThickeningFrame_valuation_integers p C v O hv
  obtain ⟨k, e0, lb, hB0, hA0, hcob0, hLie0⟩ := GlobalTheory.T.exists_adapted_quasiLog_basis_pDivGroup_lieDual p C v O hv G d c C hCf
  obtain ⟨μ', hL, hμ⟩ := GlobalTheory.T.exists_formalGroupLawLift_of_surjective F.B O F.θ F.frame.surj d c.μ c.isLaw
  obtain ⟨Θ, hΘ⟩ := frame_fraction_map p F.B O F.Q F.θ F.frame C hCf
  obtain ⟨e, he0, hB, hA⟩ := GlobalTheory.T.exists_lift_adapted_basis_quasi_logarithms_frame p C v O hv ε hε F G d c μ' hL hμ Θ hΘ k e0 hB0 hA0
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_frobenius_matrix_quasiLogarithm_basis p C v O hv ε hε F G d c μ' hL hμ k e hB hA
  have hUu := GlobalTheory.T.frobenius_matrix_isUnit_adapted_basis p C v O hv ε hε F G d c μ' hL hμ k e hB hA U hU
  have hN1 := GlobalTheory.T.frobenius_nilpotent_mod_maximal_connected_pDivGroup p C v O hv ε hε F G d c μ' hL hμ k e hB hA U fun i => (hU i).1
  have hN2 := GlobalTheory.T.isNil_dual_frobenius_alt p C v O hv ε hε F G d c μ' hL hμ k e hB hA hGd U hUu hU
  haveI := integers_isIntegrallyClosedIn hv
  haveI := G.finite_tate C
  haveI := G.free_tate C
  let tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate :=
    Module.finBasisOfFinrankEq ℤ_[p] G.Tate (G.finrank_tate C)
  obtain ⟨χ, hχ, -⟩ :=
    GlobalTheory.DieudonneSandwich.exists_dual_basis hε (G.pairing_flip_bijective C) tb.equivFun
  have hpair : ∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0 := by
    intro m m'
    have h1 := epsPairing_smul hε G (tb m) (χ m')
    rw [hχ m' (tb m)] at h1
    have h2 : epsPairing hε G (tb m) (χ m') = tb.equivFun (tb m) m' := (epsEquiv hε).injective h1
    rw [h2, Module.Basis.equivFun_self]
    all_goals
      by_cases h : m = m'
      · subst h; simp
      · simp [Pi.single_apply, h, Ne.symm h]
  have hQLe : ∀ l, QL μ' ⊤ (e l) := hB.1
  have hDe : ∀ l, DIn (⊤ : Ideal F.B) (e l) := fun l =>
    GlobalTheory.QLogDiff.dIn_of_QL p F.B O F.Q F.θ F.frame d μ' hL ⊤ (e l) (hQLe l)
  choose Y hY using fun l m =>
    (GlobalTheory.T.exists_unique_period_quasiLogarithm_pDivGroup p C v O hv ε hε F G d c μ' hL hμ (e l) (tb m) (hQLe l)).exists
  choose fχ wχ hfχ using fun m => GlobalTheory.T.exists_quasiLogarithm_of_dualCharacter p C v O hv ε hε F G d c μ' hL hμ (χ m)
  choose g hg using fun m => (hB.2 (fχ m) (hfχ m).1).exists
  obtain ⟨hbij, -⟩ := GlobalTheory.T.pdDivGroupChart_forms_basis_and_differential p C v O hv G d c
  let w : Module.Basis (Fin d) O G.omega :=
    Module.Basis.ofEquivFun (LinearEquiv.ofBijective (Fintype.linearCombination O c.form) hbij).symm
  have hw : ∀ i, w i = c.form i := by
    intro i
    simp [w, Module.Basis.ofEquivFun]
  have hcomb0 : ∀ m, constantCoeff (fχ m - comb (g m) e) = 0 := fun m => by
    rw [map_sub, (hfχ m).1.1, (ql_comb hL.const e hQLe (g m)).1, sub_zero]

  have hred : ∀ m, (∀ j, F.θ (g m (Sum.inr j)) = 0) ∧
      ∀ i, lin (map Θ (fχ m)) i = algebraMap O C (F.θ (g m (Sum.inl i))) := fun m => by
    refine GlobalTheory.T.logarithm_integers_adapted_basis_no_lie_components p C v O hv G d c k e0 lb hB0 hA0 hLie0 (map Θ (fχ m))
      (ql_map F.θ Θ hΘ hμ hL.const (hfχ m).1)
      (formalGroupLawCoboundaryOne_map_eq_zero F.θ Θ hΘ hμ hL.const (hfχ m).2.1) (fun l => F.θ (g m l)) ?_
    have := in_map_top F.θ Θ hΘ (hg m)
    rwa [map_sub, map_comb F.θ Θ hΘ, show (fun l => map Θ (e l)) = e0 from funext he0] at this

  have hperO : ∀ l m, c.HasPeriod (RingHom.id O) (tb m) (e0 l) (F.θ (Y l m)) := fun l m => by
    have h := GlobalTheory.T.hasPeriod_reduce_along_theta_to_integers p C v O hv ε hε F G d c μ' hL hμ C hCf Θ hΘ (e l) (tb m) (Y l m)
      (hQLe l) (hY l m)
    rwa [he0] at h
  refine ⟨d, k, U, Matrix.of Y, Matrix.of g, tb, χ, w, lb, ?_, hUu, ?_, ?_, ?_, ?_, ?_, hN1, hN2,
    hpair, ?_, ?_⟩
  · have := Module.finrank_eq_card_basis lb
    rw [Fintype.card_fin] at this
    omega
  ·
    ext i m
    have key : F.σ (Y i m) = ∑ l, (U * blk d k (p : F.B) 1) l i * Y l m := by
      have hc := hasPeriod_comb hv hε F c hL hμ (tb m) e hDe (fun l => Y l m) (fun l => hY l m)
        (fun l => (U * blk d k (p : F.B) 1) l i)
      have hf := GlobalTheory.T.quasiLogarithm_period_frobenius_twist p C v O hv ε hε F G d c μ' hL hμ (e i) (tb m) (Y i m) (hQLe i)
        (hY i m)
      refine hasPeriod_unique hv hε F c hL hμ (tb m)
        (hasPeriod_of_in hv hε F c hL hμ (tb m) hf (hU i).1 ?_) hc
      rw [map_sub, constantCoeff_frob p F.s (hQLe i).1, (ql_comb hL.const e hQLe _).1, sub_zero]
    rw [Matrix.map_apply, Matrix.of_apply, key, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [blk, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
      Matrix.of_apply]
    ring
  ·
    ext l m
    have key : (fun l => ∑ i, (U * blk d k (p : F.B) 1) l i * F.σ (g m i)) =
        fun l => (p : F.B) * g m l := by
      have hP : QL μ' ⊤ (algebraMap F.B F.Q (p : F.B) • fχ m) := by
        simpa using ql_add_smul hL.const (ql_zero (Q := F.Q) hL.const ⊤) (hfχ m).1 (p : F.B)
      refine (hB.2 _ hP).unique ?_ ?_
      · have e1 : algebraMap F.B F.Q (p : F.B) • fχ m -
            comb (fun l => ∑ i, (U * blk d k (p : F.B) 1) l i * F.σ (g m i)) e =
            -(frob p F.s (fχ m) - (p : F.Q) • fχ m) + frob p F.s (fχ m - comb (g m) e) +
              ∑ i, algebraMap F.B F.Q (F.σ (g m i)) •
                (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) := by
          rw [comb_sum (fun l i => (U * blk d k (p : F.B) 1) l i) (fun i => F.σ (g m i)) e, frob_sub, frob_comb p F.s F.σ F.s_alg, map_natCast]
          simp only [comb, smul_sub, Finset.sum_sub_distrib]
          abel
        rw [e1]
        refine in_add (in_add (in_neg (hfχ m).2.2.1) (in_frob p F.s F.σ F.s_alg (hg m)))
          (in_sum _ _ fun i _ => in_smul (hU i).1 _)
      · have e2 : algebraMap F.B F.Q (p : F.B) • fχ m - comb (fun l => (p : F.B) * g m l) e =
            algebraMap F.B F.Q (p : F.B) • (fχ m - comb (g m) e) := by
          simp only [comb, map_mul, mul_smul, smul_sub, Finset.smul_sum]
        rw [e2]
        exact in_smul (hg m) _
    have := congrFun key l
    simp only [Matrix.smul_apply, Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, ← this,
      Matrix.mul_apply, Matrix.map_apply]
  ·
    ext m m'
    have key : ∑ l, g m l * Y l m' =
        F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G (tb m') (χ m))) := by
      refine hasPeriod_unique hv hε F c hL hμ (tb m')
        (hasPeriod_comb hv hε F c hL hμ (tb m') e hDe (fun l => Y l m') (fun l => hY l m') (g m)) ?_
      exact hasPeriod_of_in hv hε F c hL hμ (tb m') ((hfχ m).2.2.2.2.2 (tb m')) (hg m) (hcomb0 m)
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    rw [key, hpair]
    by_cases h : m' = m
    · subst h; simp
    · simp [h, Ne.symm h]
  ·
    intro i m
    have hlie := GlobalTheory.T.tangent_eq_zero_of_formalGroupLawCoboundaryOne_eq_zero p C v O hv G d c (e0 (Sum.inl i)) (hB0.1 (Sum.inl i)).1 (hcob0 i)
    have h2 := GlobalTheory.T.quasiLogarithm_period_eq_tangent_hodgeTate p C v O hv G d c C hCf (e0 (Sum.inl i)) 0 (hB0.1 _) hlie (tb m)
    simpa using (hperO _ m).unique hCf h2
  · intro m j
    exact (hred m).1 j
  · intro j m
    exact (hperO _ m).unique hCf
      (GlobalTheory.T.quasiLogarithm_period_eq_tangent_hodgeTate p C v O hv G d c C hCf (e0 (Sum.inr j)) (lb j) (hB0.1 _) (hLie0 j) (tb m))
  · intro m
    rw [(hfχ m).2.2.2.2.1]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := (hred m).2 i
    rw [lin_map F.θ Θ hΘ, (hfχ m).2.2.2.1 i, hΘ] at h1
    rw [hw, Matrix.of_apply, hCf.inj h1]

end GlobalTheory.QLog.WindowMat
end
end
