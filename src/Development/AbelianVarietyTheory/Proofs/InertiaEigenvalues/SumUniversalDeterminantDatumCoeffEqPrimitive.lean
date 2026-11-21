import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.HeckeFlatSpecialisation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussBinomMulProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOfMemDoubleCosetK
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IntegralMatrixTranslation
import BuildAid.ForwardExisting

section
open scoped Classical BigOperators
open IsLocalRing Module Matrix

noncomputable section

namespace GlobalTheory.AdaptedLocalData

open GlobalTheory.IndefiniteRowSideFullHecke.HeckeFlatSpecialisation

section Field

variable {k : Type} [Field k]

theorem card_isCompl [Finite k] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (R : Submodule k V) :
    Nat.card {U : Submodule k V // IsCompl R U} =
      Nat.card k ^ (finrank k (V ⧸ R) * finrank k R) := by
  obtain ⟨f₀, hf₀⟩ := R.subtype.exists_leftInverse_of_injective R.ker_subtype
  have h₀ : ∀ x : R, f₀ x = x := fun x => LinearMap.congr_fun hf₀ x
  rw [Nat.card_congr R.isComplEquivProj, ← Module.finrank_linearMap k k,
    ← Module.natCard_eq_pow_finrank (K := k)]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun g => ⟨f₀ + g.comp R.mkQ, fun x => by
      have : R.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero R).2 x.2
      rw [LinearMap.add_apply, LinearMap.comp_apply, this, map_zero, add_zero, h₀]⟩) ⟨?_, ?_⟩)
  · intro g g' h
    have h1 : g.comp R.mkQ = g'.comp R.mkQ := add_left_cancel (congrArg Subtype.val h)
    exact R.linearMap_qext h1
  · rintro ⟨f, hf⟩
    refine ⟨R.liftQ (f - f₀) fun x hx => ?_, Subtype.ext ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, hf ⟨x, hx⟩, h₀ ⟨x, hx⟩, sub_self]
    · simp

theorem card_sup_eq_top [Finite k] (r t : ℕ) (R : Submodule k (Fin (r + t) → k))
    (hR : finrank k R ≤ r) :
    Nat.card {U : Submodule k (Fin (r + t) → k) // finrank k U = t ∧ R ⊔ U = ⊤} =
      if finrank k R = r then Nat.card k ^ (r * t) else 0 := by
  have key : ∀ U : Submodule k (Fin (r + t) → k), R ⊔ U = ⊤ →
      r + t + finrank k ↥(R ⊓ U) = finrank k R + finrank k U := fun U h => by
    have := Submodule.finrank_sup_add_finrank_inf_eq R U
    rwa [h, finrank_top, finrank_fin_fun] at this
  split_ifs with h
  · have hq : finrank k ((Fin (r + t) → k) ⧸ R) = t := by
      have := R.finrank_quotient_add_finrank
      rw [finrank_fin_fun] at this
      omega
    have := card_isCompl R
    rw [hq, h, mul_comm] at this
    rw [← this]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun U => ⟨fun ⟨h1, h2⟩ => ?_, fun hc => ?_⟩)
    · refine ⟨disjoint_iff.2 (Submodule.finrank_eq_zero.1 ?_), codisjoint_iff.2 h2⟩
      have := key U h2
      omega
    · have := key U hc.sup_eq_top
      rw [hc.inf_eq_bot, finrank_bot] at this
      exact ⟨by omega, hc.sup_eq_top⟩
  · haveI : IsEmpty {U : Submodule k (Fin (r + t) → k) // finrank k U = t ∧ R ⊔ U = ⊤} :=
      ⟨fun U => by have := key U.1 U.2.2; have := U.2.1; omega⟩
    exact Nat.card_of_isEmpty

end Field

section Local

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]

variable [Finite (ResidueField O)]

end Local

end GlobalTheory.AdaptedLocalData
end
end

section
open scoped BigOperators

namespace GlobalTheory

theorem card_subspaces_sup_eq_top :
    ∀ (k : Type) [Field k] [Finite k] (r t : ℕ) (R : Submodule k (Fin (r + t) → k)),
      Module.finrank k R ≤ r →
      Nat.card {U : Submodule k (Fin (r + t) → k) // Module.finrank k U = t ∧ R ⊔ U = ⊤} =
        if Module.finrank k R = r then Nat.card k ^ (r * t) else 0 := by
  intro k _ _ r t R hR
  convert AdaptedLocalData.card_sup_eq_top r t R hR

end GlobalTheory
end

section
section
open Matrix GlobalTheory.ExportSeries

namespace GlobalTheory.ExportSeries

theorem sum_univCoef_eq_prim : ∀ (k C : Type) [Field k] [Finite k] [AddCommGroup C] [Fintype C] (r n : ℕ), r ≤ n →
    ∀ (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (y : Matrix (Fin r) (Fin n) k), ∑ c, univCoef β κ c y = prim y := by
  intro k C _ _ _ _ r n hrn β κ y
  classical
  letI := Fintype.ofFinite (Planes k r n)

  have hterm : ∀ U : Planes k r n, ∑ c, (univTerm β κ y U).coeff c = if Compl U.1 y then 1 else 0 := by
    intro U
    unfold univTerm
    by_cases h : Compl U.1 y
    · rw [dif_pos h, if_pos h]
      simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    · rw [dif_neg h, if_neg h]
      simp
  have hsum : ∑ c, univCoef β κ c y = ((Nat.card k : ℚ) ^ (r * (n - r)))⁻¹ *
      (Nat.card {U : Planes k r n // Compl U.1 y} : ℚ) := by
    simp only [univCoef, univ, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, AddMonoidAlgebra.coeff_sum,
      Finsupp.finset_sum_apply]
    rw [← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl fun U _ => hterm U, Finset.sum_boole]
    congr 2
    rw [Nat.card_eq_fintype_card (α := {U : Planes k r n // Compl U.1 y}), Fintype.card_subtype]
  rw [hsum]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrn
  have ht : r + t - r = t := by omega
  rw [ht]
  set R := Submodule.span k (Set.range y.row) with hR
  have hRle : Module.finrank k R ≤ r := by
    have := finrank_range_le_card (R := k) y.row
    rw [Fintype.card_fin] at this
    exact this
  have hcard : Nat.card {U : Planes k r (r + t) // Compl U.1 y} =
      Nat.card {U : Submodule k (Fin (r + t) → k) // Module.finrank k U = t ∧ R ⊔ U = ⊤} := by
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter _ (fun U => Compl U y)).trans
      (Equiv.subtypeEquivRight fun U => ?_))
    simp only [Compl, hR]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  rw [hcard, GlobalTheory.card_subspaces_sup_eq_top k r t R hRle]
  have hq : ((Nat.card k : ℚ) ^ (r * t)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.card_pos.ne')
  have hli : LinearIndependent k y.row ↔ Module.finrank k R = r := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank, eq_comm]
  unfold prim
  by_cases h : Module.finrank k R = r
  · rw [if_pos h, if_pos (hli.2 h)]
    push_cast
    exact inv_mul_cancel₀ hq
  · rw [if_neg h, if_neg (fun h' => h (hli.1 h'))]
    simp

end GlobalTheory.ExportSeries
end

open Matrix GlobalTheory.ExportSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_universalDeterminantDatumCoeff_eq_primitive : ∀ (k C : Type) [Field k] [Finite k] [AddCommGroup C] [Fintype C] (r n : ℕ), r ≤ n → ∀ (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (y : Matrix (Fin r) (Fin n) k), ∑ c, univCoef β κ c y = prim y := by
  atlas_forward_decl GlobalTheory.ExportSeries.sum_univCoef_eq_prim
end
