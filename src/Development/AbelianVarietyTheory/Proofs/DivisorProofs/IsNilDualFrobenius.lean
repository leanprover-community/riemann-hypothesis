import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationCoeffEqZeroOfDegreeLtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationFormalGroupLawIsLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIteratePInvariantDerivationMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationMonomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstMapToFractionsMemSubmodule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstRestrictSumVariables
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationFormalGroupLawIsLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationCoeffEqZeroOfDegreeLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedInOfQuasiLogarithm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstEqZeroOfDegreeLt

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory.LawDer

theorem map_pderiv_coeffChange {R S σ : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : MvPowerSeries σ R) (s : σ) :
    MvPowerSeries.map φ (MvPowerSeries.pderiv R s f) = MvPowerSeries.pderiv S s (MvPowerSeries.map φ f) := by
  ext m
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_map,
    map_mul, map_add, map_natCast, map_one]

theorem map_atZero {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (H : MvPowerSeries (Fin d ⊕ Fin d) R) : map f (atZero H) = atZero (map f H) := by
  unfold atZero
  rw [map_subst (hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp))]
  congr 1
  funext s
  cases s <;> simp

theorem map_smul_coeffChange {R S σ : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : R)
    (H : MvPowerSeries σ R) : map f (a • H) = f a • map f H := by
  ext m
  simp [MvPowerSeries.coeff_map, MvPowerSeries.coeff_smul]

theorem map_invDer {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u : Fin d → R) (F : MvPowerSeries (Fin d) R) :
    map f (invDer μ u F) = invDer (fun i => map f (μ i)) (fun i => f (u i)) (map f F) := by
  unfold invDer
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul_coeffChange, map_atZero, map_pderiv_coeffChange, map_subst (hasSubst_of_constantCoeff_zero hμ)]

theorem map_invDer_iterate : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) →
    ∀ (u : Fin d → R) (k : ℕ) (F : MvPowerSeries (Fin d) R),
    map f ((invDer μ u)^[k] F) = (invDer (fun i => map f (μ i)) (fun i => f (u i)))^[k] (map f F) := by
  intro R S _ _ f d μ hμ u k F
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_invDer f μ hμ, ih]

end GlobalTheory.LawDer
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_invariantDerivationFormalGroupLaw_iterate : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (u : Fin d → R) (k : ℕ) (F : MvPowerSeries (Fin d) R), map f ((invDer μ u)^[k] F) = (invDer (fun i => map f (μ i)) (fun i => f (u i)))^[k] (map f F) := by
  atlas_forward_decl GlobalTheory.LawDer.map_invDer_iterate
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

namespace GlobalTheory.LawDer.Kernel

variable {R : Type} [CommRing R] {d : ℕ}

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
private lemma coeff_atZero_eq_coeff_mapDomain_inl {S : Type} [CommRing S] {n : ℕ}
    (G : MvPowerSeries (Fin n ⊕ Fin n) S) (α : Fin n →₀ ℕ) :
    coeff α (_root_.GlobalTheory.LawDer.atZero G) = coeff (Finsupp.mapDomain Sum.inl α) G :=
  (_root_.GlobalTheory.coeff_subst_restrict_sum G).1 α

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
private lemma coeff_subst_X_comp_eq_finsum {σ τ S : Type} [CommRing S] [Finite σ] [DecidableEq τ] (g : σ → τ)
    (F : MvPowerSeries σ S) (γ : τ →₀ ℕ) :
    coeff γ (subst (fun s => (X (g s) : MvPowerSeries τ S)) F) =
      ∑ᶠ e : σ →₀ ℕ, if γ = Finsupp.mapDomain g e then coeff e F else 0 := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _)]
  refine finsum_congr fun e => ?_
  rw [← Finsupp.prod_mapDomain_index (h := fun t k => (X t : MvPowerSeries τ S) ^ k) (by simp)
    (by intros; simp [pow_add]), ← monomial_one_eq, coeff_monomial]
  split_ifs <;> simp

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
private lemma coeff_subst_X_comp_eq_zero_of_not_mem_range {σ τ S : Type} [CommRing S] [Finite σ] (g : σ → τ)
    (F : MvPowerSeries σ S) {γ : τ →₀ ℕ} (hγ : γ ∉ Set.range (Finsupp.mapDomain g)) :
    coeff γ (subst (fun s => (X (g s) : MvPowerSeries τ S)) F) = 0 := by
  classical
  rw [coeff_subst_X_comp_eq_finsum]
  exact (finsum_congr fun e => if_neg fun h => hγ ⟨e, h.symm⟩).trans finsum_zero

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
private lemma coeff_mapDomain_subst_X_comp_of_injective {σ τ S : Type} [CommRing S] [Finite σ] {g : σ → τ}
    (hg : Function.Injective g) (F : MvPowerSeries σ S) (e : σ →₀ ℕ) :
    coeff (Finsupp.mapDomain g e) (subst (fun s => (X (g s) : MvPowerSeries τ S)) F) =
      coeff e F := by
  classical
  rw [coeff_subst_X_comp_eq_finsum, finsum_eq_single _ e, if_pos rfl]
  intro e' he'
  rw [if_neg]
  exact fun h => he' (Finsupp.mapDomain_injective hg h).symm

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in

theorem _root_.GlobalTheory.LawDer.Kernel.constantCoeff_iterate_invDer_mem : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ i) = 0) → ∀ (N : Ideal B) (l : MvPowerSeries (Fin d) Q) (j : Fin d), _root_.GlobalTheory.QLog.In N (_root_.GlobalTheory.Katz.cob1 (_root_.GlobalTheory.QLog.up Q μ) l) → _root_.GlobalTheory.Katz.lin l = Pi.single j 1 → ∀ (u : Fin d → B) (n : ℕ), 2 ≤ n → ∃ b ∈ N, constantCoeff ((_root_.GlobalTheory.LawDer.invDer (_root_.GlobalTheory.QLog.up Q μ) (fun i => algebraMap B Q (u i)))^[n] l) = algebraMap B Q b := by
  intro B Q _ _ _ d μ hμ N l j hc hl u n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold _root_.GlobalTheory.QLog.In at hc
  set μ' := _root_.GlobalTheory.QLog.up Q μ with hμ'
  set D := _root_.GlobalTheory.LawDer.invDer μ' (fun i => algebraMap B Q (u i)) with hD
  let S : Submodule B Q := Submodule.map (Algebra.linearMap B Q) N
  have memS : ∀ x : Q, x ∈ S ↔ ∃ b ∈ N, x = algebraMap B Q b := fun x => by
    simp only [S, Submodule.mem_map, Algebra.linearMap_apply]
    exact ⟨fun ⟨b, hb, h⟩ => ⟨b, hb, h.symm⟩, fun ⟨b, hb, h⟩ => ⟨b, hb, h.symm⟩⟩
  have hμ0 : ∀ i, constantCoeff (μ' i) = 0 := fun i => by
    simp [μ', _root_.GlobalTheory.QLog.up, constantCoeff_map, hμ i]
  have hlin := _root_.GlobalTheory.LawDer.Linear.invDer_linear Q d μ' hμ0 (fun i => algebraMap B Q (u i))
  have hlinD : ∀ F G : MvPowerSeries (Fin d) Q, D (F + G) = D F + D G := hlin.1
  have hcoeffD : ∀ (F : MvPowerSeries (Fin d) Q) (β : Fin d →₀ ℕ), coeff β (D F) =
      ∑ i, algebraMap B Q (u i) * (coeff (Finsupp.mapDomain Sum.inl β +
        Finsupp.single (Sum.inr i) 1) (subst μ' F) *
          ((Finsupp.mapDomain Sum.inl β (Sum.inr i) : Q) + 1)) := by
    intro F β
    rw [hD]
    unfold _root_.GlobalTheory.LawDer.invDer
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_smul, coeff_atZero_eq_coeff_mapDomain_inl, coeff_pderiv]
  have hP : ∀ F : MvPowerSeries (Fin d) Q, (∀ α, coeff α F ∈ S) → ∀ β, coeff β (D F) ∈ S := by
    intro F hF β
    rw [hcoeffD]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Algebra.smul_def]
    refine S.smul_mem _ ?_
    rw [← Nat.cast_succ, mul_comm, ← nsmul_eq_mul]
    exact nsmul_mem (_root_.GlobalTheory.SubstSub.coeff_subst_up_mem B Q (Fin d) (Fin d ⊕ Fin d) S F μ
      hμ hF _) _
  have hPit : ∀ (k : ℕ) (F : MvPowerSeries (Fin d) Q), (∀ α, coeff α F ∈ S) →
      ∀ β, coeff β (D^[k] F) ∈ S := by
    intro k
    induction k with
    | zero => intro F hF; simpa using hF
    | succ k ih => intro F hF; rw [Function.iterate_succ_apply]; exact ih _ (hP F hF)
  have hadd : ∀ (k : ℕ) (F G : MvPowerSeries (Fin d) Q), D^[k] (F + G) = D^[k] F + D^[k] G := by
    intro k
    induction k with
    | zero => intro F G; rfl
    | succ k ih =>
      intro F G
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        hlinD, ih]
  have hD0 : D 0 = 0 := by
    have h := hlinD 0 0
    rw [add_zero] at h
    simpa using h
  have hDC : ∀ c : Q, D (C c) = 0 := by
    intro c
    ext β
    rw [hcoeffD]
    simp [subst_C, coeff_C]
  have hCit : ∀ (k : ℕ) (c : Q), D^[k + 1] (C c) = 0 := fun k c => by
    rw [Function.iterate_succ_apply, hDC, Function.iterate_fixed hD0]
  have hzero : ∀ (β : Fin d →₀ ℕ) (i : Fin d), Finsupp.mapDomain Sum.inl β (Sum.inr i) = 0 :=
    fun β i => Finsupp.mapDomain_notin_range _ _ (by simp)
  have hsplit : subst μ' l = _root_.GlobalTheory.Katz.cob1 μ' l + _root_.GlobalTheory.Katz.inL l +
      _root_.GlobalTheory.Katz.inR l := by
    unfold _root_.GlobalTheory.Katz.cob1
    ring
  have hleft : ∀ (β : Fin d →₀ ℕ) (i : Fin d), coeff (Finsupp.mapDomain Sum.inl β +
      Finsupp.single (Sum.inr i) 1) (_root_.GlobalTheory.Katz.inL l) = 0 := by
    intro β i
    unfold _root_.GlobalTheory.Katz.inL
    apply coeff_subst_X_comp_eq_zero_of_not_mem_range
    rintro ⟨e, he⟩
    have h := congrArg (fun x => x (Sum.inr i)) he
    simp [hzero] at h
  have hright : ∀ (β : Fin d →₀ ℕ) (i : Fin d), coeff (Finsupp.mapDomain Sum.inl β +
      Finsupp.single (Sum.inr i) 1) (_root_.GlobalTheory.Katz.inR l) =
        if β = 0 then (Pi.single j 1 : Fin d → Q) i else 0 := by
    intro β i
    unfold _root_.GlobalTheory.Katz.inR
    split_ifs with hβ
    · subst hβ
      rw [Finsupp.mapDomain_zero, zero_add, ← Finsupp.mapDomain_single,
        coeff_mapDomain_subst_X_comp_of_injective Sum.inr_injective, ← hl]
      rfl
    · apply coeff_subst_X_comp_eq_zero_of_not_mem_range
      rintro ⟨e, he⟩
      obtain ⟨k, hk⟩ : ∃ k, β k ≠ 0 := by
        by_contra h
        push_neg at h
        exact hβ (Finsupp.ext h)
      have h := congrArg (fun x => x (Sum.inl k)) he
      rw [Finsupp.mapDomain_notin_range _ _ (by simp)] at h
      simp [Finsupp.mapDomain_apply Sum.inl_injective] at h
      omega
  have hg : ∀ β, coeff β (D l - C (algebraMap B Q (u j))) ∈ S := by
    intro β
    have hsum : coeff β (D l - C (algebraMap B Q (u j))) = ∑ i, algebraMap B Q (u i) *
        coeff (Finsupp.mapDomain Sum.inl β + Finsupp.single (Sum.inr i) 1)
          (_root_.GlobalTheory.Katz.cob1 μ' l) := by
      rw [map_sub, hcoeffD]
      simp only [hsplit, map_add, hleft, hright, hzero, Nat.cast_zero, zero_add, add_zero,
        mul_one, mul_add, Finset.sum_add_distrib]
      by_cases hβ : β = 0 <;> simp [hβ, Pi.single_apply, coeff_C]
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Algebra.smul_def]
    refine S.smul_mem _ ((memS _).2 ?_)
    obtain ⟨b, hb, h⟩ := hc (Finsupp.mapDomain Sum.inl β + Finsupp.single (Sum.inr i) 1)
    exact ⟨b, hb, h⟩
  have key : D^[m + 2] l = D^[m + 1] (D l - C (algebraMap B Q (u j))) := by
    conv_lhs => rw [Function.iterate_succ_apply, ← sub_add_cancel (D l) (C (algebraMap B Q (u j)))]
    rw [hadd, hCit, add_zero]
  rw [key]
  obtain ⟨b, hb, h⟩ := (memS _).1 (hPit (m + 1) _ hg 0)
  refine ⟨b, hb, ?_⟩
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact h

end GlobalTheory.LawDer.Kernel
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_iterate_invariantDerivation_mem : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ i) = 0) → ∀ (N : Ideal B) (l : MvPowerSeries (Fin d) Q) (j : Fin d), In N (cob1 (up Q μ) l) → lin l = Pi.single j 1 → ∀ (u : Fin d → B) (n : ℕ), 2 ≤ n → ∃ b ∈ N, constantCoeff ((invDer (up Q μ) (fun i => algebraMap B Q (u i)))^[n] l) = algebraMap B Q b := by
  atlas_forward_decl GlobalTheory.LawDer.Kernel.constantCoeff_iterate_invDer_mem
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

namespace GlobalTheory.LawDer.IterateLocal

open MvPowerSeries in
set_option autoImplicit false in
private lemma iterate_invDer_sub (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u : Fin d → R) :
    ∀ (m : ℕ) (F G : MvPowerSeries (Fin d) R),
      (_root_.GlobalTheory.LawDer.invDer μ u)^[m] F - (_root_.GlobalTheory.LawDer.invDer μ u)^[m] G =
        (_root_.GlobalTheory.LawDer.invDer μ u)^[m] (F - G) := by
  have hadd := (_root_.GlobalTheory.LawDer.Linear.invDer_linear R d μ hμ u).1
  intro m
  induction m with
  | zero => intro F G; rfl
  | succ m ih =>
    intro F G
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    congr 1
    rw [sub_eq_iff_eq_add, ← hadd, sub_add_cancel]

open MvPowerSeries in
set_option autoImplicit false in
private lemma coeff_iterate_invDer_eq_zero_of_degree_lt (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u : Fin d → R) (N : ℕ) :
    ∀ (m : ℕ) (H : MvPowerSeries (Fin d) R), (∀ α : Fin d →₀ ℕ, α.degree < N + m → coeff α H = 0) →
      ∀ α : Fin d →₀ ℕ, α.degree < N →
        coeff α ((_root_.GlobalTheory.LawDer.invDer μ u)^[m] H) = 0 := by
  intro m
  induction m with
  | zero => intro H hH α hα; exact hH α (by simpa using hα)
  | succ m ih =>
    intro H hH α hα
    rw [Function.iterate_succ_apply]
    refine ih _ (fun β hβ => ?_) α hα
    exact _root_.GlobalTheory.invDer_coeff_eq_zero_of_degree_lt R d μ hμ u H (N + m)
      (fun γ hγ => hH γ (by omega)) β hβ

open MvPowerSeries in
set_option autoImplicit false in

theorem _root_.GlobalTheory.LawDer.IterateLocal.constantCoeff_iterate_invDer_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (u : Fin d → R) (n : ℕ) (F G : MvPowerSeries (Fin d) R), (∀ α : Fin d →₀ ℕ, α.degree ≤ n → coeff α F = coeff α G) → constantCoeff ((_root_.GlobalTheory.LawDer.invDer μ u)^[n] F) = constantCoeff ((_root_.GlobalTheory.LawDer.invDer μ u)^[n] G) := by
  intro R _ d μ hμ u n F G hFG
  rw [← sub_eq_zero, ← map_sub, iterate_invDer_sub R d μ hμ u,
    ← coeff_zero_eq_constantCoeff_apply]
  refine coeff_iterate_invDer_eq_zero_of_degree_lt R d μ hμ u 1 n (F - G) (fun α hα => ?_) 0
    (by simp)
  rw [map_sub, hFG α (by omega), sub_self]

end GlobalTheory.LawDer.IterateLocal
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_iterate_invariantDerivation_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (u : Fin d → R) (n : ℕ) (F G : MvPowerSeries (Fin d) R), (∀ α : Fin d →₀ ℕ, α.degree ≤ n → coeff α F = coeff α G) → constantCoeff ((invDer μ u)^[n] F) = constantCoeff ((invDer μ u)^[n] G) := by
  atlas_forward_decl GlobalTheory.LawDer.IterateLocal.constantCoeff_iterate_invDer_congr
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

namespace GlobalTheory.QLogInt

theorem coeff_integral_of_QL : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ l : MvPowerSeries (Fin d) Q, QL μ ⊤ l → ∀ α : Fin d →₀ ℕ, α.degree ≤ p → (∀ i, α ≠ Finsupp.single i p) → ∃ b : B, coeff α l = algebraMap B Q b := by
  intro p hpf B O Q _ _ _ _ θ hF d μ hμ l hl α hdeg hne
  have hp : p.Prime := hpf.out
  classical
  by_cases h0 : α = 0
  · refine ⟨0, ?_⟩
    rw [h0, coeff_zero_eq_constantCoeff_apply, hl.1, map_zero]
  obtain ⟨k, hk⟩ : ∃ k, α k ≠ 0 := by
    by_contra h
    push_neg at h
    exact h0 (Finsupp.ext h)
  have hkle : α k ≤ p := (Finsupp.le_degree k α).trans hdeg
  have hklt : α k < p := by
    refine lt_of_le_of_ne hkle fun hkp => hne k ?_
    have hs : Finsupp.single k p ≤ α := by
      rw [Finsupp.single_le_iff]; omega
    have hsplit : α = Finsupp.single k p + (α - Finsupp.single k p) := (add_tsub_cancel_of_le hs).symm
    have hd : (α - Finsupp.single k p).degree = 0 := by
      have h2 := congrArg Finsupp.degree hsplit
      rw [map_add, Finsupp.degree_single] at h2
      omega
    rw [(Finsupp.degree_eq_zero_iff _).1 hd, add_zero] at hsplit
    exact hsplit
  have hcop : Nat.Coprime (α k) p :=
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk) hklt)))
  obtain ⟨u, hu⟩ := hF.unit_coprime (α k) hcop
  obtain ⟨b', -, hb'⟩ := GlobalTheory.QLogDiff.dIn_of_QL p B O Q θ hF d μ hμ ⊤ l hl α k
  refine ⟨(↑u⁻¹ : B) * b', ?_⟩
  have h1 : algebraMap B Q (↑u⁻¹ : B) * (α k : Q) = 1 := by
    rw [← map_natCast (algebraMap B Q) (α k), ← hu, ← map_mul, Units.inv_mul, map_one]
  rw [map_mul, ← hb']
  linear_combination (-(coeff α l)) * h1

end GlobalTheory.QLogInt
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_quasiLogarithm_integral_low_degree : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ l : MvPowerSeries (Fin d) Q, QL μ ⊤ l → ∀ α : Fin d →₀ ℕ, α.degree ≤ p → (∀ i, α ≠ Finsupp.single i p) → ∃ b : B, coeff α l = algebraMap B Q b := by
  atlas_forward_decl GlobalTheory.QLogInt.coeff_integral_of_QL
end

section
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory.FrobIter

def iterLin {R : Type} [CommRing R] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (u : Fin d → R) (n : ℕ) :
    MvPowerSeries (Fin d) R →ₗ[R] MvPowerSeries (Fin d) R where
  toFun := (invDer μ u)^[n]
  map_add' := by
    obtain ⟨hadd, -, -⟩ := GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear R d μ hμ u
    induction n with
    | zero => intro F G; rfl
    | succ n ih => intro F G; simp only [Function.iterate_succ_apply', ih, hadd]
  map_smul' := by
    obtain ⟨-, hsmul, -⟩ := GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear R d μ hμ u
    induction n with
    | zero => intro a F; rfl
    | succ n ih => intro a F; simp only [Function.iterate_succ_apply', ih, hsmul, RingHom.id_apply]

theorem iterLin_apply {R : Type} [CommRing R] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (u : Fin d → R) (n : ℕ) (F : MvPowerSeries (Fin d) R) :
    iterLin hμ u n F = (invDer μ u)^[n] F := rfl

theorem constantCoeff_iterate_invDer_X_sub_mem : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (l : MvPowerSeries (Fin d) Q) (j : Fin d), QL μ ⊤ l → In (RingHom.ker θ) (cob1 (up Q μ) l) → lin l = Pi.single j 1 → ∀ c : Fin d → B, (∀ i, algebraMap B Q (c i) = (p : Q) * coeff (Finsupp.single i p) l) → ∀ u : Fin d → B, constantCoeff ((invDer μ u)^[p] (X j)) - ∑ i, c i * u i ^ p ∈ RingHom.ker θ ⊔ Ideal.span {(p : B)} := by
  intro p _ B O Q _ _ _ _ θ hF d μ hL l j hQL hcob hlin c hc u
  classical
  have hp : p.Prime := Fact.out
  have hμ := hL.const
  have hμQ : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ,
      map_zero]
  obtain ⟨b, hbN, hb⟩ := GlobalTheory.T.constantCoeff_iterate_invariantDerivation_mem B Q d μ hμ (RingHom.ker θ) l j hcob hlin u p hp.two_le
  have h3 := GlobalTheory.T.coeff_quasiLogarithm_integral_low_degree p B O Q θ hF d μ hL l hQL
  let P : (Fin d →₀ ℕ) → Prop := fun α => α.degree ≤ p ∧ ∀ i, α ≠ Finsupp.single i p
  let h : (Fin d →₀ ℕ) → B := fun α => if hα : P α then (h3 α hα.1 hα.2).choose else 0
  have hh : ∀ α, P α → algebraMap B Q (h α) = coeff α l := fun α hα => by
    simp only [h, dif_pos hα]; exact (h3 α hα.1 hα.2).choose_spec.symm
  let H : MvPowerSeries (Fin d) B := fun α => h α
  have hH : ∀ α, coeff α H = h α := fun α => rfl
  let q : Fin d → Q := fun i => coeff (Finsupp.single i p) l
  have hinj : ∀ i k : Fin d, Finsupp.single i p = Finsupp.single k p ↔ i = k := fun i k =>
    Finsupp.single_left_inj hp.ne_zero
  let G : MvPowerSeries (Fin d) Q :=
    map (algebraMap B Q) H + ∑ i, q i • monomial (Finsupp.single i p) (1 : Q)
  have hG : ∀ α : Fin d →₀ ℕ, α.degree ≤ p → coeff α l = coeff α G := by
    intro α hα
    simp only [G, map_add, coeff_map, hH, map_sum, map_smul, coeff_monomial, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    by_cases hP : ∀ i, α ≠ Finsupp.single i p
    · rw [hh α ⟨hα, hP⟩, Finset.sum_eq_zero (fun i _ => if_neg (hP i)), add_zero]
    · push_neg at hP
      obtain ⟨i, rfl⟩ := hP
      have : h (Finsupp.single i p) = 0 := dif_neg fun hα => hα.2 i rfl
      rw [this, map_zero, zero_add, Finset.sum_eq_single i (fun k _ hk => if_neg fun e =>
        hk ((hinj i k).1 e).symm) (by simp), if_pos rfl]

  have hnat : ∀ F : MvPowerSeries (Fin d) B,
      constantCoeff ((invDer (up Q μ) (fun i => algebraMap B Q (u i)))^[p] (map (algebraMap B Q) F)) =
        algebraMap B Q (constantCoeff ((invDer μ u)^[p] F)) := fun F => by
    rw [← constantCoeff_map, GlobalTheory.T.map_invariantDerivationFormalGroupLaw_iterate B Q (algebraMap B Q) d μ hμ u p F]; rfl
  have hmon : ∀ i : Fin d, monomial (Finsupp.single i p) (1 : Q) =
      map (algebraMap B Q) (monomial (Finsupp.single i p) (1 : B)) := fun i => by
    rw [map_monomial, (algebraMap B Q).map_one]
  have hmono : ∀ i : Fin d, constantCoeff ((invDer μ u)^[p] (monomial (Finsupp.single i p) (1 : B))) =
      (p.factorial : B) * u i ^ p := fun i => by
    have := GlobalTheory.T.constantCoeff_iterate_invariant_derivation_monomial B d μ hμ hL.unit hL.comm u (Finsupp.single i p)
    rw [Finsupp.degree_single] at this
    rw [this, Finset.prod_eq_single i (fun k _ hk => by rw [Finsupp.single_apply, if_neg (Ne.symm hk),
      pow_zero]) (by simp), Finsupp.single_eq_same]
  have e1 := GlobalTheory.T.constantCoeff_iterate_invariantDerivation_congr Q d (up Q μ) hμQ (fun i => algebraMap B Q (u i)) p l G hG
  have e2 : constantCoeff ((invDer (up Q μ) (fun i => algebraMap B Q (u i)))^[p] G) =
      algebraMap B Q (constantCoeff ((invDer μ u)^[p] H)) +
        ∑ i, q i * algebraMap B Q ((p.factorial : B) * u i ^ p) := by
    rw [← iterLin_apply hμQ]
    simp only [G, map_add, map_sum, map_smul, iterLin_apply, hmon, hnat]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_C_mul, map_mul, constantCoeff_C, hnat, hmono]
  obtain ⟨r, hr⟩ := GlobalTheory.T.constantCoeff_iterate_invariant_derivation_linear p B d μ hμ hL.unit hL.comm u H
  have hlin1 : ∀ k, coeff (Finsupp.single k 1) H = if k = j then 1 else 0 := fun k => by
    apply hF.inj
    have hPk : P (Finsupp.single k 1) := ⟨by rw [Finsupp.degree_single]; exact hp.one_le, fun i e => by
      rcases (Finsupp.single_eq_single_iff _ _ _ _).1 e with ⟨_, h1⟩ | ⟨h1, _⟩
      · exact hp.one_lt.ne h1
      · exact one_ne_zero h1⟩
    rw [hH, hh _ hPk]
    have := congrFun hlin k
    simp only [lin] at this
    rw [this, Pi.single_apply]
    split_ifs <;> simp
  have hsumX : ∑ k, constantCoeff ((invDer μ u)^[p] (X k)) * coeff (Finsupp.single k 1) H =
      constantCoeff ((invDer μ u)^[p] (X j)) := by
    simp [hlin1]
  rw [hsumX] at hr
  have key : b = constantCoeff ((invDer μ u)^[p] H) + ((p - 1).factorial : B) * ∑ i, c i * u i ^ p := by
    apply hF.inj
    rw [← hb, e1, e2]
    simp only [map_add, map_mul, map_sum, map_pow, map_natCast]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc, ← Nat.mul_factorial_pred hp.ne_zero]
    push_cast
    ring
  obtain ⟨m, hm⟩ : p ∣ (p - 1).factorial + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.wilsons_lemma]
    ring
  have hmB : ((p - 1).factorial : B) = p * m - 1 := by
    have := congrArg (Nat.cast : ℕ → B) hm
    push_cast at this
    linear_combination this
  have eq : constantCoeff ((invDer μ u)^[p] (X j)) - ∑ i, c i * u i ^ p =
      b - p * (r + m * ∑ i, c i * u i ^ p) := by
    rw [key, hmB]
    linear_combination -hr
  rw [eq]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left hbN)
    (Ideal.mem_sup_right (Ideal.mem_span_singleton.2 ⟨_, rfl⟩))

end GlobalTheory.FrobIter
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_pIterate_invariantDerivation_coord : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (l : MvPowerSeries (Fin d) Q) (j : Fin d), QL μ ⊤ l → In (RingHom.ker θ) (cob1 (up Q μ) l) → lin l = Pi.single j 1 → ∀ c : Fin d → B, (∀ i, algebraMap B Q (c i) = (p : Q) * coeff (Finsupp.single i p) l) → ∀ u : Fin d → B, constantCoeff ((invDer μ u)^[p] (X j)) - ∑ i, c i * u i ^ p ∈ RingHom.ker θ ⊔ Ideal.span {(p : B)} := by
  atlas_forward_decl GlobalTheory.FrobIter.constantCoeff_iterate_invDer_X_sub_mem
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobCoef

theorem coeff_frob_single (p : ℕ) [hp : Fact p.Prime] {Q : Type} [CommRing Q] {d : ℕ}
    (s : Q →+* Q) (f : MvPowerSeries (Fin d) Q) (j : Fin d) :
    coeff (Finsupp.single j p) (frob p s f) = s (lin f j) := by
  classical
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hs : HasSubst (fun i => (X i : MvPowerSeries (Fin d) Q) ^ p) :=
    hasSubst_of_constantCoeff_zero fun i => by simp [hp0]
  rw [frob, coeff_subst hs]
  have key : ∀ e : Fin d →₀ ℕ, (e.prod fun i n => ((X i : MvPowerSeries (Fin d) Q) ^ p) ^ n) =
      monomial (p • e) 1 := by
    intro e
    induction e using Finsupp.induction with
    | zero => simp
    | single_add i n e hi hn ih =>
      rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), ih, Finsupp.prod_single_index
        (by simp), ← pow_mul, X_pow_eq, monomial_mul_monomial, one_mul, smul_add,
        Finsupp.smul_single, smul_eq_mul]
  simp_rw [key]
  rw [finsum_eq_single _ (Finsupp.single j 1)]
  · rw [coeff_monomial, if_pos (by rw [Finsupp.smul_single, smul_eq_mul, mul_one]), smul_eq_mul,
      mul_one, coeff_map, lin]
  · intro e he
    rw [coeff_monomial, if_neg, smul_zero]
    intro h
    apply he
    ext i
    have := congrArg (fun g => g i) h
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply] at this ⊢
    split_ifs at this ⊢ with h1
    · exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0) (this.symm.trans (mul_one p).symm)
    · exact (mul_eq_zero.1 this.symm).resolve_left hp0

theorem coef_logs_inv_frob : ∀ (p : ℕ) [Fact p.Prime] (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (s : Q →+* Q) (σ : B →+* B), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σ b)) → Function.Injective (algebraMap B Q) → ∀ (d k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) Q) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B), IsUnit U → (∀ i, In (⊤ : Ideal B) (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : B)}) (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e)) → (∀ a, lin (e (Sum.inl a)) = Pi.single a 1) → (∀ r j, ∃ b, lin (e r) j = algebraMap B Q b) → ∃ c : Fin d → Fin d → B, ∀ a j, algebraMap B Q (c a j) = (p : Q) * coeff (Finsupp.single j p) (e (Sum.inl a)) ∧ ∃ b, c a j - U⁻¹ (Sum.inl j) (Sum.inl a) = p * b := by
  intro p _ B Q _ _ _ s σ hs _ d k e U hU h hlin hint
  classical
  set x : Fin d → Fin d ⊕ Fin k → Q := fun j l => (p : Q) * coeff (Finsupp.single j p) (e l) with hx
  have hD : ∀ l i, (U * blk d k (p : B) 1) l i =
      U l i * Sum.elim (fun _ => (p : B)) (fun _ => 1) i := by
    intro l i
    simp [blk, Matrix.mul_diagonal]
  have hco : ∀ i j, coeff (Finsupp.single j p)
      (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e) =
      s (lin (e i) j) - ∑ l, algebraMap B Q (U l i * Sum.elim (fun _ => (p : B)) (fun _ => 1) i) *
        coeff (Finsupp.single j p) (e l) := by
    intro i j
    rw [map_sub, GlobalTheory.FrobCoef.coeff_frob_single, comb, map_sum]
    simp_rw [coeff_smul, hD]
  have key : ∀ j, ∃ y : Fin d ⊕ Fin k → B, (∀ i, ∑ l, algebraMap B Q (U l i) * x j l =
      algebraMap B Q (y i)) ∧ ∀ i, ∃ t, y i - (Pi.single (Sum.inl j) (1 : B) : Fin d ⊕ Fin k → B) i = p * t := by
    intro j
    have H : ∀ i, ∃ yi : B, ∑ l, algebraMap B Q (U l i) * x j l = algebraMap B Q yi ∧
        ∃ t, yi - (Pi.single (Sum.inl j) (1 : B) : Fin d ⊕ Fin k → B) i = p * t := by
      rintro (a | r)
      · obtain ⟨b, hb, hbe⟩ := (h (Sum.inl a)).2 a rfl (Finsupp.single j p)
        obtain ⟨β, rfl⟩ := Ideal.mem_span_singleton'.1 hb
        rw [hco, hlin] at hbe
        refine ⟨(Pi.single a (1 : B) : Fin d → B) j - β * p, ?_, -β, ?_⟩
        · have h1 : s ((Pi.single a (1 : Q) : Fin d → Q) j) = algebraMap B Q ((Pi.single a (1 : B) : Fin d → B) j) := by
            by_cases haj : j = a
            · subst haj; simp
            · simp [Pi.single_apply, haj]
          have hS : ∑ l, algebraMap B Q (U l (Sum.inl a)) * x j l = ∑ l, algebraMap B Q
              (U l (Sum.inl a) * (p : B)) * coeff (Finsupp.single j p) (e l) :=
            Finset.sum_congr rfl fun l _ => by simp only [hx, Sum.elim_inl, map_mul, map_natCast]; ring
          simp only [Sum.elim_inl] at hbe
          rw [hS, map_sub, ← h1]
          linear_combination -hbe
        · by_cases haj : a = j
          · subst haj; simp; ring
          · simp [Pi.single_apply, haj, Ne.symm haj]; ring
      · obtain ⟨b1, -, hb1⟩ := (h (Sum.inr r)).1 (Finsupp.single j p)
        obtain ⟨b0, hb0⟩ := hint (Sum.inr r) j
        rw [hco, hb0, hs] at hb1
        refine ⟨p * (σ b0 - b1), ?_, σ b0 - b1, by simp⟩
        simp only [Sum.elim_inr, mul_one] at hb1
        have : ∑ l, algebraMap B Q (U l (Sum.inr r)) * coeff (Finsupp.single j p) (e l) =
            algebraMap B Q (σ b0 - b1) := by
          rw [map_sub, ← hb1]; ring
        simp only [hx, map_mul, map_natCast, ← this, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => by ring
    choose y hy1 hy2 using H
    exact ⟨y, hy1, hy2⟩
  choose y hy1 hy2 using key
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det U).1 hU)
  refine ⟨fun a j => ∑ i, U⁻¹ i (Sum.inl a) * y j i, fun a j => ⟨?_, ?_⟩⟩
  · have : ∀ m, algebraMap B Q (∑ i, U⁻¹ i m * y j i) = x j m := by
      intro m
      calc algebraMap B Q (∑ i, U⁻¹ i m * y j i)
          = ∑ i, algebraMap B Q (U⁻¹ i m) * ∑ l, algebraMap B Q (U l i) * x j l := by
            simp only [map_sum, map_mul, hy1]
        _ = ∑ l, algebraMap B Q ((U * U⁻¹) l m) * x j l := by
            simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring
        _ = x j m := by
            rw [hUU]
            simp [Matrix.one_apply]
    exact this _
  · choose t ht using hy2 j
    refine ⟨∑ i, U⁻¹ i (Sum.inl a) * t i, ?_⟩
    have h1 : U⁻¹ (Sum.inl j) (Sum.inl a) = ∑ i, U⁻¹ i (Sum.inl a) * (Pi.single (Sum.inl j) (1 : B) : Fin d ⊕ Fin k → B) i := by
      simp [Pi.single_apply]
    rw [h1, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, ht i]; ring

end GlobalTheory.FrobCoef
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_p_logarithms_congr_inv_frobenius_matrix_mod_p : ∀ (p : ℕ) [Fact p.Prime] (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (s : Q →+* Q) (σ : B →+* B), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σ b)) → Function.Injective (algebraMap B Q) → ∀ (d k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) Q) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B), IsUnit U → (∀ i, In (⊤ : Ideal B) (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : B)}) (frob p s (e i) - comb (fun l => (U * blk d k (p : B) 1) l i) e)) → (∀ a, lin (e (Sum.inl a)) = Pi.single a 1) → (∀ r j, ∃ b, lin (e r) j = algebraMap B Q b) → ∃ c : Fin d → Fin d → B, ∀ a j, algebraMap B Q (c a j) = (p : Q) * coeff (Finsupp.single j p) (e (Sum.inl a)) ∧ ∃ b, c a j - U⁻¹ (Sum.inl j) (Sum.inl a) = p * b := by
  atlas_forward_decl GlobalTheory.FrobCoef.coef_logs_inv_frob
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

namespace GlobalTheory.DualFrobNilMat

theorem mulVec_transpose_inv_blk_apply {B : Type} [CommRing B] (σ : B →+* B) (p : ℕ) {d k : ℕ}
    (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B) (w : Fin d ⊕ Fin k → B) (r : Fin d ⊕ Fin k) :
    ((U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ (w j)) r =
      (∑ j : Fin d, U⁻¹ (Sum.inl j) r * σ (w (Sum.inl j))) +
      (p : B) * ∑ j : Fin k, U⁻¹ (Sum.inr j) r * σ (w (Sum.inr j)) := by
  have hU : ∀ r s, U.transpose⁻¹ r s = U⁻¹ s r := fun r s => by
    rw [← Matrix.transpose_nonsing_inv]; rfl
  simp only [Matrix.mulVec, dotProduct, blk, Matrix.mul_diagonal, hU, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_one, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

theorem isNil_of_block : ∀ (B O : Type) [CommRing B] [CommRing O] (θ : B →+* O) (σ : B →+* B) (p : ℕ) (m : Ideal O), θ (p : B) ∈ m → m ≠ ⊤ → (∀ b, ∃ c, σ b - b ^ p = p * c) → ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B) (c : Fin d → Fin d → B), (∀ a j, ∃ b, c a j - U⁻¹ (Sum.inl j) (Sum.inl a) = p * b) → (∃ N : ℕ, ∀ w : Fin d → O ⧸ m, (fun w : Fin d → O ⧸ m => fun a => ∑ j, Ideal.Quotient.mk m (θ (c a j)) * w j ^ p)^[N] w = 0) → IsNil θ σ (U.transpose⁻¹ * blk d k 1 (p : B)) := by
  intro B O _ _ θ σ p m hp hm hσ d k U c hc hS
  obtain ⟨N, hN⟩ := hS
  set ρ : B →+* O ⧸ m := (Ideal.Quotient.mk m).comp θ with hρ
  have hρp : ρ (p : B) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hp
  have hρσ : ∀ b, ρ (σ b) = ρ b ^ p := by
    intro b
    obtain ⟨e, he⟩ := hσ b
    have h := congrArg ρ he
    rw [map_sub, map_mul, map_pow, hρp, zero_mul, sub_eq_zero] at h
    exact h
  have hp0 : p ≠ 0 := by
    rintro rfl
    apply hm
    obtain ⟨e, he⟩ := hσ 0
    simp only [map_zero, pow_zero, zero_sub, Nat.cast_zero, zero_mul, neg_eq_zero] at he
    have h1 : (1 : O) = 0 := by rw [← map_one θ, he, map_zero]
    rw [Ideal.eq_top_iff_one, h1]
    exact m.zero_mem
  have hT : ∀ (w : Fin d ⊕ Fin k → B) r,
      ρ (((U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ (w j)) r) =
        ∑ j, ρ (U⁻¹ (Sum.inl j) r) * ρ (w (Sum.inl j)) ^ p := by
    intro w r
    rw [mulVec_transpose_inv_blk_apply, map_add, map_mul, hρp, zero_mul, add_zero, map_sum]
    simp only [map_mul, hρσ]
  have hinl : ∀ a j, ρ (U⁻¹ (Sum.inl j) (Sum.inl a)) = ρ (c a j) := by
    intro a j
    obtain ⟨e, he⟩ := hc a j
    have h := congrArg ρ he
    rw [map_sub, map_mul, hρp, zero_mul, sub_eq_zero] at h
    exact h.symm
  have hiter : ∀ (t : ℕ) (v : Fin d ⊕ Fin k → B),
      (fun a => ρ (((fun w : Fin d ⊕ Fin k → B =>
        (U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ (w j))^[t] v) (Sum.inl a))) =
      (fun w : Fin d → O ⧸ m => fun a => ∑ j, Ideal.Quotient.mk m (θ (c a j)) * w j ^ p)^[t]
        (fun a => ρ (v (Sum.inl a))) := by
    intro t
    induction t with
    | zero => intro v; rfl
    | succ t ih =>
      intro v
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      funext a
      rw [hT]
      exact Finset.sum_congr rfl fun j _ => by rw [hinl]; rfl
  refine ⟨N + 1, fun v r hu => hm ?_⟩
  rw [Function.iterate_succ_apply'] at hu
  have h0 : ρ (((U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ
      (((fun w : Fin d ⊕ Fin k → B =>
        (U.transpose⁻¹ * blk d k 1 (p : B)).mulVec fun j => σ (w j))^[N] v) j)) r) = 0 := by
    rw [hT]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h := congrFun (hiter N v) j
    rw [hN] at h
    simp only [Pi.zero_apply] at h
    rw [h, zero_pow hp0, mul_zero]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.Quotient.eq_zero_iff_mem.1 h0) hu

end GlobalTheory.DualFrobNilMat
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNilpotent_dualFrobenius_of_block : ∀ (B O : Type) [CommRing B] [CommRing O] (θ : B →+* O) (σ : B →+* B) (p : ℕ) (m : Ideal O), θ (p : B) ∈ m → m ≠ ⊤ → (∀ b, ∃ c, σ b - b ^ p = p * c) → ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B) (c : Fin d → Fin d → B), (∀ a j, ∃ b, c a j - U⁻¹ (Sum.inl j) (Sum.inl a) = p * b) → (∃ N : ℕ, ∀ w : Fin d → O ⧸ m, (fun w : Fin d → O ⧸ m => fun a => ∑ j, Ideal.Quotient.mk m (θ (c a j)) * w j ^ p)^[N] w = 0) → IsNil θ σ (U.transpose⁻¹ * blk d k 1 (p : B)) := by
  atlas_forward_decl GlobalTheory.DualFrobNilMat.isNil_of_block
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory.LocalDualNil

theorem exists_pow_mem_map {O R : Type*} [CommRing O] [CommRing R] [Algebra O R]
    [Module.Finite O R] [IsLocalRing R] (ε : R →ₐ[O] O) (m : Ideal O) (hm : m.IsMaximal) :
    ∃ r : ℕ, ∀ φ : R, ε φ ∈ m → ∀ s, r ≤ s → φ ^ s ∈ m.map (algebraMap O R) := by
  set J : Ideal R := m.map (algebraMap O R) with hJ
  by_cases htop : J = ⊤
  · exact ⟨0, fun φ _ s _ => htop ▸ Submodule.mem_top⟩
  letI : Field (O ⧸ m) := Ideal.Quotient.field m
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 htop
  haveI : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : Module.Finite (O ⧸ m) (R ⧸ J) := Module.Finite.of_restrictScalars_finite O _ _
  haveI : IsArtinianRing (R ⧸ J) := IsArtinianRing.of_finite (O ⧸ m) _
  obtain ⟨r, hr⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ J)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hr
  haveI : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨r, fun φ hφ s hs => ?_⟩
  have h1 : ¬ IsUnit φ := fun h => hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hφ (h.map ε))
  have h2 : Ideal.Quotient.mk J φ ∈ IsLocalRing.maximalIdeal (R ⧸ J) :=
    fun h => h1 (isUnit_of_map_unit _ _ h)
  have h3 := Ideal.pow_mem_pow h2 r
  rw [hr, Submodule.zero_eq_bot, Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] at h3
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [pow_add]
  exact J.mul_mem_right _ h3

theorem exists_pow_apply_mem : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (n : ℕ)
    (m : Ideal O), m.IsMaximal → IsLocalRing (G.dual.A n) → ∃ r : ℕ, ∀ φ : G.dual.A n,
      φ 1 ∈ m → ∀ s, r ≤ s → ∀ a : G.A n, (φ ^ s) a ∈ m := by
  intro p O _ G n m hm hloc
  obtain ⟨r, hr⟩ := exists_pow_mem_map (Bialgebra.counitAlgHom O (G.dual.A n)) m hm
  refine ⟨r, fun φ hφ s hs a => ?_⟩
  have h := hr φ hφ s hs
  generalize φ ^ s = ψ at h
  have h' : ψ ∈ m • (⊤ : Submodule O (G.dual.A n)) := by
    rw [Ideal.smul_top_eq_map]
    exact h
  refine Submodule.smul_induction_on (p := fun ψ : G.dual.A n => ψ a ∈ m) h' ?_ ?_
  · intro c hc χ _
    exact m.mul_mem_right (χ a) hc
  · intro x y hx hy
    exact m.add_mem hx hy

end GlobalTheory.LocalDualNil
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniform_convolution_pow_apply_mem_localDual : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (n : ℕ) (m : Ideal O), m.IsMaximal → IsLocalRing (G.dual.A n) → ∃ r : ℕ, ∀ φ : G.dual.A n, φ 1 ∈ m → ∀ s, r ≤ s → ∀ a : G.A n, (φ ^ s) a ∈ m := by
  atlas_forward_decl GlobalTheory.LocalDualNil.exists_pow_apply_mem
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

namespace GlobalTheory.FrNil

theorem counit_ev_sub_constantCoeff (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
    (c : QLog.Chart G d) (n : ℕ) (F : MvPowerSeries (Fin d) O) :
    (p : O) ∣ Coalgebra.counit (R := O) (c.ev n F) - constantCoeff F := by
  obtain ⟨N, hN⟩ := (c.isEval n).2 1
  set P : MvPolynomial (Fin d) O := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N) F with hP

  have halg : ((Bialgebra.counitAlgHom O (G.A n)).comp
      ((c.ev n).comp (MvPolynomial.coeToMvPowerSeries.algHom O))) =
      MvPolynomial.aeval (fun _ => (0 : O)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply,
      MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply, MvPolynomial.coe_X,
      MvPowerSeries.map_id]
    rw [(c.isEval n).1 i]
    exact c.aug n i
  have hPc : Coalgebra.counit (R := O) (c.ev n (P : MvPowerSeries (Fin d) O)) = constantCoeff F := by
    have := congrArg (fun φ => φ P) halg
    simp only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply,
      Algebra.algebraMap_self, RingHom.id_apply, MvPowerSeries.map_id] at this
    rw [show Coalgebra.counit (R := O) (c.ev n (P : MvPowerSeries (Fin d) O)) =
      Bialgebra.counitAlgHom O (G.A n) (c.ev n (P : MvPowerSeries (Fin d) O)) from rfl, this]
    rw [MvPolynomial.aeval_zero', hP, ← coeff_zero_eq_constantCoeff_apply, Algebra.algebraMap_self,
      RingHom.id_apply, MvPolynomial.constantCoeff_eq, coeff_trunc', if_pos]
    intro i
    exact Nat.zero_le _
  have hT : ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α (F - (P : MvPowerSeries (Fin d) O)) = 0 := by
    intro α hα
    rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos, sub_self]
    intro i
    show α i ≤ N
    exact le_trans (Finsupp.le_degree i α) hα.le
  obtain ⟨a, ha⟩ := hN _ hT
  rw [pow_one] at ha
  have hsplit : c.ev n F = c.ev n (F - (P : MvPowerSeries (Fin d) O)) + c.ev n P := by
    rw [← map_add, sub_add_cancel]
  refine ⟨Coalgebra.counit (R := O) a, ?_⟩
  rw [hsplit, map_add, ha, hPc, add_sub_cancel_right]
  rw [show ((p : G.A n)) * a = (p : O) • a by rw [Algebra.smul_def, map_natCast], map_smul, smul_eq_mul]

end GlobalTheory.FrNil
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.counit_formalChart_ev_sub_constantCoeff_dvd : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (F : MvPowerSeries (Fin d) O), (p : O) ∣ Coalgebra.counit (R := O) (c.ev n F) - constantCoeff F := by
  atlas_forward_decl GlobalTheory.FrNil.counit_ev_sub_constantCoeff
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

namespace GlobalTheory

theorem comul_ev_sub_ev₂_subst_mem :
    ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ)
      (F : MvPowerSeries (Fin d) O), ∃ t : G.A n ⊗[O] G.A n,
        Coalgebra.comul (R := O) (c.ev n F) - c.ev₂ n (subst c.μ F) = (p : O) • t := by
  intro p O _ G d c n F
  have hμ : HasSubst c.μ := hasSubst_of_constantCoeff_zero c.isLaw.const
  let φ₁ : MvPowerSeries (Fin d) O →ₐ[O] G.A n ⊗[O] G.A n :=
    (Bialgebra.comulAlgHom O (G.A n)).comp (c.ev n)
  let φ₂ : MvPowerSeries (Fin d) O →ₐ[O] G.A n ⊗[O] G.A n := (c.ev₂ n).comp (substAlgHom hμ)
  have h1 : ∀ f, φ₁ f = Coalgebra.comul (R := O) (c.ev n f) := fun f => rfl
  have h2 : ∀ f, φ₂ f = c.ev₂ n (subst c.μ f) := fun f => by
    simp only [φ₂, AlgHom.comp_apply, coe_substAlgHom]
  have hpoly : φ₁.comp (MvPolynomial.coeToMvPowerSeries.algHom O) =
      φ₂.comp (MvPolynomial.coeToMvPowerSeries.algHom O) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp only [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply, MvPolynomial.coe_X,
      Algebra.algebraMap_self, MvPowerSeries.map_id, RingHom.id_apply]
    rw [h1, h2, (c.isEval n).1 i, subst_X hμ, c.comul]
  obtain ⟨N₁, hN₁⟩ := (c.isEval n).2 1
  obtain ⟨N₂, hN₂⟩ := (c.isEval₂ n).2 1
  set N := max N₁ N₂
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N) F
  set T := F - (P : MvPowerSeries (Fin d) O)
  have hT : ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α T = 0 := by
    intro α hα
    simp only [T, P, map_sub, MvPolynomial.coeff_coe, coeff_trunc']
    rw [if_pos, sub_self]
    intro i
    show α i ≤ N
    exact le_of_lt (lt_of_le_of_lt (Finsupp.le_degree i α) hα)
  have hPe : φ₁ (P : MvPowerSeries (Fin d) O) = φ₂ (P : MvPowerSeries (Fin d) O) := by
    have := congrArg (fun ψ => ψ P) hpoly
    simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using this
  obtain ⟨a, ha⟩ := hN₁ T fun α hα => hT α (lt_of_lt_of_le hα (le_max_left _ _))
  obtain ⟨b, hb⟩ := hN₂ (subst c.μ T) fun β hβ =>
    coeff_subst_eq_zero_of_degree_lt O (Fin d) (Fin d ⊕ Fin d) c.μ T N c.isLaw.const hT β
      (lt_of_lt_of_le hβ (le_max_right _ _))
  rw [pow_one] at ha hb
  refine ⟨Coalgebra.comul (R := O) a - b, ?_⟩
  have hF : F = (P : MvPowerSeries (Fin d) O) + T := by simp [T]
  rw [← h1, ← h2, hF, map_add, map_add, hPe, add_sub_add_left_eq_sub, h1, h2, ha, hb,
    ← Bialgebra.comulAlgHom_apply, map_mul, map_natCast, Bialgebra.comulAlgHom_apply,
    ← mul_sub, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

end GlobalTheory
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comul_chart_sub_subst_mem_p_smul : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (F : MvPowerSeries (Fin d) O), ∃ t : G.A n ⊗[O] G.A n, Coalgebra.comul (R := O) (c.ev n F) - c.ev₂ n (subst c.μ F) = (p : O) • t := by
  atlas_forward_decl GlobalTheory.comul_ev_sub_ev₂_subst_mem
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

namespace GlobalTheory.PairingEv

theorem mem_of_monomial_mem_of_tail_mem {σ R : Type} [CommRing R] [Fintype σ]
    (S : Submodule R (MvPowerSeries σ R)) (N : ℕ) (h1 : ∀ γ : σ →₀ ℕ, monomial γ (1 : R) ∈ S)
    (h2 : ∀ T : MvPowerSeries σ R, (∀ α : σ →₀ ℕ, α.degree < N → coeff α T = 0) → T ∈ S)
    (H : MvPowerSeries σ R) : H ∈ S := by
  classical
  have hP : ∀ P : MvPolynomial σ R, (P : MvPowerSeries σ R) ∈ S := fun P => by
    induction P using MvPolynomial.induction_on' with
    | monomial γ a =>
      rw [MvPolynomial.coe_monomial]
      have := S.smul_mem a (h1 γ)
      rwa [← map_smul, smul_eq_mul, mul_one] at this
    | add P Q hP hQ => rw [MvPolynomial.coe_add]; exact S.add_mem hP hQ
  have := S.add_mem (hP (trunc' R (Finsupp.equivFunOnFinite.symm fun _ => N) H))
    (h2 (H - (trunc' R (Finsupp.equivFunOnFinite.symm fun _ => N) H : MvPolynomial σ R)) ?_)
  · simpa using this
  · intro α hα
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos, sub_self]
    intro j
    exact (Finsupp.le_degree j α).trans hα.le

theorem coeff_atZero_pderiv_inr {R : Type} [CommRing R] {d : ℕ}
    (H : MvPowerSeries (Fin d ⊕ Fin d) R) (i : Fin d) (α : Fin d →₀ ℕ) :
    coeff α (atZero (pderiv R (Sum.inr i) H)) =
      coeff (α.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1) H := by
  rw [atZero, (coeff_subst_restrict_sum _).1, coeff_pderiv,
    Finsupp.mapDomain_of_notMem_range _ _ (by simp)]
  simp

theorem atZero_pderiv_inr_monomial {R : Type} [CommRing R] {d : ℕ} (α β : Fin d →₀ ℕ) (i : Fin d) :
    atZero (pderiv R (Sum.inr i) (monomial (α.sumElim β) (1 : R))) =
      lin (monomial β (1 : R)) i • monomial α (1 : R) := by
  classical
  ext γ
  rw [coeff_atZero_pderiv_inr, map_smul, lin, coeff_monomial, coeff_monomial, coeff_monomial]
  have : γ.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1 = γ.sumElim (Finsupp.single i 1) := by
    rw [Finsupp.sumElim_eq_add, Finsupp.mapDomain_single]
  rw [this]
  have h2 : γ.sumElim (Finsupp.single i 1) = α.sumElim β ↔ γ = α ∧ Finsupp.single i 1 = β := by
    constructor
    · intro h
      exact ⟨Finsupp.ext fun j => by simpa using DFunLike.congr_fun h (Sum.inl j),
        Finsupp.ext fun j => by simpa using DFunLike.congr_fun h (Sum.inr j)⟩
    · rintro ⟨rfl, rfl⟩; rfl
  simp only [h2]
  by_cases h3 : γ = α <;> by_cases h4 : Finsupp.single i 1 = β <;> simp [h3, h4]

theorem chart_ev₂_monomial {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ}
    (c : QLog.Chart G d) (n : ℕ) (α β : Fin d →₀ ℕ) :
    c.ev₂ n (monomial (α.sumElim β) 1) = c.ev n (monomial α 1) ⊗ₜ[O] c.ev n (monomial β 1) := by
  simp only [monomial_one_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [map_mul, map_prod, map_pow, (c.isEval n).1, (c.isEval₂ n).1, Sum.elim_inl,
    Sum.elim_inr, Finsupp.sumElim_inl, Finsupp.sumElim_inr]
  have e1 := map_prod (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] G.A n)
    (fun j => c.x n j ^ α j) Finset.univ
  have e2 := map_prod (Algebra.TensorProduct.includeRight : G.A n →ₐ[O] G.A n ⊗[O] G.A n)
    (fun j => c.x n j ^ β j) Finset.univ
  simp only [map_pow, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply] at e1 e2
  rw [← e1, ← e2, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem pairing_ev₂_sub_mem : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (m : Ideal O), (p : O) ∈ m → ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m) → ∀ (ψ : G.A n →ₗ[O] O) (H : MvPowerSeries (Fin d ⊕ Fin d) O), LinearMap.mul' O O (TensorProduct.map ψ φ.ofConv (c.ev₂ n H)) - ψ (c.ev n (∑ i, u i • atZero (pderiv O (Sum.inr i) H))) ∈ m := by
  intro p O _ G d c n m hp u φ hφ ψ H
  obtain ⟨N₁, h₁⟩ := (c.isEval n).2 1
  obtain ⟨N₂, h₂⟩ := (c.isEval₂ n).2 1
  have hs : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ : Fin d => 0)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp)
  let D : MvPowerSeries (Fin d ⊕ Fin d) O →ₗ[O] MvPowerSeries (Fin d) O :=
    ∑ i, u i • ((substAlgHom hs).toLinearMap ∘ₗ (pderiv O (Sum.inr i)).toLinearMap)
  have hD : ∀ H, D H = ∑ i, u i • atZero (pderiv O (Sum.inr i) H) := fun H => by
    simp [D, atZero, LinearMap.sum_apply, coe_substAlgHom]
  let P : G.A n ⊗[O] G.A n →ₗ[O] O := LinearMap.mul' O O ∘ₗ TensorProduct.map ψ φ.ofConv
  let L : MvPowerSeries (Fin d ⊕ Fin d) O →ₗ[O] O :=
    P ∘ₗ (c.ev₂ n).toLinearMap - ψ ∘ₗ (c.ev n).toLinearMap ∘ₗ D
  have hL : ∀ H, L H = P (c.ev₂ n H) - ψ (c.ev n (∑ i, u i • atZero (pderiv O (Sum.inr i) H))) :=
    fun H => by rw [← hD]; rfl
  have key := mem_of_monomial_mem_of_tail_mem (Submodule.comap L m) (N₁ + N₂ + 1) ?_ ?_ H
  · rw [Submodule.mem_comap, hL] at key
    exact key
  · intro γ
    rw [Submodule.mem_comap, hL, ← Finsupp.comapDomain_sumElim_comapDomain γ]
    generalize Finsupp.comapDomain Sum.inl γ _ = α
    generalize Finsupp.comapDomain Sum.inr γ _ = β
    rw [chart_ev₂_monomial]
    simp only [atZero_pderiv_inr_monomial, smul_smul, ← Finset.sum_smul, map_smul, smul_eq_mul]
    have := m.mul_mem_left (ψ (c.ev n (monomial α 1))) (hφ (monomial β 1))
    convert this using 1
    have e : P (c.ev n (monomial α 1) ⊗ₜ[O] c.ev n (monomial β 1)) =
        ψ (c.ev n (monomial α 1)) * φ (c.ev n (monomial β 1)) := by
      simp only [P, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply]
    rw [e]; ring
  · intro T hT
    rw [Submodule.mem_comap, hL]
    obtain ⟨a, ha⟩ := h₂ T fun α hα => hT α (by omega)
    obtain ⟨b, hb⟩ := h₁ (∑ i, u i • atZero (pderiv O (Sum.inr i) T)) fun α hα => by
      rw [map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, coeff_atZero_pderiv_inr, hT, smul_zero]
      rw [map_add, Finsupp.degree_mapDomain, Finsupp.degree_single]
      omega
    rw [ha, hb, pow_one, pow_one, ← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul, map_nsmul,
      nsmul_eq_mul, nsmul_eq_mul]
    exact m.sub_mem (m.mul_mem_right _ hp) (m.mul_mem_right _ hp)

end GlobalTheory.PairingEv
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_pairing_chart_partial_derivative_mod_max : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (m : Ideal O), (p : O) ∈ m → ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m) → ∀ (ψ : G.A n →ₗ[O] O) (H : MvPowerSeries (Fin d ⊕ Fin d) O), LinearMap.mul' O O (TensorProduct.map ψ φ.ofConv (c.ev₂ n H)) - ψ (c.ev n (∑ i, u i • atZero (pderiv O (Sum.inr i) H))) ∈ m := by
  atlas_forward_decl GlobalTheory.PairingEv.pairing_ev₂_sub_mem
end

section
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
  GlobalTheory.LawDer TensorProduct

namespace GlobalTheory.LawDer

theorem convPow_ev_sub_constantCoeff_iterate_mem : ∀ (p : ℕ) (O : Type) [CommRing O]
    (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (m : Ideal O), (p : O) ∈ m →
    ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m) →
    ∀ (k : ℕ) (F : MvPowerSeries (Fin d) O),
      (φ ^ k) (c.ev n F) - constantCoeff ((invDer c.μ u)^[k] F) ∈ m := by
  intro p O _ G d c n m hp u φ hφ k
  induction k with
  | zero =>
    intro F
    obtain ⟨a, ha⟩ := GlobalTheory.T.counit_formalChart_ev_sub_constantCoeff_dvd p O G d c n F
    rw [pow_zero, Function.iterate_zero, id, LinearMap.convOne_apply, Algebra.algebraMap_self,
      RingHom.id_apply, ha]
    exact m.mul_mem_right a hp
  | succ k ih =>
    intro F
    obtain ⟨t, ht⟩ := GlobalTheory.T.comul_chart_sub_subst_mem_p_smul p O G d c n F
    rw [pow_succ, LinearMap.convMul_apply, Function.iterate_succ_apply, sub_eq_iff_eq_add.1 ht,
      map_add, map_add, map_smul, map_smul]
    have h1 := GlobalTheory.T.dual_pairing_chart_partial_derivative_mod_max p O G d c n m hp u φ hφ (φ ^ k).ofConv (subst c.μ F)
    have h2 := ih (invDer c.μ u F)
    have h3 : (p : O) • LinearMap.mul' O O (TensorProduct.map (φ ^ k).ofConv φ.ofConv t) ∈ m := by
      rw [smul_eq_mul]; exact m.mul_mem_right _ hp
    have := m.add_mem (m.add_mem h1 h2) h3
    convert this using 1
    simp only [invDer]
    ring

end GlobalTheory.LawDer
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convPow_ofConv_sub_constantCoeff_invariantDerivation : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (m : Ideal O), (p : O) ∈ m → ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m) → ∀ (k : ℕ) (F : MvPowerSeries (Fin d) O), (φ ^ k) (c.ev n F) - constantCoeff ((invDer c.μ u)^[k] F) ∈ m := by
  atlas_forward_decl GlobalTheory.LawDer.convPow_ev_sub_constantCoeff_iterate_mem
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem GlobalTheory.QLog.Chart.exists_dual_lift_lin : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (m : Ideal O), (p : O) ∈ m → ∃ n : ℕ, ∀ u : Fin d → O, ∃ φ : G.dual.A n, ∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m := by
  intro p O _ G d c m hp
  obtain ⟨n, hn⟩ := c.ker 1 2
  refine ⟨n, fun u => ?_⟩
  let L : MvPowerSeries (Fin d) O →ₗ[O] O := ∑ i, u i • coeff (Finsupp.single i 1)
  have hL : ∀ F, L F = ∑ i, u i * lin F i := fun F => by simp [L, LinearMap.sum_apply, lin]
  let f : MvPowerSeries (Fin d) O →ₗ[O] O ⧸ m := m.mkQ ∘ₗ L
  have hk : LinearMap.ker (c.ev n).toLinearMap ≤ LinearMap.ker f := by
    intro F hF
    have h := hn F hF
    change Ideal.Quotient.mk m (L F) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hL]
    refine Submodule.sum_mem _ fun i _ => m.mul_mem_left _ ?_
    obtain ⟨a, ha⟩ := h (Finsupp.single i 1) (by simp)
    have : lin F i = p ^ 1 * a := ha
    rw [this, pow_one]
    exact m.mul_mem_right _ hp
  let g : G.A n →ₗ[O] O ⧸ m := (LinearMap.ker (c.ev n).toLinearMap).liftQ f hk ∘ₗ
    ((c.ev n).toLinearMap.quotKerEquivOfSurjective (c.surj n)).symm.toLinearMap
  have hg : ∀ F, g (c.ev n F) = f F := fun F => by
    have : ((c.ev n).toLinearMap.quotKerEquivOfSurjective (c.surj n)).symm (c.ev n F) =
        Submodule.Quotient.mk F := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property m.mkQ g m.mkQ_surjective
  refine ⟨WithConv.toConv φ, fun F => ?_⟩
  rw [← hL, ← Submodule.Quotient.eq]
  exact (LinearMap.congr_fun hφ (c.ev n F)).trans (hg F)
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartierDual_lift_linearCoefficients_mod : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (m : Ideal O), (p : O) ∈ m → ∃ n : ℕ, ∀ u : Fin d → O, ∃ φ : G.dual.A n, ∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m := by
  atlas_forward_decl GlobalTheory.QLog.Chart.exists_dual_lift_lin
end

section
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem GlobalTheory.DualFrobNil.isNil_dual_frobenius : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → IsConn G.dual → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, IsUnit U → (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hL hμ k e hB hA hconn U hU hfr
  obtain ⟨m, hmax, hpm⟩ := Ideal.exists_le_maximal (Ideal.span {(p : O)}) (by
    rw [Ne, Ideal.span_singleton_eq_top]; exact Fact.out)
  have hp : (p : O) ∈ m := hpm (Ideal.mem_span_singleton_self _)
  obtain ⟨c', hc'⟩ := GlobalTheory.T.coeff_p_logarithms_congr_inv_frobenius_matrix_mod_p p F.B F.Q F.s F.σ F.s_alg F.frame.inj d k e U hU hfr (fun a => (hA a).2)
    (fun r j => by obtain ⟨b, -, hb⟩ := (hB.1 r).2.1 j; exact ⟨b, hb⟩)
  refine GlobalTheory.T.isNilpotent_dualFrobenius_of_block F.B O F.θ F.σ p m (by rw [map_natCast]; exact hp) hmax.ne_top
    (fun b => by obtain ⟨c, hc⟩ := F.σ_pow b; exact ⟨c, hc⟩) d k U c' (fun a j => (hc' a j).2) ?_
  set Sh : (Fin d → O ⧸ m) → (Fin d → O ⧸ m) :=
    fun w a => ∑ j, Ideal.Quotient.mk m (F.θ (c' a j)) * w j ^ p with hSh
  obtain ⟨n, hlift⟩ := GlobalTheory.T.exists_cartierDual_lift_linearCoefficients_mod p O G d c m hp
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_uniform_convolution_pow_apply_mem_localDual p O G n m hmax (hconn n)
  have hθ : ∀ x ∈ RingHom.ker F.θ ⊔ Ideal.span {(p : F.B)}, F.θ x ∈ m := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    rw [map_add, RingHom.mem_ker.1 hy, zero_add, map_mul, map_natCast]
    exact m.mul_mem_left _ hp
  have step : ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ Fs, φ (c.ev n Fs) - ∑ i, u i * lin Fs i ∈ m) →
      ∃ u' : Fin d → O, (∀ Fs, (φ ^ p) (c.ev n Fs) - ∑ i, u' i * lin Fs i ∈ m) ∧
        (fun a => Ideal.Quotient.mk m (u' a)) = Sh (fun a => Ideal.Quotient.mk m (u a)) := by
    intro u φ hφ
    refine ⟨fun a => constantCoeff ((invDer c.μ u)^[p] (X a)), fun Fs => ?_, ?_⟩
    · obtain ⟨t, ht⟩ := GlobalTheory.T.constantCoeff_iterate_invariant_derivation_linear p O d c.μ c.isLaw.const c.isLaw.unit c.isLaw.comm u Fs
      have h1 := GlobalTheory.T.convPow_ofConv_sub_constantCoeff_invariantDerivation p O G d c n m hp u φ hφ p Fs
      have h2 : (p : O) * t ∈ m := m.mul_mem_right t hp
      have e1 : (φ ^ p) (c.ev n Fs) - ∑ i, constantCoeff ((invDer c.μ u)^[p] (X i)) * lin Fs i =
          ((φ ^ p) (c.ev n Fs) - constantCoeff ((invDer c.μ u)^[p] Fs)) + p * t := by
        rw [← ht]; simp only [lin]; ring
      rw [e1]; exact m.add_mem h1 h2
    · funext a
      choose ũ hũ using fun i => F.frame.surj (u i)
      have hnat := GlobalTheory.T.map_invariantDerivationFormalGroupLaw_iterate F.B O F.θ d μ' hL.const ũ p (X a)
      have hmu : (fun i => map F.θ (μ' i)) = c.μ := funext hμ
      have hu : (fun i => F.θ (ũ i)) = u := funext hũ
      rw [hmu, hu, map_X] at hnat
      have key := hθ _ (GlobalTheory.T.constantCoeff_pIterate_invariantDerivation_coord p F.B O F.Q F.θ F.frame d μ' hL (e (Sum.inl a)) a (hB.1 _) (hA a).1
        (hA a).2 (c' a) (fun i => (hc' a i).1) ũ)
      have hcc : constantCoeff ((invDer c.μ u)^[p] (X a)) =
          F.θ (constantCoeff ((invDer μ' ũ)^[p] (X a))) := by
        rw [← hnat, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]
      simp only [hSh]
      rw [hcc, ← hu]
      simp only [← map_pow, ← map_mul, ← map_sum]
      rw [Ideal.Quotient.eq]
      simpa [map_sub, map_sum, map_mul, map_pow] using key
  have iter : ∀ t (u : Fin d → O) (φ : G.dual.A n), (∀ Fs, φ (c.ev n Fs) - ∑ i, u i * lin Fs i ∈ m) →
      ∃ u' : Fin d → O, (∀ Fs, (φ ^ (p ^ t)) (c.ev n Fs) - ∑ i, u' i * lin Fs i ∈ m) ∧
        (fun a => Ideal.Quotient.mk m (u' a)) = Sh^[t] (fun a => Ideal.Quotient.mk m (u a)) := by
    intro t
    induction t with
    | zero => intro u φ hφ; exact ⟨u, by simpa using hφ, rfl⟩
    | succ t ih =>
      intro u φ hφ
      obtain ⟨u1, h1, e1⟩ := ih u φ hφ
      obtain ⟨u2, h2, e2⟩ := step u1 _ h1
      refine ⟨u2, fun Fs => ?_, ?_⟩
      · rw [pow_succ, pow_mul]; exact h2 Fs
      · rw [e2, e1, Function.iterate_succ_apply']
  refine ⟨r, fun w => ?_⟩
  obtain ⟨u, rfl⟩ : ∃ u : Fin d → O, (fun a => Ideal.Quotient.mk m (u a)) = w :=
    ⟨fun a => (Ideal.Quotient.mk_surjective (w a)).choose,
      funext fun a => (Ideal.Quotient.mk_surjective (w a)).choose_spec⟩
  obtain ⟨φ, hφ⟩ := hlift u
  obtain ⟨u', h', e'⟩ := iter r u φ hφ
  rw [← e']
  funext a
  have h1 : φ 1 ∈ m := by
    have := hφ 1
    simpa [lin, coeff_one] using this
  have hle : r ≤ p ^ r := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have h3 := hr φ h1 (p ^ r) hle (c.x n a)
  have h4 := h' (X a)
  rw [(c.isEval n).1 a] at h4
  have hs : ∑ i, u' i * lin (X a : MvPowerSeries (Fin d) O) i = u' a := by
    simp [lin, coeff_X, Finsupp.single_eq_single_iff]
  rw [hs] at h4
  have h5 : u' a ∈ m := by
    have := m.sub_mem h3 h4
    simpa using this
  simpa [Ideal.Quotient.eq_zero_iff_mem] using h5
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNil_dual_frobenius_alt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → IsConn G.dual → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, IsUnit U → (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) := by
  atlas_forward_decl GlobalTheory.DualFrobNil.isNil_dual_frobenius
end
