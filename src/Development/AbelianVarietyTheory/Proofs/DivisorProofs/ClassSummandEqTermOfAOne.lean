import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CxTotalEqFullSumIrrOfCxCountReg
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyOfRegAfOfFixL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntOfDenLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalTermIntegralExpression
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderIsHopfOrderNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicBoundedPolynomials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDenominatorIntegralPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyPadicBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyBoundedDenominators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeFactorFormGroupBoundedOfTestSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumConjClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairWeightInvariantFormGroupConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalSumAtPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabEqStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixLineConjIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianPositivityInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeightedPairOrbitsOfFiniteWeightedFixedPoiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullSumRegroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairsSameSimilitude
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistedUnitCommutes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsConjOfMinpolyEqOfSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalSupportFinitePrimeSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyKottwitzLatticeSeparableMinpolyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTauFixedUnitCentralizerIsNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFixedUnitClassesCentralizerRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralTestFunctionSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMarkedPairClassesDegreeOneTermNeZero

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.FinPolysIrr

theorem eig_norm_sq_of_a_one (p : ℕ) [Fact p.Prime] (G : HTGroup p) (ha : G.a = 1) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (β : G.Cˣ) (hβ : sh G β = β) (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1)
    (y : grp G β) (a : PosV G v β) (hfix : FixL G v β y a.1) (w : InfinitePlace G.F) (μ : ℂ)
    (x : Fin G.n → ℂ) (hx : x ≠ 0) (hμ : G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) *ᵥ x = μ • x) :
    ‖μ‖ ^ 2 = ((((y : G.Cˣ × ℚˣ).2 : ℚ)) : ℝ) := by
  obtain ⟨-, -, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G w β hβ hR
  have hsim := GlobalTheory.LKCx.grp_similitude_herm p G w β y
  have hs0 : (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast ((y : G.Cˣ × ℚˣ).2).ne_zero
  have hsig := G.sig w
  refine GlobalTheory.eig_norm_sq_of_similitude G.n (G.gram w) (herm G w β) (toV G w β y : Matrix (Fin G.n) (Fin G.n) ℂ)
    (G.gram_herm w) Z _ ?_ ?_ hZ hs0 ?_ ?_ μ x hx hμ
  · rcases hsig with h | h <;> omega
  · have := G.n_pos
    rcases hsig with h | h <;> omega
  · rw [Complex.ofReal_ratCast]; exact hsim
  · by_cases hw : w = v
    · subst hw
      obtain ⟨c, hc⟩ := hfix
      exact Or.inr ⟨c, a.1, hc, a.2⟩
    · left
      have h1 : sigPosH (G.gram_herm w) ≠ 1 := by
        intro h1
        have hcard : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} ≤ 1 := ha.le
        have := Fintype.card_le_one_iff.1 hcard ⟨w, h1⟩ ⟨v, hv⟩
        exact hw (congrArg Subtype.val this)
      rcases hsig with h | h
      · exact absurd h.1 h1
      · exact h.1

theorem minpoly_coeff_bdd_of_a_one (p : ℕ) [Fact p.Prime] (G : HTGroup p) (ha : G.a = 1)
    (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) (β : G.Cˣ) (hβ : sh G β = β)
    (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) (S : ℝ) : ∃ B : ℝ, ∀ (y : grp G β) (a : PosV G v β),
    FixL G v β y a.1 → (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≤ S → ∀ (φ : G.F →+* ℂ) (k : ℕ),
    ‖φ ((minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k)‖ ≤ B := by
  refine ⟨max (√(max S 0)) 1 ^ (G.n ^ 2) * ((G.n ^ 2).choose (G.n ^ 2 / 2) : ℝ), ?_⟩
  intro y a hfix hS φ k
  set γ : G.C := (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hγ
  have hint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hdeg : (minpoly G.F γ).natDegree ≤ G.n ^ 2 := G.rankC ▸ minpoly.natDegree_le γ
  have hbd : ∀ (w : InfinitePlace G.F) (z : ℂ), (minpoly G.F γ).eval₂ w.embedding z = 0 → ‖z‖ ≤ √(max S 0) := by
    intro w z hz
    obtain ⟨x, hx, hzx⟩ := GlobalTheory.LKCx.PolyArch.roots_eig_any p G w γ z hz
    have h2 := eig_norm_sq_of_a_one p G ha v hv β hβ hR y a hfix w z x hx hzx
    have h3 : ‖z‖ ^ 2 ≤ max S 0 := h2 ▸ le_max_of_le_left hS
    simpa using Real.abs_le_sqrt h3
  have hroots : ∀ z ∈ ((minpoly G.F γ).map φ).roots, ‖z‖ ≤ √(max S 0) := by
    intro z hz
    have hr : (minpoly G.F γ).eval₂ φ z = 0 := by
      have := (Polynomial.mem_roots'.1 hz).2
      rwa [Polynomial.IsRoot, Polynomial.eval_map] at this
    rcases InfinitePlace.embedding_mk_eq φ with h | h
    · rw [← h] at hr; exact hbd _ z hr
    · have hr' : (minpoly G.F γ).eval₂ (InfinitePlace.mk φ).embedding (starRingEnd ℂ z) = 0 := by
        rw [h]
        have := congrArg (starRingEnd ℂ) hr
        rw [map_zero, Polynomial.hom_eval₂] at this
        convert this using 2
        exact RingHom.ext fun x => rfl
      simpa using hbd _ _ hr'
  have := Polynomial.coeff_bdd_of_roots_le φ (minpoly.monic hint) (IsAlgClosed.splits _) hdeg hroots k
  rwa [Polynomial.coeff_map] at this

end GlobalTheory.LKCx.FinPolysIrr

namespace GlobalTheory.LKCx

open GlobalTheory.LKCx.FinPolysIrr in

theorem finite_minpoly_fix_a_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → Set.Finite {P : Polynomial G.F | ∃ (y : grp G β) (a : Dat G v β), P = minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0} := by
  intro p _ G ha v hv L f hf K' f' hf' β x t hx hsym hR
  obtain ⟨D, hD, hDy⟩ := GlobalTheory.T.minpoly_bounded_denominators p G L f hf β x t hx
  obtain ⟨Bp, hBp⟩ := GlobalTheory.T.minpoly_padic_bounded p G K' f' hf' β
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.bounded_denominator_integral_power G.F p Bp
  obtain ⟨S, hS⟩ := GlobalTheory.T.similitudeFactor_formGroup_bounded_of_test_support p G L f hf K' f' hf' β x t hx
  obtain ⟨B, hB⟩ := minpoly_coeff_bdd_of_a_one p G ha v hv β hsym hR S
  have hpD : 0 < p ^ m₀ * D := Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos _) hD
  refine (GlobalTheory.T.finite_monic_bounded_polynomials G.F (G.n ^ 2) (p ^ m₀ * D) B hpD).subset ?_
  rintro P ⟨y, a, rfl, hfix, hne⟩
  have h1 : f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) ≠ 0 := left_ne_zero_of_mul hne
  have h2 : f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0 := right_ne_zero_of_mul hne
  have hint : IsIntegral G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := Algebra.IsIntegral.isIntegral _
  refine ⟨minpoly.monic hint, ?_, fun k => ⟨?_, fun φ => hB y a.2 hfix (hS y a.1.1 a.1.2 h1 h2) φ k⟩⟩
  · rw [← G.rankC]; exact minpoly.natDegree_le _
  · have := hm₀ _ D (hDy y a.1.1 h1 k) (fun φ => hBp y a.1.2 h2 φ k)
    push_cast
    simpa [mul_assoc] using this

example : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → Set.Finite {P : Polynomial G.F | ∃ (y : grp G β) (a : Dat G v β), P = minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0} :=
  finite_minpoly_fix_a_one

end GlobalTheory.LKCx
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbital_term_real_trivialisation : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → Set.Finite {P : Polynomial G.F | ∃ (y : grp G β) (a : Dat G v β), P = minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0} := by
  first | (exact @GlobalTheory.LKCx.finite_minpoly_fix_a_one) | (exact GlobalTheory.LKCx.finite_minpoly_fix_a_one) | (intros; apply GlobalTheory.LKCx.finite_minpoly_fix_a_one  <;> assumption)
end

section
namespace GlobalTheory.ClassPart

private lemma summand_conj {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) (η : Γ) (y : Y) (γ : Γ) :
    ((Nat.card (MulAction.stabilizer Γ (η • y) ⊓ Subgroup.centralizer {η * γ * η⁻¹} : Subgroup Γ) : ℕ) : ℂ)⁻¹ *
        F (η • y) (η * γ * η⁻¹) =
      ((Nat.card (MulAction.stabilizer Γ y ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F y γ := by
  rw [hF]
  congr 3
  symm
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (MulAut.conj η).toEquiv ?_
  intro s
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
    MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff, mul_smul, inv_smul_smul, smul_left_cancel_iff]
  refine and_congr_right (fun _ => ?_)
  rw [show η * s * η⁻¹ * (η * γ * η⁻¹) = η * (s * γ) * η⁻¹ by group,
    show η * γ * η⁻¹ * (η * s * η⁻¹) = η * (γ * s) * η⁻¹ by group, mul_left_inj, mul_right_inj]

theorem orbitSum_conj : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → ∀ (γ g : Γ), ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) γ = ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {g * γ * g⁻¹}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {g * γ * g⁻¹} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (g * γ * g⁻¹) := by
  intro Γ Y _ _ F hF γ g
  set S : Γ → Y → ℂ := fun c y =>
    ((Nat.card (MulAction.stabilizer Γ y ⊓ Subgroup.centralizer {c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F y c with hSdef
  have hS : ∀ (η : Γ) (y : Y) (c : Γ), S (η * c * η⁻¹) (η • y) = S c y := fun η y c => summand_conj F hF η y c
  have hZ : ∀ (c : Γ) (ζ : Γ), ζ ∈ Subgroup.centralizer {c} → ∀ y, S c (ζ • y) = S c y := by
    intro c ζ hζ y
    have hcj : ζ * c * ζ⁻¹ = c := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hζ
      rw [hζ]; group
    have := hS ζ y c
    rwa [hcj] at this
  set γ' := g * γ * g⁻¹ with hγ'
  have hrel : ∀ a b : Y, (MulAction.orbitRel (Subgroup.centralizer {γ}) Y) a b ↔
      (MulAction.orbitRel (Subgroup.centralizer {γ'}) Y) (g • a) (g • b) := by
    intro a b
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Subtype.exists, Subgroup.mk_smul]
    constructor
    · rintro ⟨ζ, hζ, h⟩
      refine ⟨g * ζ * g⁻¹, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hζ ⊢
        rw [hγ']
        rw [show g * ζ * g⁻¹ * (g * γ * g⁻¹) = g * (ζ * γ) * g⁻¹ by group,
          show g * γ * g⁻¹ * (g * ζ * g⁻¹) = g * (γ * ζ) * g⁻¹ by group, hζ]
      · rw [← h]; simp [mul_smul]
    · rintro ⟨ζ, hζ, h⟩
      refine ⟨g⁻¹ * ζ * g, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hζ ⊢
        rw [hγ'] at hζ
        have h2 : g⁻¹ * (g * γ * g⁻¹ * ζ) * g = g⁻¹ * (ζ * (g * γ * g⁻¹)) * g := by rw [hζ]
        rw [show g⁻¹ * (g * γ * g⁻¹ * ζ) * g = γ * (g⁻¹ * ζ * g) by group,
          show g⁻¹ * (ζ * (g * γ * g⁻¹)) * g = g⁻¹ * ζ * g * γ by group] at h2
        exact h2.symm
      · have := congrArg (g⁻¹ • ·) h
        simpa [mul_smul] using this
  let e : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ}) Y ≃
      MulAction.orbitRel.Quotient (Subgroup.centralizer {γ'}) Y :=
    Quotient.congr (MulAction.toPerm g) hrel
  change ∑ᶠ o, S γ (Quotient.out o) = ∑ᶠ o, S γ' (Quotient.out o)
  rw [← finsum_comp_equiv e]
  apply finsum_congr
  intro o
  have hmk : (Quotient.mk _ (Quotient.out (e o)) : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ'}) Y) =
      Quotient.mk _ (g • Quotient.out o) := by
    rw [Quotient.out_eq]
    conv_lhs => rw [← Quotient.out_eq o]
    rfl
  have hr := Quotient.exact hmk
  have hr' : Quotient.out (e o) ∈ MulAction.orbit (Subgroup.centralizer {γ'}) (g • Quotient.out o) := hr
  rw [MulAction.mem_orbit_iff] at hr'
  obtain ⟨ζ, hζ⟩ := hr'
  rw [← hζ, Subgroup.smul_def, hZ γ' ζ ζ.2, hγ', hS]

end GlobalTheory.ClassPart
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_orbit_sum_conjugate : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → ∀ (γ g : Γ), ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) γ = ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {g * γ * g⁻¹}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {g * γ * g⁻¹} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (g * γ * g⁻¹) := by
  first | (exact @GlobalTheory.ClassPart.orbitSum_conj) | (exact GlobalTheory.ClassPart.orbitSum_conj) | (intros; apply GlobalTheory.ClassPart.orbitSum_conj <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairWeight_invariant_form_group_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), ∀ (η : grp G β) (a : GlobalTheory.CxUnfold.Ys G v β x t hx Kf K') (y : grp G β), GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (η • a) (η * y * η⁻¹) = GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' a y := by
  first | (exact @GlobalTheory.CxUnfold.cxF_smul_conj_gen) | (exact GlobalTheory.CxUnfold.cxF_smul_conj_gen) | (intros; apply GlobalTheory.CxUnfold.cxF_smul_conj_gen  <;> assumption)
end

section
open GlobalTheory.LKCount

namespace GlobalTheory.LKCount

variable {Γ G : Type} [Group Γ] [Group G]

noncomputable def doubleCosetToOrbit (ι : Γ →* G) (H : Subgroup Γ) (K : Subgroup G) :
    DoubleCoset.Quotient ((H.map ι : Subgroup G) : Set G) (K : Set G) →
      MulAction.orbitRel.Quotient H (LeftCosets ι K) :=
  Quotient.lift (fun x => (Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K x))) (by
    intro a b hab
    obtain ⟨_, ⟨h, hh, rfl⟩, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hab
    refine (Quotient.sound ?_).symm
    refine ⟨⟨h, hh⟩, ?_⟩
    show LeftCosets.mk ι K (ι h * a) = LeftCosets.mk ι K (ι h * a * k)
    rw [LeftCosets.mk_eq_mk]
    convert hk using 1
    group)

theorem doubleCosetToOrbit_mk (ι : Γ →* G) (H : Subgroup Γ) (K : Subgroup G) (x : G) :
    doubleCosetToOrbit ι H K (DoubleCoset.mk _ _ x) =
      Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K x) := rfl

theorem doubleCosetToOrbit_bijective (ι : Γ →* G) (H : Subgroup Γ) (K : Subgroup G) :
    Function.Bijective (doubleCosetToOrbit ι H K) := by
  constructor
  · intro p q hpq
    rw [← DoubleCoset.out_eq' _ _ p, ← DoubleCoset.out_eq' _ _ q] at hpq ⊢
    rw [doubleCosetToOrbit_mk, doubleCosetToOrbit_mk] at hpq
    obtain ⟨h, hh⟩ := Quotient.exact hpq
    have hh' : LeftCosets.mk ι K (ι (h : Γ) * q.out) = LeftCosets.mk ι K p.out := hh
    rw [LeftCosets.mk_eq_mk] at hh'
    refine ((DoubleCoset.eq _ _ _ _).2 ⟨ι h, Subgroup.mem_map_of_mem ι h.2, _, hh', ?_⟩).symm
    group
  · intro o
    induction o using Quotient.inductionOn with
    | h y =>
      refine ⟨DoubleCoset.mk _ _ (LeftCosets.rep ι K y), ?_⟩
      rw [doubleCosetToOrbit_mk, LeftCosets.mk_rep]

theorem finsum_doubleCoset_eq_finsum_orbit {Γ G : Type} [Group Γ] [Group G] (ι : Γ →* G) (H : Subgroup Γ)
    (K : Subgroup G) (g : LeftCosets ι K → ℂ) (hg : ∀ h ∈ H, ∀ y : LeftCosets ι K, g (h • y) = g y) :
    ∑ᶠ q : DoubleCoset.Quotient ((H.map ι : Subgroup G) : Set G) (K : Set G), g (LeftCosets.mk ι K (Quotient.out q)) =
      ∑ᶠ o : MulAction.orbitRel.Quotient H (LeftCosets ι K), g (Quotient.out o) := by
  let e := Equiv.ofBijective _ (doubleCosetToOrbit_bijective ι H K)
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  have hq : e q = Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K q.out) := by
    show doubleCosetToOrbit ι H K q = _
    conv_lhs => rw [← DoubleCoset.out_eq' _ _ q]
    rfl
  rw [hq]
  obtain ⟨h, hh⟩ := Quotient.exact (Quotient.out_eq
    (Quotient.mk (MulAction.orbitRel H (LeftCosets ι K)) (LeftCosets.mk ι K q.out)))
  rw [← hh]
  exact (hg h h.2 _).symm

end GlobalTheory.LKCount
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxUnfoldGen

open GlobalTheory.CxUnfold

section Abstract

variable {Γ : Type} [Group Γ]

theorem card_stabilizer_smul_inf {X : Type} [MulAction Γ X] (Z : Subgroup Γ) {ζ : Γ} (hζ : ζ ∈ Z) (a : X) :
    Nat.card (MulAction.stabilizer Γ (ζ • a) ⊓ Z : Subgroup Γ) = Nat.card (MulAction.stabilizer Γ a ⊓ Z : Subgroup Γ) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨ζ⁻¹ * g.1 * ζ, ?_⟩
      invFun := fun g => ⟨ζ * g.1 * ζ⁻¹, ?_⟩
      left_inv := fun g => by ext; simp [mul_assoc]
      right_inv := fun g => by ext; simp [mul_assoc] }
  · obtain ⟨g, hg⟩ := g
    rw [Subgroup.mem_inf] at hg
    have hg1 : g • ζ • a = ζ • a := hg.1
    refine Subgroup.mem_inf.2 ⟨?_, Z.mul_mem (Z.mul_mem (Z.inv_mem hζ) hg.2) hζ⟩
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hg1, inv_smul_smul]
  · obtain ⟨g, hg⟩ := g
    rw [Subgroup.mem_inf] at hg
    have hg1 : g • a = a := hg.1
    refine Subgroup.mem_inf.2 ⟨?_, Z.mul_mem (Z.mul_mem hζ hg.2) (Z.inv_mem hζ)⟩
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul, hg1]

theorem finsum_orbit_prod_line {U P : Type} [MulAction Γ U] [MulAction Γ P] (Z : Subgroup Γ) (l₀ : P)
    (hl₀ : ∀ ζ ∈ Z, ζ • l₀ = l₀) (F : U × P → ℂ) (c : U → ℂ) (hF0 : ∀ u l, l ≠ l₀ → F (u, l) = 0)
    (hF1 : ∀ u, F (u, l₀) = c u) (hc : ∀ ζ ∈ Z, ∀ u, c (ζ • u) = c u) :
    ∑ᶠ o : MulAction.orbitRel.Quotient Z (U × P),
        ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Z : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) =
      ∑ᶠ o : MulAction.orbitRel.Quotient Z U,
        ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Z : Subgroup Γ) : ℕ) : ℂ)⁻¹ * c (Quotient.out o) := by
  set S : U × P → ℂ := fun a => ((Nat.card (MulAction.stabilizer Γ a ⊓ Z : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F a with hS

  have hstab : ∀ u, (MulAction.stabilizer Γ ((u, l₀) : U × P) ⊓ Z : Subgroup Γ) = MulAction.stabilizer Γ u ⊓ Z := by
    intro u; ext g
    simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Prod.smul_mk, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, hl₀ g h2⟩, h2⟩

  have hSinv : ∀ ζ ∈ Z, ∀ a, S (ζ • a) = S a := by
    intro ζ hζ a
    simp only [hS]
    rw [card_stabilizer_smul_inf Z hζ a]
    congr 1
    obtain ⟨u, l⟩ := a
    rw [Prod.smul_mk]
    by_cases hl : l = l₀
    · subst hl; rw [hl₀ ζ hζ, hF1, hF1, hc ζ hζ]
    · have hl' : ζ • l ≠ l₀ := by
        intro h; apply hl
        have := congrArg (fun m => ζ⁻¹ • m) h
        simpa [hl₀ ζ⁻¹ (Z.inv_mem hζ)] using this
      rw [hF0 _ _ hl, hF0 _ _ hl']

  let φ : MulAction.orbitRel.Quotient Z U → MulAction.orbitRel.Quotient Z (U × P) :=
    Quotient.map' (fun u => (u, l₀)) (by
      rintro u u' ⟨ζ, rfl⟩
      refine ⟨ζ, ?_⟩
      show ((ζ : Γ) • u', (ζ : Γ) • l₀) = ((ζ : Γ) • u', l₀)
      rw [hl₀ _ ζ.2])
  have hφ : Function.Injective φ := by
    intro q q' h
    induction q using Quotient.inductionOn' with | h u => ?_
    induction q' using Quotient.inductionOn' with | h u' => ?_
    have h' := Quotient.exact' h
    obtain ⟨ζ, hζ⟩ := h'
    apply Quotient.sound'
    refine ⟨ζ, ?_⟩
    exact congrArg Prod.fst hζ

  have hsupp : Function.support (fun o : MulAction.orbitRel.Quotient Z (U × P) => S (Quotient.out o)) ⊆ Set.range φ := by
    intro o ho
    have hne : F (Quotient.out o) ≠ 0 := by
      intro h0; apply ho; simp [hS, h0]
    have hl : (Quotient.out o).2 = l₀ := by
      by_contra hl
      exact hne (by rw [← Prod.mk.eta (p := Quotient.out o)]; exact hF0 _ _ hl)
    refine ⟨Quotient.mk'' (Quotient.out o).1, ?_⟩
    show Quotient.mk'' ((Quotient.out o).1, l₀) = o
    rw [← hl, Prod.mk.eta]
    exact Quotient.out_eq' o
  have hval : ∀ q : MulAction.orbitRel.Quotient Z U, S (Quotient.out (φ q)) =
      ((Nat.card (MulAction.stabilizer Γ (Quotient.out q) ⊓ Z : Subgroup Γ) : ℕ) : ℂ)⁻¹ * c (Quotient.out q) := by
    intro q
    have h1 : (Quotient.mk'' (Quotient.out (φ q)) : MulAction.orbitRel.Quotient Z (U × P)) =
        Quotient.mk'' (Quotient.out q, l₀) := by
      rw [Quotient.out_eq']
      conv_lhs => rw [← Quotient.out_eq' q]
      rfl
    obtain ⟨ζ, hζ⟩ := Quotient.exact' h1
    rw [← hζ]
    change S ((ζ : Γ) • _) = _
    rw [hSinv _ ζ.2]
    simp only [hS]
    rw [hstab, hF1]
  calc ∑ᶠ o : MulAction.orbitRel.Quotient Z (U × P), S (Quotient.out o)
      = ∑ᶠ o ∈ Set.range φ, S (Quotient.out o) := by
        rw [← finsum_mem_inter_support, Set.inter_eq_right.2 hsupp, finsum_mem_support]
    _ = ∑ᶠ q, S (Quotient.out (φ q)) := finsum_mem_range hφ
    _ = _ := finsum_congr hval

end Abstract

end GlobalTheory.CxUnfoldGen

noncomputable section

namespace GlobalTheory.CxUnfoldGen

open GlobalTheory.CxUnfold

section Point

variable {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂]

def cosetVal (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) (u : LeftCosets (ι₁.prod ι₂) (K₁.prod K₂)) : ℂ :=
  f₁ ((LeftCosets.rep _ _ u).1⁻¹ * γ * (LeftCosets.rep _ _ u).1) *
    φ ((LeftCosets.rep _ _ u).2⁻¹ * δ * (LeftCosets.rep _ _ u).2)

variable (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) {K₁ : Subgroup G₁} {K₂ : Subgroup G₂} (γ : G₁) (δ : G₂)
  {f₁ : G₁ → ℂ} {φ : G₂ → ℂ}

theorem cosetVal_mk (hf₁ : ∀ k ∈ K₁, ∀ g, f₁ (k⁻¹ * g * k) = f₁ g) (hφ : ∀ k ∈ K₂, ∀ g, φ (k⁻¹ * g * k) = φ g)
    (x : G₁ × G₂) :
    cosetVal ι₁ ι₂ K₁ K₂ γ δ f₁ φ (LeftCosets.mk _ _ x) = f₁ (x.1⁻¹ * γ * x.1) * φ (x.2⁻¹ * δ * x.2) := by
  obtain ⟨k, hk, e⟩ := LeftCosets.rep_mk (ι := ι₁.prod ι₂) (K := K₁.prod K₂) x
  rw [Subgroup.mem_prod] at hk
  rw [cosetVal, e]
  have e1 : (x * k).1⁻¹ * γ * (x * k).1 = k.1⁻¹ * (x.1⁻¹ * γ * x.1) * k.1 := by
    simp only [Prod.fst_mul]; group
  have e2 : (x * k).2⁻¹ * δ * (x * k).2 = k.2⁻¹ * (x.2⁻¹ * δ * x.2) * k.2 := by
    simp only [Prod.snd_mul]; group
  rw [e1, e2, hf₁ _ hk.1, hφ _ hk.2]

theorem cosetVal_smul (hf₁ : ∀ k ∈ K₁, ∀ g, f₁ (k⁻¹ * g * k) = f₁ g) (hφ : ∀ k ∈ K₂, ∀ g, φ (k⁻¹ * g * k) = φ g)
    (η : Γ) (h₁ : ι₁ η * γ = γ * ι₁ η) (h₂ : ι₂ η * δ = δ * ι₂ η) (u : LeftCosets (ι₁.prod ι₂) (K₁.prod K₂)) :
    cosetVal ι₁ ι₂ K₁ K₂ γ δ f₁ φ (η • u) = cosetVal ι₁ ι₂ K₁ K₂ γ δ f₁ φ u := by
  conv_lhs => rw [← LeftCosets.mk_rep u, LeftCosets.smul_mk]
  conv_rhs => rw [← LeftCosets.mk_rep u]
  rw [cosetVal_mk ι₁ ι₂ γ δ hf₁ hφ, cosetVal_mk ι₁ ι₂ γ δ hf₁ hφ]
  simp only [Prod.fst_mul, Prod.snd_mul, MonoidHom.prod_apply]
  have e1 : (ι₁ η * (LeftCosets.rep _ _ u).1)⁻¹ * γ * (ι₁ η * (LeftCosets.rep _ _ u).1) =
      (LeftCosets.rep _ _ u).1⁻¹ * γ * (LeftCosets.rep _ _ u).1 := by
    have h : (ι₁ η)⁻¹ * γ * ι₁ η = γ := by rw [mul_assoc, ← h₁, ← mul_assoc, inv_mul_cancel, one_mul]
    calc _ = (LeftCosets.rep _ _ u).1⁻¹ * ((ι₁ η)⁻¹ * γ * ι₁ η) * (LeftCosets.rep _ _ u).1 := by group
      _ = _ := by rw [h]
  have e2 : (ι₂ η * (LeftCosets.rep _ _ u).2)⁻¹ * δ * (ι₂ η * (LeftCosets.rep _ _ u).2) =
      (LeftCosets.rep _ _ u).2⁻¹ * δ * (LeftCosets.rep _ _ u).2 := by
    have h : (ι₂ η)⁻¹ * δ * ι₂ η = δ := by rw [mul_assoc, ← h₂, ← mul_assoc, inv_mul_cancel, one_mul]
    calc _ = (LeftCosets.rep _ _ u).2⁻¹ * ((ι₂ η)⁻¹ * δ * ι₂ η) * (LeftCosets.rep _ _ u).2 := by group
      _ = _ := by rw [h]
  rw [e1, e2]

theorem pointSum_centralizer_eq (hf₁ : ∀ k ∈ K₁, ∀ g, f₁ (k⁻¹ * g * k) = f₁ g)
    (hφ : ∀ k ∈ K₂, ∀ g, φ (k⁻¹ * g * k) = φ g) (y₀ : Γ) :
    pointSum (ι₁.comp (Subgroup.centralizer {y₀}).subtype) (ι₂.comp (Subgroup.centralizer {y₀}).subtype)
        (MonoidHom.id G₂) K₁ K₂ (ι₁ y₀) (ι₂ y₀) f₁ φ =
      ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {y₀}) (LeftCosets (ι₁.prod ι₂) (K₁.prod K₂)),
        ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {y₀} : Subgroup Γ) : ℕ) : ℂ)⁻¹ *
          cosetVal ι₁ ι₂ K₁ K₂ (ι₁ y₀) (ι₂ y₀) f₁ φ (Quotient.out o) := by
  set Z := Subgroup.centralizer {y₀} with hZ
  have hcomm : ∀ η ∈ Z, η * y₀ = y₀ * η := by
    intro η hη
    exact ((Subgroup.mem_centralizer_iff.1 hη) y₀ (Set.mem_singleton _)).symm
  set g : LeftCosets (ι₁.prod ι₂) (K₁.prod K₂) → ℂ := fun u =>
    ((Nat.card (MulAction.stabilizer Γ u ⊓ Z : Subgroup Γ) : ℕ) : ℂ)⁻¹ * cosetVal ι₁ ι₂ K₁ K₂ (ι₁ y₀) (ι₂ y₀) f₁ φ u
    with hg
  have hginv : ∀ η ∈ Z, ∀ u, g (η • u) = g u := by
    intro η hη u
    simp only [hg]
    rw [card_stabilizer_smul_inf Z hη u,
      cosetVal_smul ι₁ ι₂ _ _ hf₁ hφ η (by rw [← map_mul, ← map_mul, hcomm η hη]) (by rw [← map_mul, ← map_mul, hcomm η hη])]
  have hr : (((ι₁.comp Z.subtype).prod (ι₂.comp Z.subtype)).range : Set (G₁ × G₂)) =
      ((Z.map (ι₁.prod ι₂) : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) := by
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.prod_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype, Subtype.exists, exists_prop]
  have hcard : ∀ x : G₁ × G₂, Nat.card (stab (ι₁.comp Z.subtype) (ι₂.comp Z.subtype) K₁ K₂ x) =
      Nat.card (MulAction.stabilizer Γ (LeftCosets.mk (ι₁.prod ι₂) (K₁.prod K₂) x) ⊓ Z : Subgroup Γ) := by
    intro x
    rw [← stab_eq_stabilizer ι₁ ι₂]
    exact Nat.card_congr
      { toFun := fun η => ⟨η.1.1, Subgroup.mem_inf.2 ⟨η.2, η.1.2⟩⟩
        invFun := fun η => ⟨⟨η.1, (Subgroup.mem_inf.1 η.2).2⟩, (Subgroup.mem_inf.1 η.2).1⟩
        left_inv := fun η => rfl
        right_inv := fun η => rfl }
  unfold pointSum
  rw [hr, ← GlobalTheory.LKCount.finsum_doubleCoset_eq_finsum_orbit (ι₁.prod ι₂) Z (K₁.prod K₂) g hginv]
  refine finsum_congr fun q => ?_
  simp only [hg]
  rw [cosetVal_mk ι₁ ι₂ _ _ hf₁ hφ, hcard]
  rfl

end Point

end GlobalTheory.CxUnfoldGen

noncomputable section

namespace GlobalTheory.CxUnfoldGen

open GlobalTheory.CxUnfold

theorem finsum_mul_const_complex {α : Type} (g : α → ℂ) (w : ℂ) : ∑ᶠ i, g i * w = (∑ᶠ i, g i) * w := by
  exact (finsum_mul _ _).symm

theorem cls_eq_of_uniq : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y₀ : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y₀ * h) ≠ 0 → ∀ z z' : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re → FixL G v β y₀ z → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z) → ∀ y₀ : grp G β, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {y₀}) (GlobalTheory.CxUnfold.Ys G v β x t hx Kf K'), ((Nat.card (MulAction.stabilizer (grp G β) (Quotient.out o) ⊓ Subgroup.centralizer {y₀} : Subgroup (grp G β)) : ℕ) : ℂ)⁻¹ * GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (Quotient.out o) y₀ = if (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y₀ z) then wt (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * pointSum ((toAfF G β x t hx).comp (Subgroup.centralizer {y₀}).subtype) ((toP1 G β).comp (Subgroup.centralizer {y₀}).subtype) (MonoidHom.id (Gr G 1)) Kf K' (toAfF G β x t hx y₀) (toP1 G β y₀) f f' else 0 := by
  intro p _ G v wt Kf f hf₁ K' f' hφ β x t hx huniq' y₀
  set Z := Subgroup.centralizer {y₀} with hZ
  have hcomm : ∀ η ∈ Z, η * y₀ = y₀ * η := by
    intro η hη
    exact ((Subgroup.mem_centralizer_iff.1 hη) y₀ (Set.mem_singleton _)).symm
  by_cases hpos : ∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y₀ z
  swap
  · rw [if_neg hpos]
    refine finsum_eq_zero_of_forall_eq_zero fun o => ?_
    rw [cxF, if_neg (fun h => hpos ⟨_, h⟩), mul_zero]
  rw [if_pos hpos]
  obtain ⟨z₀, hz₀pos, hz₀fix⟩ := hpos
  by_cases hf0 : ∃ h, f (h⁻¹ * toAfF G β x t hx y₀ * h) ≠ 0
  swap
  · push_neg at hf0
    have hl : ∀ o : MulAction.orbitRel.Quotient Z (Ys G v β x t hx Kf K'),
        cxF G v wt β x t hx Kf f K' f' (Quotient.out o) y₀ = 0 := by
      intro o
      rw [cxF]
      split_ifs
      · rw [hf0, zero_mul, zero_mul]
      · rfl
    simp only [hl, mul_zero, finsum_zero, pointSum, hf0, zero_mul]
  obtain ⟨h₀, hh₀⟩ := hf0
  have huniq : ∀ z', 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z₀ :=
    fun z' hp hfx => huniq' y₀ h₀ hh₀ z₀ z' hz₀pos hp hz₀fix hfx
  have hz₀ne : z₀ ≠ 0 := by
    rintro rfl; simp at hz₀pos
  let l₀ : PLv G v β := Projectivization.mk ℂ z₀ hz₀ne

  have hl₀ : ∀ ζ ∈ Z, ζ • l₀ = l₀ := by
    intro ζ hζ
    change Projectivization.map _ _ (Projectivization.mk ℂ z₀ hz₀ne) = Projectivization.mk ℂ z₀ hz₀ne
    rw [Projectivization.map_mk]
    have hp := (GlobalTheory.LKCx.pos_iff_smul_toV p G v β ζ z₀ 1 one_ne_zero).1 hz₀pos
    rw [one_smul] at hp
    have hfx := (GlobalTheory.LKCx.fixL_conj_iff p G v β y₀ ζ z₀).1 hz₀fix
    rw [hcomm ζ hζ, mul_inv_cancel_right] at hfx
    obtain ⟨c, hc⟩ := huniq _ hp hfx
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨c, by rw [Matrix.toLin'_apply]; exact hc.symm⟩

  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ (Projectivization.rep_nonzero (l₀ : Projectivization ℂ (Fin G.n → ℂ))) hz₀ne).1
    (Projectivization.mk_rep (l₀ : Projectivization ℂ (Fin G.n → ℂ)))
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact Projectivization.rep_nonzero (l₀ : Projectivization ℂ (Fin G.n → ℂ)) (by rw [← ha, zero_smul])
  set F : Ys G v β x t hx Kf K' → ℂ := fun b => cxF G v wt β x t hx Kf f K' f' b y₀ with hF
  set c : LeftCosets ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') → ℂ := fun u =>
    cosetVal (toAfF G β x t hx) (toP1 G β) Kf K' (toAfF G β x t hx y₀) (toP1 G β y₀) f f' u *
      wt (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) with hc
  have hF0 : ∀ u l, l ≠ l₀ → F (u, l) = 0 := by
    intro u l hl
    simp only [hF]
    rw [cxF, if_neg]
    rintro ⟨hp, hfx⟩
    obtain ⟨d, hd⟩ := huniq _ hp hfx
    apply hl
    exact (Projectivization.mk_rep (l : Projectivization ℂ (Fin G.n → ℂ))).symm.trans
      ((Projectivization.mk_eq_mk_iff' ℂ _ _ (Projectivization.rep_nonzero _) hz₀ne).2 ⟨d, hd.symm⟩)
  have hF1 : ∀ u, F (u, l₀) = c u := by
    intro u
    simp only [hF, hc]
    rw [cxF, if_pos]
    · rfl
    refine ⟨?_, ?_⟩
    · have hp := (GlobalTheory.LKCx.pos_iff_smul_toV p G v β 1 z₀ a ha0).1 hz₀pos
      have e : ((toV G v β 1 : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z₀ = z₀ := by simp
      rw [e, ha] at hp
      exact hp
    · obtain ⟨d, hd⟩ := hz₀fix
      refine ⟨d, ?_⟩
      rw [← ha, Matrix.mulVec_smul, hd, smul_comm]
  have hcinv : ∀ ζ ∈ Z, ∀ u, c (ζ • u) = c u := by
    intro ζ hζ u
    simp only [hc]
    rw [cosetVal_smul (toAfF G β x t hx) (toP1 G β) _ _ hf₁ hφ ζ
      (by rw [← map_mul, ← map_mul, hcomm ζ hζ]) (by rw [← map_mul, ← map_mul, hcomm ζ hζ])]
  refine (finsum_orbit_prod_line Z l₀ hl₀ F c hF0 hF1 hcinv).trans ?_
  rw [pointSum_centralizer_eq (toAfF G β x t hx) (toP1 G β) hf₁ hφ y₀, mul_comm, ← finsum_mul_const_complex]
  refine finsum_congr fun o => ?_
  simp only [hc]
  ring

end GlobalTheory.CxUnfoldGen
end
end
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugacyClassPart_eq_weight_mul_kottwitzPointSum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y₀ : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y₀ * h) ≠ 0 → ∀ z z' : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re → FixL G v β y₀ z → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z) → ∀ y₀ : grp G β, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {y₀}) (GlobalTheory.CxUnfold.Ys G v β x t hx Kf K'), ((Nat.card (MulAction.stabilizer (grp G β) (Quotient.out o) ⊓ Subgroup.centralizer {y₀} : Subgroup (grp G β)) : ℕ) : ℂ)⁻¹ * GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (Quotient.out o) y₀ = if (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y₀ z) then wt (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * pointSum ((toAfF G β x t hx).comp (Subgroup.centralizer {y₀}).subtype) ((toP1 G β).comp (Subgroup.centralizer {y₀}).subtype) (MonoidHom.id (Gr G 1)) Kf K' (toAfF G β x t hx y₀) (toP1 G β y₀) f f' else 0 := by
  first | (exact @GlobalTheory.CxUnfoldGen.cls_eq_of_uniq) | (exact GlobalTheory.CxUnfoldGen.cls_eq_of_uniq) | (intros; apply GlobalTheory.CxUnfoldGen.cls_eq_of_uniq  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CxUnfold

theorem support_cxF_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (h : G.GAf × Gr G 1) (z : Fin G.n → ℂ), 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → Set.Finite {y : grp G β | FixL G v β y z ∧ f (h.1⁻¹ * toAfF G β x t hx y * h.1) * f' (h.2⁻¹ * toP1 G β y * h.2) ≠ 0}) → ∀ a : GlobalTheory.CxUnfold.Ys G v β x t hx Kf K', (Function.support (GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' a)).Finite := by
  intro p _ G v wt Kf f _ K' f' _ β x t hx hfin a
  by_cases hpos : 0 < (star (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
      (herm G v β *ᵥ Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))).re
  · refine (hfin (LeftCosets.rep _ _ a.1) _ hpos).subset ?_
    intro y hy
    rw [Function.mem_support] at hy
    unfold cxF at hy
    split_ifs at hy with hc
    · exact ⟨hc.2, left_ne_zero_of_mul hy⟩
    · exact absurd rfl hy
  · convert Set.finite_empty
    ext y
    simp only [Function.mem_support, Set.mem_empty_iff_false, iff_false, not_not]
    unfold cxF
    rw [if_neg (fun hc => hpos hc.1)]

end GlobalTheory.CxUnfold
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairWeight_support_finite_of_finite_fixing : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (h : G.GAf × Gr G 1) (z : Fin G.n → ℂ), 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → Set.Finite {y : grp G β | FixL G v β y z ∧ f (h.1⁻¹ * toAfF G β x t hx y * h.1) * f' (h.2⁻¹ * toP1 G β y * h.2) ≠ 0}) → ∀ a : GlobalTheory.CxUnfold.Ys G v β x t hx Kf K', (Function.support (GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' a)).Finite := by
  first | (exact @GlobalTheory.CxUnfold.support_cxF_finite) | (exact GlobalTheory.CxUnfold.support_cxF_finite) | (intros; apply GlobalTheory.CxUnfold.support_cxF_finite <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separable_formGroup_element_fixes_unique_positive_line : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (β : G.Cˣ), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ y₀ : grp G β, (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n → (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable → ∀ z z' : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re → FixL G v β y₀ z → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z := by
  first | (exact @GlobalTheory.LKCx.fixL_pos_unique_of_sep) | (exact GlobalTheory.LKCx.fixL_pos_unique_of_sep) | (intros; apply GlobalTheory.LKCx.fixL_pos_unique_of_sep  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxRegLoc

theorem local_class_scalar_norm_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β →
    ∀ y₀ : grp G β, (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable →
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n →
    ∃ S : Finset ℕ, ∀ (y : grp G β) (g : G.GAf), f (g⁻¹ * toAfF G β x t hx y * g) ≠ 0 →
    ∀ c : G.Cˣ, (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) ∧
      inC G ℚ_[ℓ] (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (β : G.C) *
        (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G L f hf β x t hx hβ y₀ hsep hdeg
  have hcomm : ∀ a b : G.C, Commute a (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) →
      Commute b (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) → Commute a b :=
    fun a b ha hb => GlobalTheory.LKCx.ClsReg.commute_of_commute_of_separable G _ hsep hdeg a b ha hb
  obtain ⟨Ω, hΩc, hΩ⟩ := GlobalTheory.T.exists_compact_support_twistedHeckeTestFunction p G L f hf
  have hev := eventually_compL_mem_intPts p G Ω hΩc
  have hlat := GlobalTheory.T.eventually_kottwitz_lattice_separable_minpoly p G (y₀ : G.Cˣ × ℚˣ).1 hsep hdeg
  have hnorm := GlobalTheory.T.eventually_tauFixed_unit_centralizer_is_norm p G β hβ (y₀ : G.Cˣ × ℚˣ).1 _ y₀.2.1 hsep hdeg
  have hstab := GlobalTheory.FinClsLoc.intC_stab p G β
  obtain ⟨S, hS⟩ := GlobalTheory.FinClsLoc.exists_finset_forall_prime_awayP_padic p _ (hev.and (hlat.and (hnorm.and hstab)))
  refine ⟨S, fun y g hfy c hc ℓ _ hℓ => ?_⟩
  obtain ⟨w, ⟨hev', hlat', hnorm', hmul, hstar, hβi, hβi'⟩, ⟨e⟩⟩ := hS ℓ hℓ
  apply GlobalTheory.T.localTwistedNormConclusion_transfer_ringEquiv p G (w.1.adicCompletion ℚ) ℚ_[ℓ] e
  have hint := hev' _ (hΩ _ hfy)
  obtain ⟨k, lam, hk1, hk2, hk3⟩ := GlobalTheory.T.exists_local_conj_trivialization_at_place_awayP p G β x t hx y g c (y₀ : G.Cˣ × ℚˣ).1 hc w
  obtain ⟨z, m, hz, hm, hm', hkzm⟩ := hlat' k (by rw [hk1]; exact hint.1) (by rw [hk2]; exact hint.2.1)
  have hap := GlobalTheory.grp_conj_unit_props p G β hβ y y₀ c hc (GlobalTheory.grp_factor_eq_of_conj p G β y y₀ c hc)
  have hinv := starT_invol G (w.1.adicCompletion ℚ)
  have hbb : inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) * inC G (w.1.adicCompletion ℚ) (β : G.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hβ' : (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) (β : G.C))).unop = inC G (w.1.adicCompletion ℚ) (β : G.C) := by
    show (starT G.star (w.1.adicCompletion ℚ) ((1 : w.1.adicCompletion ℚ) ⊗ₜ (β : G.C))).unop = (1 : w.1.adicCompletion ℚ) ⊗ₜ (β : G.C)
    rw [starT_tmul]
    exact congrArg (TensorProduct.tmul ℚ (1 : w.1.adicCompletion ℚ)) hβ
  have hY' : inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * inC G (w.1.adicCompletion ℚ) (β : G.C) *
      (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))).unop =
      algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (algebraMap ℚ (w.1.adicCompletion ℚ) ((y₀ : G.Cˣ × ℚˣ).2 : ℚ)) * inC G (w.1.adicCompletion ℚ) (β : G.C) := by
    have h := congrArg (inC G (w.1.adicCompletion ℚ)) y₀.2.1
    rw [map_mul, map_mul, map_mul] at h
    have e1 : inC G (w.1.adicCompletion ℚ) (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) =
        (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))).unop :=
      (starT_tmul G.star (w.1.adicCompletion ℚ) 1 _).symm
    have e2 : inC G (w.1.adicCompletion ℚ) (algebraMap ℚ G.C ((y₀ : G.Cˣ × ℚˣ).2 : ℚ)) =
        algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (algebraMap ℚ (w.1.adicCompletion ℚ) ((y₀ : G.Cˣ × ℚˣ).2 : ℚ)) := by
      rw [← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] w.1.adicCompletion ℚ ⊗[ℚ] G.C).commutes _
    rw [e1, e2] at h
    exact h
  have hN : ∀ m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = m * (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) →
      Commute (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) →
      inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) = m' →
      ∃ v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) ∧
        (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = v * (inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
    intro m' hm'v hcm hτ
    have hss : (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * (starT G.star (w.1.adicCompletion ℚ) ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop = 1 := by
      rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
    have h1 : (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * (inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop *
        ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) = 1 := by
      rw [hm'v]
      calc _ = (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * ((starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop *
            (inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) * inC G (w.1.adicCompletion ℚ) (β : G.C)) *
            (starT G.star (w.1.adicCompletion ℚ) ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop) * ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) := by
            simp only [mul_assoc]
        _ = 1 := by rw [hbb, mul_one, hss, mul_one, Units.mul_inv]
    have hinv' := Units.inv_eq_of_mul_eq_one_right h1
    refine hnorm' m' hcm ?_ ?_ hτ
    · rw [hm'v]; exact hmul _ _ (hmul _ _ hm (hstar _ hm)) hβi'
    · rw [hinv']; exact hmul _ _ (hmul _ _ hβi (hstar _ hm')) hm'
  have halg := GlobalTheory.twisted_norm_local_step (starT G.star (w.1.adicCompletion ℚ)) hinv
    (Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom β)
    (Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom (y₀ : G.Cˣ × ℚˣ).1) k z m
    (inC G (w.1.adicCompletion ℚ) (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)))
    lam (Units.map (algebraMap ℚ (w.1.adicCompletion ℚ)).toMonoidHom (y₀ : G.Cˣ × ℚˣ).2) hβ' hY'
    (hap.2.1.map (inC G (w.1.adicCompletion ℚ))) hk3 hkzm hz hN
  obtain ⟨z', hz', hz'eq⟩ := halg
  exact ⟨lam, z', hz', hz'eq⟩

end GlobalTheory.CxRegLoc
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.harrisTaylor_regular_conjugate_local_scalar_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β →
    ∀ y₀ : grp G β, (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable →
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n →
    ∃ S : Finset ℕ, ∀ (y : grp G β) (g : G.GAf), f (g⁻¹ * toAfF G β x t hx y * g) ≠ 0 →
    ∀ c : G.Cˣ, (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) ∧
      inC G ℚ_[ℓ] (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (β : G.C) *
        (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C)) := by
  first | exact @GlobalTheory.CxRegLoc.local_class_scalar_norm_sep | exact GlobalTheory.CxRegLoc.local_class_scalar_norm_sep
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.ClsReg

theorem classes_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ P : Polynomial G.F, ∃ Y : Finset (grp G β), ∀ y : grp G β, minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P → (∃ a : Dat G v β, FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0) → ∃ y₀ ∈ Y, ∃ γ : grp G β, y = γ * y₀ * γ⁻¹ := by
  intro p _ G _ v _ L f hf K' f' _ β x t hx hreg hβ _ P
  by_cases hne : ∃ y₀ : grp G β, minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P ∧
      ∃ a : Dat G v β, FixL G v β y₀ a.2.1 ∧
        f (a.1.1⁻¹ * toAfF G β x t hx y₀ * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y₀ * a.1.2) ≠ 0
  swap
  · exact ⟨∅, fun y hy ha => absurd ⟨y, hy, ha⟩ hne⟩
  obtain ⟨y₀, hP₀, a₀, hfix₀, ha₀⟩ := hne
  obtain ⟨hdeg₀, hsep₀⟩ := hreg y₀ a₀.1.1 (left_ne_zero_of_mul ha₀) ⟨a₀.2.1, a₀.2.2, hfix₀⟩
  obtain ⟨hy₀, -⟩ := y₀.prop
  obtain ⟨S, hS⟩ := GlobalTheory.T.harrisTaylor_regular_conjugate_local_scalar_norm p G L f hf β x t hx hβ y₀ hsep₀ hdeg₀
  obtain ⟨A, hA⟩ := GlobalTheory.T.finite_fixed_unit_classes_centralizer_regular p G β hβ ((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) (((y₀ : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) hy₀ hsep₀ hdeg₀ S
  have key : ∀ y : grp G β, minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P → ∀ g : G.GAf,
      f (g⁻¹ * toAfF G β x t hx y * g) ≠ 0 → ∃ a' ∈ A, ∃ b : Bool, ∃ (c : G.Cˣ) (r : ℚˣ) (e : G.Cˣ),
        (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) ∧
        Commute (e : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ decide (0 < (r : ℚ)) = b ∧
        (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * a' * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) := by
    intro y hy g hg
    obtain ⟨c, hc⟩ := units_conj_of_minpoly_eq_of_separable G ((y : G.Cˣ × ℚˣ).1) ((y₀ : G.Cˣ × ℚˣ).1)
      (by rw [hy, hP₀]) hsep₀ hdeg₀
    have h2 := GlobalTheory.grp_factor_eq_of_conj p G β y y₀ c hc
    obtain ⟨hu, hcm, hfix⟩ := GlobalTheory.grp_conj_unit_props p G β hβ y y₀ c hc h2
    obtain ⟨a', ha', r, e, he, hre⟩ := hA _ hu hcm hfix (fun ℓ _ hℓ => hS y g hg c hc ℓ hℓ)
    exact ⟨a', ha', decide (0 < (r : ℚ)), c, r, e, hc, he, rfl, hre⟩
  let D : G.C × Bool → grp G β → Prop := fun ab y => ∃ (c : G.Cˣ) (r : ℚˣ) (e : G.Cˣ),
        (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) ∧
        Commute (e : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ decide (0 < (r : ℚ)) = ab.2 ∧
        (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * ab.1 * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C)))
  let ρ : G.C × Bool → grp G β := fun ab => if h : ∃ y, D ab y then h.choose else 1
  refine ⟨(A ×ˢ (Finset.univ : Finset Bool)).image ρ, ?_⟩
  rintro y hy ⟨a, _, ha⟩
  obtain ⟨a', ha', b, hD⟩ := key y hy a.1.1 (left_ne_zero_of_mul ha)
  have hex : ∃ y, D (a', b) y := ⟨y, hD⟩
  refine ⟨ρ (a', b), Finset.mem_image_of_mem _ (Finset.mem_product.2 ⟨ha', Finset.mem_univ _⟩), ?_⟩
  have hρ : ρ (a', b) = hex.choose := dif_pos hex
  rw [hρ]
  obtain ⟨c', r', e', hc', he', hb', hre'⟩ := hex.choose_spec
  dsimp only at hb' hre'
  obtain ⟨c, r, e, hc, he, hb, hre⟩ := hD
  have h2 : (hex.choose : G.Cˣ × ℚˣ).2 = (y : G.Cˣ × ℚˣ).2 := by
    rw [GlobalTheory.grp_factor_eq_of_conj p G β _ y₀ c' hc', GlobalTheory.grp_factor_eq_of_conj p G β y y₀ c hc]
  refine GlobalTheory.Div.conj_of_twist p G β hex.choose y ((y₀ : G.Cˣ × ℚˣ).1) c' c (e * e'⁻¹) ((r : ℚ) / r') hc' hc h2 ?_ ?_ ?_
  · rw [Units.val_mul]
    exact he.mul_left he'.units_inv_left
  · have hr : (0 < (r : ℚ)) ↔ (0 < (r' : ℚ)) := by
      rw [← decide_eq_decide, hb, hb']
    rcases lt_or_gt_of_ne r'.ne_zero with h | h
    · have hn : ¬ (0 < (r : ℚ)) := fun h0 => absurd (hr.1 h0) (not_lt.2 h.le)
      exact div_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 hn) r.ne_zero) h
    · exact div_pos (hr.2 h) h
  · rw [hre', hre]
    exact conj_rel_alg' G β e e' a' r r'

end GlobalTheory.LKCx.ClsReg
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.orbital_integral_test_function_first : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ P : Polynomial G.F, ∃ Y : Finset (grp G β), ∀ y : grp G β, minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P → (∃ a : Dat G v β, FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0) → ∃ y₀ ∈ Y, ∃ γ : grp G β, y = γ * y₀ * γ⁻¹ := by
  first | exact @GlobalTheory.LKCx.ClsReg.classes_finite | exact GlobalTheory.LKCx.ClsReg.classes_finite
end

section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.CxReg

open GlobalTheory.LKCx.Regroup

variable {p : ℕ} [Fact p.Prime]

theorem sep_of_regAf (G : HTGroup p) (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) (f : G.GAf → ℂ)
    (hreg : ∀ g, f g ≠ 0 → RegAf G g) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (hsym : sh G β = β) (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) :
    (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) := by
  rintro y h hne ⟨z, hz, hfix⟩
  exact GlobalTheory.LKCx.minpoly_of_regAf_of_fixL p G v hv β hsym hR x t hx y h ⟨z, hz⟩ hfix (hreg _ hne)

theorem finite_pts_reg (G : HTGroup p) (ha : G.a = 1) (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1)
    (L : G.Level) (f : G.GAf → ℂ) (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f)
    (hreg : ∀ g, f g ≠ 0 → RegAf G g) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ)
    (hf' : IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f') (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (hsym : sh G β = β) (htr : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) :
    Set.Finite {q : Pts G v β x t hx L.K.toSubgroup K' | ∃ y : grp G β, FixL G v β y (Quot.out q).2.1 ∧
      f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx y * (Quot.out q).1.1) *
        f' ((Quot.out q).1.2⁻¹ * toP1 G β y * (Quot.out q).1.2) ≠ 0} := by
  have hsep := sep_of_regAf G v hv f hreg β x t hx hsym htr
  obtain ⟨Y, hY⟩ := Classical.axiomOfChoice
    (fun P => GlobalTheory.T.orbital_integral_test_function_first p G ha v hv L f hf K' f' hf' β x t hx hsep hsym htr P)
  refine ((GlobalTheory.T.orbital_term_real_trivialisation p G ha v hv L f hf K' f' hf' β x t hx hsym htr).biUnion
    (fun P _ => (Y P).finite_toSet.biUnion
      (fun y₀ _ => GlobalTheory.T.orbital_integral_test_function_second p G ha v hv L f hf K' f' hf' β x t hx hsep hsym htr y₀))).subset ?_
  rintro q ⟨y, hy, hne⟩
  obtain ⟨y₀, hy₀, γ, rfl⟩ := hY _ y rfl ⟨Quot.out q, hy, hne⟩
  simp only [Set.mem_iUnion]
  exact ⟨_, ⟨γ * y₀ * γ⁻¹, Quot.out q, rfl, hy, hne⟩, y₀, hy₀, γ, hy, hne⟩

theorem class_summand_eq_term_of_a_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * sigG G 1 k) = f' g) → ∀ (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (r : grp G P.β), (r : G.Cˣ × ℚˣ) = (P.γ, P.c) → (if (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v P.β *ᵥ z)).re ∧ FixL G v P.β r z) then wt (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * pointSum ((toAfF G P.β x t hx).comp (Subgroup.centralizer {r}).subtype) ((toP1 G P.β).comp (Subgroup.centralizer {r}).subtype) (MonoidHom.id (Gr G 1)) Kf K' (toAfF G P.β x t hx r) (toP1 G P.β r) f f' else 0) = (if ∃ μ, P.Mark μ then wt P.pol * P.term Kf f 1 K' f' else 0) := by
  intro p _ G hG v hv wt Kf f K' f' hf hf' P x t hx r hr
  have hiff := fix_iff_mark G hG v hv P r hr
  by_cases hm : ∃ μ, P.Mark μ
  · rw [if_pos (hiff.2 hm), if_pos hm]
    obtain ⟨μ, hμ⟩ := hm
    have hpos := cent_sim_pos p G P μ hG hμ
    set e := centEquiv G P hpos r hr with he
    have h1 : (toAfF G P.β x t hx).comp (Subgroup.centralizer {r}).subtype =
        (P.toAf x t hx).comp e.toMonoidHom := by
      ext1 y; rfl
    have h2 : (toP1 G P.β).comp (Subgroup.centralizer {r}).subtype = (P.toQr 1 1).comp e.toMonoidHom := by
      ext1 y
      show inclG G 1 (locC G y.1.1) = (MulAut.conj (1 : Gr G 1)⁻¹) (inclG G 1 (locC G y.1.1))
      simp
    have h3 : toAfF G P.β x t hx r = P.toAf x t hx P.self := by
      obtain ⟨r, hr'⟩ := r
      simp only at hr
      subst hr
      rfl
    have h4 : toP1 G P.β r = inclG G 1 P.atP := by
      show inclG G 1 (locC G (r : G.Cˣ × ℚˣ)) = _
      rw [hr]; rfl
    have h5 : minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P.pol := by
      rw [hr]; rfl
    rw [h1, h2, h3, h4, h5, GlobalTheory.pointSum_comp_mulEquiv, GlobalTheory.T.orbital_term_point_sum p G P Kf f K' f' hf hf' x t hx]
  · rw [if_neg (fun h => hm (hiff.1 h)), if_neg hm]

end GlobalTheory.LKCx.CxReg

namespace GlobalTheory.LKCx

end GlobalTheory.LKCx
end
end
