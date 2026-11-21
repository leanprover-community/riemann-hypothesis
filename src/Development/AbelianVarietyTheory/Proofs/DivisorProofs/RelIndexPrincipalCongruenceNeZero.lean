import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DformRelEquivalence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatZeroFromResolutionAndGaga
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import GroundTheory.Brauer.SkolemNoether
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairHermitianFormInvertibleSimilitudeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairGramInvCongruentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenvectorOfMinpolyRootHermitianPsiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueNormSqOfSimilitudeHermitianSignatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePolynomialsBoundedDenom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairRelated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameElementSignAmbiguity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEigenvaluesClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDenominatorsNonzeroTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicConjugateOfTrivialisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormOutsideFiniteSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteBadPlacesPairs
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedRootRealSignatureOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitConjOfMinpolyEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutantOfMaximalDegreeElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompactUnitaryAdelicImageIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjugatorsDifferByCentralizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostAllPlacesTwistedUnitIntegral
import BuildAid.ForwardExisting

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LKCx
variable {p : ℕ} [Fact p.Prime]

def RegEl (G : HTGroup p) (y : G.Cˣ) : Prop :=
  (minpoly G.F (y : G.C)).natDegree = G.n ∧ (minpoly G.F (y : G.C)).Separable

def pairOf {G : HTGroup p} (F : Form G) (r : grp G F.β) (h : RegEl G (r : G.Cˣ × ℚˣ).1) : Pair G :=
  ⟨F.β, (r : G.Cˣ × ℚˣ).1, (r : G.Cˣ × ℚˣ).2, F.sym, r.2.1, h, F.trivAf, F.trivR⟩

end GlobalTheory.LKCx

namespace GlobalTheory.LKCx
variable {p : ℕ} [Fact p.Prime]

theorem pairOf_β {G : HTGroup p} (F : Form G) (r : grp G F.β) (h : RegEl G (r : G.Cˣ × ℚˣ).1) :
    (pairOf F r h).β = F.β := rfl

theorem pairOf_γ {G : HTGroup p} (F : Form G) (r : grp G F.β) (h : RegEl G (r : G.Cˣ × ℚˣ).1) :
    (pairOf F r h).γ = (r : G.Cˣ × ℚˣ).1 := rfl

open GlobalTheory.LKTrip.Example GlobalTheory.LKMid.Example in

example : ∃ (h : RegEl (ex 1 one_ne_zero) exPair.γ),
    pairOf (Form.ofPair exPair) ⟨(exPair.γ, exPair.c), exPair.sim, by show (0:ℚ) < 5; norm_num⟩ h = exPair :=
  ⟨exPair.reg, rfl⟩

end GlobalTheory.LKCx
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKIrr
variable {p : ℕ} [Fact p.Prime]

theorem irreducible_minpoly_inv (G : HTGroup p) (γ : G.Cˣ) (hirr : Irreducible (minpoly G.F (γ : G.C))) :
    Irreducible (minpoly G.F ((γ⁻¹ : G.Cˣ) : G.C)) := by
  have hi : IsIntegral G.F (γ : G.C) := Algebra.IsIntegral.isIntegral _
  set m := minpoly G.F (γ : G.C) with hmdef
  haveI : Fact (Irreducible m) := ⟨hirr⟩
  have hm0 : m ≠ 0 := minpoly.ne_zero hi
  haveI : FiniteDimensional G.F (AdjoinRoot m) := (AdjoinRoot.powerBasis hm0).finite
  have hz : ∀ a : Polynomial G.F, a ∈ Ideal.span {m} → Polynomial.aeval (γ : G.C) a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
    rw [map_mul, minpoly.aeval, zero_mul]
  let f : AdjoinRoot m →ₐ[G.F] G.C := Ideal.Quotient.liftₐ (Ideal.span {m}) (Polynomial.aeval (γ : G.C)) hz
  have ef : f (AdjoinRoot.root m) = γ := by
    show Ideal.Quotient.liftₐ (Ideal.span {m}) (Polynomial.aeval (γ : G.C)) hz
      (Ideal.Quotient.mk _ Polynomial.X) = _
    exact Polynomial.aeval_X _
  have hinj : Function.Injective f := f.toRingHom.injective
  have hr0 : AdjoinRoot.root m ≠ 0 := by
    intro h
    have : (γ : G.C) = 0 := by rw [← ef, h, map_zero]
    exact γ.ne_zero this
  have hinv : f ((AdjoinRoot.root m)⁻¹) = ((γ⁻¹ : G.Cˣ) : G.C) := by
    have h1 : f ((AdjoinRoot.root m)⁻¹) * γ = 1 := by
      rw [← ef, ← map_mul, inv_mul_cancel₀ hr0, map_one]
    calc f ((AdjoinRoot.root m)⁻¹) = f ((AdjoinRoot.root m)⁻¹) * γ * ((γ⁻¹ : G.Cˣ) : G.C) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  rw [← hinv, minpoly.algHom_eq f hinj]
  exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)
end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr
open Polynomial GlobalTheory.GlobEig

theorem exists_emb_isRoot_irr {F C E : Type} [Field F] [NumberField F] [Ring C] [Algebra F C]
    [Algebra ℚ C] [IsScalarTower ℚ F C] [FiniteDimensional F C] [Field E] [Algebra ℚ E] [IsAlgClosed E]
    (y : C) (hirr : Irreducible (minpoly F y)) (μ : E) (h : ((minpoly ℚ y).map (algebraMap ℚ E)).IsRoot μ) :
    ∃ τ : F →+* E, ((minpoly F y).map τ).IsRoot μ := by
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  haveI : Fact (Irreducible (minpoly F y)) := ⟨hirr⟩
  haveI : FiniteDimensional F (AdjoinRoot (minpoly F y)) :=
    (AdjoinRoot.powerBasis (minpoly.ne_zero hyi)).finite
  haveI : FiniteDimensional ℚ (AdjoinRoot (minpoly F y)) := Module.Finite.trans F _
  haveI : Algebra.IsAlgebraic ℚ (AdjoinRoot (minpoly F y)) := Algebra.IsAlgebraic.of_finite ℚ _
  set r := AdjoinRoot.root (minpoly F y)
  have hdvd : minpoly ℚ y ∣ minpoly ℚ r := by
    apply minpoly.dvd
    have h1 : minpoly F y ∣ (minpoly ℚ r).map (algebraMap ℚ F) := by
      rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq, aeval_map_algebraMap, minpoly.aeval]
    obtain ⟨k, hk⟩ := h1
    rw [← aeval_map_algebraMap F, hk, map_mul, minpoly.aeval, zero_mul]
  have hne : minpoly ℚ r ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral r)
  have hμ' : μ ∈ (minpoly ℚ r).rootSet E := by
    rw [mem_rootSet]
    refine ⟨hne, ?_⟩
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, map_mul, aeval_def, eval₂_eq_eval_map, h.eq_zero, zero_mul]
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hμ'
  obtain ⟨ψ, hψ⟩ := hμ'
  refine ⟨(ψ : AdjoinRoot (minpoly F y) →+* E).comp (algebraMap F _), ?_⟩
  rw [← hψ, IsRoot.def, eval_map]
  change eval₂ ((ψ : AdjoinRoot (minpoly F y) →+* E).comp (algebraMap F _))
    ((ψ : AdjoinRoot (minpoly F y) →+* E) r) (minpoly F y) = 0
  rw [← hom_eval₂, ← aeval_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

theorem root_norm_le_irr {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β y : G.Cˣ) (c : ℚˣ)
    (hirr : Irreducible (minpoly G.F (y : G.C)))
    (hyc : (y : G.C) * β * sh G y = algebraMap ℚ G.C c * β) (B : ℝ) (hc : ‖((c : ℚ) : ℚ_[p])‖ ≤ B)
    (hc' : ‖(((c⁻¹ : ℚˣ) : ℚ) : ℚ_[p])‖ ≤ B)
    (hy : ∀ (w : Fin G.m) (μ : PadicAlgCl p),
      ((G.rho w (y : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ B)
    (hyi : ∀ (w : Fin G.m) (μ : PadicAlgCl p),
      ((G.rho w ((y⁻¹ : G.Cˣ) : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ B)
    (μ : PadicAlgCl p) (hμ : ((LinearMap.mulLeft ℚ (y : G.C)).charpoly.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ) :
    ‖μ‖ ≤ B * B := by
  have h0 := isRoot_minpoly_of_isRoot_charpoly (y : G.C) μ hμ
  obtain ⟨τ, hτ⟩ := exists_emb_isRoot_irr (F := G.F) (y : G.C) hirr μ h0
  have hcpos : 0 < ‖((c : ℚ) : ℚ_[p])‖ := norm_pos_iff.2 (by simp)
  have hprod : ‖((c : ℚ) : ℚ_[p])‖ * ‖(((c⁻¹ : ℚˣ) : ℚ) : ℚ_[p])‖ = 1 := by
    rw [← norm_mul, ← Rat.cast_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Rat.cast_one, norm_one]
  have hB0 : 0 ≤ B := hcpos.le.trans hc
  have hB1 : 1 ≤ B := by
    have h1 : 1 ≤ B * B := by
      rw [← hprod]
      exact mul_le_mul hc hc' (norm_nonneg _) hB0
    nlinarith
  rcases liesOver_or_conj G τ with hu | hu
  · obtain ⟨i, ν, hνμ, hν⟩ := exists_root_rho G τ hu y μ hτ
    have h1 := hy i ν hν
    rw [hνμ] at h1
    nlinarith
  · have h2 := isRoot_minpoly_sh G y τ μ hτ
    obtain ⟨i, ν, hνμ, hν⟩ := exists_root_rho G _ hu (sh G y) μ h2
    have h3 := isRoot_inv G i β y c hyc ν hν
    have h4 := hyi i _ h3
    have hs : ‖((c : ℚ) : PadicAlgCl p)‖ = ‖((c : ℚ) : ℚ_[p])‖ := by
      rw [← PadicAlgCl.norm_extends, map_ratCast]
    rw [norm_mul, norm_inv, hs, hνμ, ← div_eq_mul_inv, div_le_iff₀ hcpos] at h4
    calc ‖μ‖ ≤ B * ‖((c : ℚ) : ℚ_[p])‖ := h4
      _ ≤ B * B := mul_le_mul_of_nonneg_left hc hB0

end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr

end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr
open GlobalTheory.LKMid.Northcott

end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr

end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr

end GlobalTheory.LKIrr

namespace GlobalTheory.LKIrr

end GlobalTheory.LKIrr
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

theorem DPair.form_law {p : ℕ} [Fact p.Prime] (G : HTGroup p) (P : DPair G) (v : InfinitePlace G.F) :
    (G.psi v P.γ)ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v P.γ =
      ((P.c : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu
  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]
  have hu : sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ =
      algebraMap ℚ G.C (P.c : ℚ) * ((P.β⁻¹ : G.Cˣ) : G.C) := by
    apply (Units.mul_right_inj (P.γ * P.β)).mp
    rw [Units.val_mul, ← Algebra.smul_def]
    calc (P.γ : G.C) * P.β * (sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ)
        = ((P.γ : G.C) * P.β * sh G (P.γ : G.C)) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ := by
          simp only [mul_assoc]
      _ = (P.c : ℚ) • ((P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ) := by
          rw [P.sim, ← Algebra.smul_def]; simp only [smul_mul_assoc]
      _ = (P.c : ℚ) • ((P.γ : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C)) := by
          rw [Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [mul_smul_comm, mul_assoc]
  rw [hH]
  calc G.gram v * G.psi v (sh G (P.γ : G.C)) * (G.gram v)⁻¹ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *
        G.psi v P.γ
      = G.gram v * (G.psi v (sh G (P.γ : G.C)) * ((G.gram v)⁻¹ * G.gram v) *
          G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) * G.psi v P.γ) := by simp only [mul_assoc]
    _ = G.gram v * G.psi v (sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ) := by
        rw [hgg', mul_one, map_mul, map_mul]
    _ = G.gram v * ((P.c : ℚ) • G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
        rw [hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]
    _ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]

end GlobalTheory.LKDef
end

section
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef.FinPol

variable {p : ℕ} [Fact p.Prime]

theorem integral_of_term_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ)
    (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r →
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → IsTest (sigG G r) (KHT p G.m G.n r G.Fw) K φ →
    ∃ N : ℕ, 0 < N ∧ ∀ P : DPair G, Irreducible P.pol → P.term L.K.toSubgroup f r K φ ≠ 0 →
      IsIntegral ℤ ((N : ℤ) • (P.γ : G.C)) ∧ IsIntegral ℤ ((N : ℤ) • ((P.γ⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G L f r K φ hr hf hφ
  obtain ⟨Ω, hΩc, hΩ⟩ := GlobalTheory.T.twistedHeckeTestFunction_support_compact p G L f hf
  obtain ⟨D, hD, hDp⟩ := GlobalTheory.T.compact_conj_charpoly_bounded_denominators_awayP p G (Ω ∪ Ω⁻¹) (hΩc.union hΩc.inv)
  obtain ⟨k, hk⟩ := GlobalTheory.T.twisted_orbit_norm_bounds p G r K φ hr hφ
  have hp := (Fact.out : p.Prime)
  refine ⟨D * p ^ (2 * k * Module.finrank ℚ G.C), Nat.mul_pos hD (pow_pos hp.pos _), ?_⟩
  intro P hirr hP
  have fin : ∀ (y0 : G.Cˣ) (c0 : ℚˣ), Irreducible (minpoly G.F (y0 : G.C)) →
      (y0 : G.C) * P.β * sh G y0 = algebraMap ℚ G.C c0 * P.β →
      ‖((c0 : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ k → ‖(((c0⁻¹ : ℚˣ) : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ k →
      (∀ (w : Fin G.m) (μ : PadicAlgCl p),
        ((G.rho w (y0 : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ (p : ℝ) ^ k) →
      (∀ (w : Fin G.m) (μ : PadicAlgCl p),
        ((G.rho w ((y0⁻¹ : G.Cˣ) : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ →
          ‖μ‖ ≤ (p : ℝ) ^ k) →
      (∀ i, ∃ kk : ℕ, ∃ a : ℤ, ((D * p ^ kk : ℕ) : ℚ) * (LinearMap.mulLeft ℚ (y0 : G.C)).charpoly.coeff i = a) →
      IsIntegral ℤ (((D * p ^ (2 * k * Module.finrank ℚ G.C) : ℕ) : ℤ) • (y0 : G.C)) := by
    intro y0 c0 hirr0 hy0 hc hc' hu hu' hAf
    have hroots := GlobalTheory.LKIrr.root_norm_le_irr G P.β y0 c0 hirr0 hy0 _ hc hc' hu hu'
    have hroots' : ∀ μ : PadicAlgCl p,
        ((LinearMap.mulLeft ℚ (y0 : G.C)).charpoly.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ →
        ‖μ‖ ≤ (p : ℝ) ^ (2 * k) := fun μ hμ => by
      rw [show 2 * k = k + k by ring, pow_add]; exact hroots μ hμ
    have h6 := GlobalTheory.T.padic_coeff_denominator_bound_of_bounded_roots p _ (LinearMap.charpoly_monic _) (2 * k) hroots'
    rw [LinearMap.charpoly_natDegree] at h6
    apply GlobalTheory.T.isIntegral_natCast_smul_of_mul_charpoly_coeff_int G.C
    intro i
    obtain ⟨kk, hkk⟩ := hAf i
    exact GlobalTheory.T.den_bound_combine_padic_primeToP p D (2 * k * Module.finrank ℚ G.C) kk hp _ (h6 i) hkk
  rw [DPair.term] at hP
  split_ifs at hP with h
  swap
  · exact absurd rfl hP
  rw [DPair.termAt, pointSum] at hP
  obtain ⟨q, hq⟩ : ∃ q, _ ≠ (0 : ℂ) := by
    by_contra hc
    push_neg at hc
    exact hP (by rw [finsum_congr hc]; exact finsum_zero)
  have hq2 := (mul_ne_zero_iff.1 hq).2
  have hfq := (mul_ne_zero_iff.1 hq2).1
  have hφq := (mul_ne_zero_iff.1 hq2).2
  set x := P.trivAf.choose with hxdef
  set o := Quotient.out q with hodef
  have hgΩ := hΩ _ hfq
  have hnrm := h.choose_spec
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hk P.atP h.choose.1 h.choose.2 o.2 hnrm hφq
  set g := o.1⁻¹ * P.toAf x P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec P.self * o.1 with hg
  have hg1 : ((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) =
      ((o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1⁻¹ * x) * Units.map (inC G (AfP p)).toMonoidHom P.γ *
        ((o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1⁻¹ * x)⁻¹ := by
    show ((o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ * (x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹) *
      (o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 = _
    group
  set X := (o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1⁻¹ * x
  have hA := hDp g (P.γ : G.C) X (Or.inl hgΩ) (by rw [hg1]; rfl)
  have hgi : g⁻¹ ∈ Ω ∪ Ω⁻¹ := Or.inr (by simpa using hgΩ)
  have hA' := hDp g⁻¹ ((P.γ⁻¹ : G.Cˣ) : G.C) X hgi (by
    show (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ).val = _
    rw [hg1]; simp [mul_assoc])
  have hc1 : ((P.atP.1 : ℚ_[p]ˣ) : ℚ_[p]) = ((P.c : ℚ) : ℚ_[p]) := by
    show algebraMap ℚ ℚ_[p] (P.c : ℚ) = _
    simp
  have hc2 : ((P.atP.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) = (((P.c⁻¹ : ℚˣ) : ℚ) : ℚ_[p]) := by
    show algebraMap ℚ ℚ_[p] ((P.c⁻¹ : ℚˣ) : ℚ) = _
    simp
  have hw1 : ∀ w, (((P.atP.2 w : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w))) =
      G.rho w (P.γ : G.C) := fun w => rfl
  have hw2 : ∀ w, ((((P.atP.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w))) =
      G.rho w ((P.γ⁻¹ : G.Cˣ) : G.C) := fun w => rfl
  have hrel' : ((P.γ⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((P.γ⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C ((P.c⁻¹ : ℚˣ) : ℚ) * P.β := (P.cent.inv_mem P.self.2).2
  have hirr' : Irreducible (minpoly G.F ((P.γ⁻¹ : G.Cˣ) : G.C)) := GlobalTheory.LKIrr.irreducible_minpoly_inv G P.γ hirr
  refine ⟨fin P.γ P.c hirr P.sim (hc1 ▸ hk1) (hc2 ▸ hk2) (fun w μ hμ => hk3 w μ (by rw [hw1]; exact hμ))
      (fun w μ hμ => hk4 w μ (by rw [hw2]; exact hμ)) hA,
    fin P.γ⁻¹ P.c⁻¹ hirr' hrel' (hc2 ▸ hk2) (by rw [inv_inv]; exact hc1 ▸ hk1)
      (fun w μ hμ => hk4 w μ (by rw [hw2]; exact hμ))
      (fun w μ hμ => hk3 w μ (by rw [hw1, ← inv_inv P.γ]; exact hμ)) hA'⟩

end GlobalTheory.LKDef.FinPol

namespace GlobalTheory.LKDef.FinPol

variable {p : ℕ} [Fact p.Prime]

theorem roots_eig (G : HTGroup p) (P : DPair G) (v : InfinitePlace G.F) (w : ℂ)
    (hw : P.pol.eval₂ v.embedding w = 0) : ∃ x : Fin G.n → ℂ, x ≠ 0 ∧ G.psi v P.γ *ᵥ x = w • x := by
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  let ψF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ :=
    { G.psi v with
      commutes' := fun x => by
        show G.psi v (algebraMap G.F G.C x) = _
        rw [G.psi_F, Matrix.algebraMap_eq_diagonal]
        rfl }
  let Ψ : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψF (fun a _ => Algebra.commute_algebraMap_left a _)
  haveI : Nontrivial (Matrix (Fin G.n) (Fin G.n) ℂ) := by
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    infer_instance
  have hinj : Function.Injective Ψ := RingHom.injective (Ψ : ℂ ⊗[G.F] G.C →+* Matrix (Fin G.n) (Fin G.n) ℂ)
  set Γ := G.psi v P.γ with hΓ
  have hΨ : ∀ k : ℕ, Ψ (1 ⊗ₜ ((P.γ : G.C) ^ k)) = Γ ^ k := by
    intro k
    calc Ψ (1 ⊗ₜ ((P.γ : G.C) ^ k)) = Algebra.ofId ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) 1 * ψF ((P.γ : G.C) ^ k) :=
          Algebra.TensorProduct.lift_tmul _ _ _ _ _
      _ = Γ ^ k := by rw [map_one, one_mul, map_pow]; rfl
  have hli0 := Module.Flat.linearIndependent_one_tmul (S := ℂ) (linearIndependent_pow (K := G.F) (P.γ : G.C))
  have hli := hli0.map' Ψ.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
  have hli' : LinearIndependent ℂ (fun i : Fin (minpoly G.F (P.γ : G.C)).natDegree => Γ ^ (i : ℕ)) := by
    have e : (⇑Ψ.toLinearMap ∘ fun i : Fin (minpoly G.F (P.γ : G.C)).natDegree =>
        (1 : ℂ) ⊗ₜ[G.F] ((P.γ : G.C) ^ (i : ℕ))) = fun i : Fin (minpoly G.F (P.γ : G.C)).natDegree => Γ ^ (i : ℕ) := by
      funext i
      exact hΨ i
    rw [e] at hli
    exact hli
  have hd : (minpoly G.F (P.γ : G.C)).natDegree = G.n := P.reg.1
  have hint : IsIntegral G.F (P.γ : G.C) := Algebra.IsIntegral.isIntegral _
  have hpm : P.pol.Monic := minpoly.monic hint
  set Q := P.pol.map (algebraMap G.F ℂ) with hQ
  have hQm : Q.Monic := hpm.map _
  have hQdeg : Q.natDegree = G.n := by rw [hQ, hpm.natDegree_map]; exact P.reg.1
  have hQΓ : Polynomial.aeval Γ Q = 0 := by
    rw [hQ, Polynomial.aeval_map_algebraMap]
    have h : Polynomial.aeval (ψF (P.γ : G.C)) P.pol = 0 := by
      rw [Polynomial.aeval_algHom_apply]
      simp [DPair.pol, minpoly.aeval]
    exact h
  have hroot : Q.IsRoot w := by
    rw [Polynomial.IsRoot, hQ, Polynomial.eval_map]; exact hw
  by_contra hne
  push_neg at hne
  have hdet : (Γ - algebraMap ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) w).det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hne x hx0
    rw [Matrix.sub_mulVec, sub_eq_zero] at hx
    rw [hx, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  set R := Q /ₘ (Polynomial.X - Polynomial.C w) with hRdef
  have hQR : (Polynomial.X - Polynomial.C w) * R = Q := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hroot
  have hRΓ : Polynomial.aeval Γ R = 0 := by
    have h1 := hQΓ
    rw [← hQR, map_mul] at h1
    have hu : IsUnit (Polynomial.aeval Γ (Polynomial.X - Polynomial.C w)) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.2 hdet
    exact (hu.mul_right_eq_zero).1 h1
  have hRd : R.natDegree = G.n - 1 := by
    rw [hRdef, Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C w), hQdeg, Polynomial.natDegree_X_sub_C]
  have hR0 : R ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQR
    exact hQm.ne_zero hQR.symm
  have hsum : ∑ i : Fin (minpoly G.F (P.γ : G.C)).natDegree, R.coeff i • Γ ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => R.coeff i • Γ ^ i), hd, ← hRΓ, Polynomial.aeval_eq_sum_range, hRd,
      Nat.sub_add_cancel G.n_pos]
  have hc := Fintype.linearIndependent_iff.1 hli' (fun i => R.coeff i) hsum
    ⟨G.n - 1, by rw [hd]; have := G.n_pos; omega⟩
  exact hR0 (Polynomial.leadingCoeff_eq_zero.1 (by rw [Polynomial.leadingCoeff, hRd]; exact hc))

theorem eig_norm_sq (G : HTGroup p) (P : DPair G) (v : InfinitePlace G.F) (w : ℂ) (x : Fin G.n → ℂ)
    (hx0 : x ≠ 0) (hx : G.psi v P.γ *ᵥ x = w • x) : ‖w‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  have hlaw := DPair.form_law G P v
  set H := G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) with hH
  set A := G.psi v (P.γ : G.C) with hA
  set q : ℂ := star x ⬝ᵥ (H *ᵥ x) with hq
  have hq0 : q ≠ 0 := by
    intro h0
    have hd := P.posR v x hx0
    by_cases hv : sigPosH (G.gram_herm v) = 1
    · have := hd.1 hv; rw [← hH, ← hq, h0] at this; simp at this
    · have := hd.2 hv; rw [← hH, ← hq, h0] at this; simp at this
  have key : star x ⬝ᵥ ((Aᴴ * H * A) *ᵥ x) = (star w * w) * q := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hx, dotProduct_mulVec, ← star_mulVec, hx, mulVec_smul, star_smul,
      smul_dotProduct, dotProduct_smul, hq]
    simp only [smul_eq_mul]; ring
  rw [hlaw, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at key
  have hc : star w * w = ((P.c : ℚ) : ℂ) := mul_right_cancel₀ hq0 key.symm
  have h2 : ((Complex.normSq w : ℝ) : ℂ) = ((((P.c : ℚ) : ℝ)) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    push_cast
    exact hc
  rw [← Complex.normSq_eq_norm_sq]
  exact_mod_cast h2

end GlobalTheory.LKDef.FinPol

namespace GlobalTheory.LKDef.FinPol

open GlobalTheory.LKMid.Northcott

variable {p : ℕ} [Fact p.Prime]

theorem finite_pol_int (G : HTGroup p) (N : ℕ) (hN : 0 < N) :
    {P0 : Polynomial G.F | ∃ P : DPair G, P.pol = P0 ∧
      IsIntegral ℤ ((N : ℤ) • (P.γ : G.C)) ∧ IsIntegral ℤ ((N : ℤ) • ((P.γ⁻¹ : G.Cˣ) : G.C))}.Finite := by
  refine (GlobalTheory.T.finite_monic_of_roots_bdd_of_mul_isIntegral G.F G.n N N hN).subset ?_
  rintro _ ⟨P, rfl, hI1, hI2⟩
  have hc0 : ((P.c : ℚ) : ℝ) ≠ 0 := by exact_mod_cast P.c.ne_zero
  have hint : ∀ (v : InfinitePlace G.F) (w : ℂ) (x : Fin G.n → ℂ), x ≠ 0 → G.psi v P.γ *ᵥ x = w • x →
      IsIntegral ℤ ((N : ℂ) * w) ∧ IsIntegral ℤ ((N : ℂ) * w⁻¹) := by
    intro v w x hx hwx
    have hinv : G.psi v ((P.γ⁻¹ : G.Cˣ) : G.C) * G.psi v (P.γ : G.C) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hx' : x = w • (G.psi v ((P.γ⁻¹ : G.Cˣ) : G.C) *ᵥ x) := by
      conv_lhs => rw [← Matrix.one_mulVec x, ← hinv, ← Matrix.mulVec_mulVec, hwx, Matrix.mulVec_smul]
    have hw0 : w ≠ 0 := by
      rintro rfl; apply hx; rw [hx', zero_smul]
    have hinvx : G.psi v ((P.γ⁻¹ : G.Cˣ) : G.C) *ᵥ x = w⁻¹ • x := by
      calc _ = w⁻¹ • (w • (G.psi v ((P.γ⁻¹ : G.Cˣ) : G.C) *ᵥ x)) := by
            rw [smul_smul, inv_mul_cancel₀ hw0, one_smul]
        _ = w⁻¹ • x := by rw [← hx']
    constructor
    · refine isIntegral_eig (hI1.map (G.psi v).toIntAlgHom) hx ?_
      change G.psi v ((N : ℤ) • (P.γ : G.C)) *ᵥ x = _
      rw [map_zsmul, Matrix.smul_mulVec, hwx, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
      push_cast; rfl
    · refine isIntegral_eig (hI2.map (G.psi v).toIntAlgHom) hx ?_
      change G.psi v ((N : ℤ) • ((P.γ⁻¹ : G.Cˣ) : G.C)) *ᵥ x = _
      rw [map_zsmul, Matrix.smul_mulVec, hinvx, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
      push_cast; rfl
  have hkey : ∀ (v : InfinitePlace G.F) (w : ℂ), P.pol.eval₂ v.embedding w = 0 →
      ‖w‖ ≤ N ∧ IsIntegral ℤ ((N : ℂ) * w) := by
    intro v w hw
    obtain ⟨x, hx, hwx⟩ := roots_eig G P v w hw
    obtain ⟨h2, h3⟩ := hint v w x hx hwx
    exact ⟨norm_le_of_isIntegral_inv w P.c N hN (eig_norm_sq G P v w x hx hwx) hc0 h3, h2⟩
  refine ⟨minpoly.monic (Algebra.IsIntegral.isIntegral _), P.reg.1, ?_⟩
  intro φ w hw
  have hr : P.pol.eval₂ φ w = 0 := by
    have := (Polynomial.mem_roots'.1 hw).2
    rwa [Polynomial.IsRoot, Polynomial.eval_map] at this
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [← h] at hr; exact hkey _ w hr
  · have hr' : P.pol.eval₂ (InfinitePlace.mk φ).embedding (starRingEnd ℂ w) = 0 := by
      rw [h]
      have := congrArg (starRingEnd ℂ) hr
      rw [map_zero, Polynomial.hom_eval₂] at this
      convert this using 2
      exact RingHom.ext fun x => rfl
    obtain ⟨h1, h2⟩ := hkey _ _ hr'
    refine ⟨by simpa using h1, ?_⟩
    have := h2.map (starRingEnd ℂ).toIntAlgHom
    simpa using this

theorem finite_pol_term_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      {P0 : Polynomial G.F | ∃ P : GlobalTheory.LKDef.DPair G, P.pol = P0 ∧ Irreducible P.pol ∧
        P.term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  intro p _ G _ L f hf _ K' f' hf' _
  obtain ⟨N, hN, hb⟩ := integral_of_term_ne_zero p G L f 1 K' f' one_pos hf hf'
  refine (finite_pol_int G N hN).subset ?_
  rintro _ ⟨P, rfl, hi, ht⟩
  exact ⟨P, rfl, hb P hi ht⟩

end GlobalTheory.LKDef.FinPol
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_minpoly_definitePairs_term_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      {P0 : Polynomial G.F | ∃ P : GlobalTheory.LKDef.DPair G, P.pol = P0 ∧ Irreducible P.pol ∧
        P.term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  atlas_forward_decl GlobalTheory.LKDef.FinPol.finite_pol_term_ne_zero
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem units_conj_of_minpoly_eq_of_irreducible : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (a b : G.Cˣ),
    minpoly G.F (a : G.C) = minpoly G.F (b : G.C) → Irreducible (minpoly G.F (b : G.C)) →
      ∃ g : G.Cˣ, (a : G.C) = g * b * ↑g⁻¹ := by
  intro p _ G a b h hirr
  have hb : IsIntegral G.F (b : G.C) := IsIntegral.of_finite G.F _
  haveI : Fact (Irreducible (minpoly G.F (b : G.C))) := ⟨hirr⟩
  haveI : FiniteDimensional G.F (AdjoinRoot (minpoly G.F (b : G.C))) :=
    (AdjoinRoot.powerBasis (minpoly.ne_zero hb)).finite
  have ha : Polynomial.aeval (a : G.C) (minpoly G.F (b : G.C)) = 0 := by rw [← h]; exact minpoly.aeval _ _
  obtain ⟨y, hy⟩ := GroundTheory.Brauer.exists_unit_conj (evalQuot _ (b : G.C) (minpoly.aeval _ _))
    (evalQuot _ (a : G.C) ha)
  refine ⟨y, ?_⟩
  have := hy (AdjoinRoot.root _)
  rwa [evalQuot_root, evalQuot_root] at this

end GlobalTheory.LKCx
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentConj

variable {p : ℕ} [Fact p.Prime]

theorem sh_mul' (G : HTGroup p) (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_add' (G : HTGroup p) (x y : G.C) : sh G (x + y) = sh G x + sh G y := by
  simp only [sh, map_add, MulOpposite.unop_add]

theorem sh_one' (G : HTGroup p) : sh G 1 = 1 := by
  simp only [sh, map_one, MulOpposite.unop_one]

theorem sh_sh' (G : HTGroup p) (x : G.C) : sh G (sh G x) = x := G.star_star x

theorem sh_inv_of_sym (G : HTGroup p) (β : G.Cˣ) (hβ : sh G β = β) :
    sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) := by
  have e : sh G ((β⁻¹ : G.Cˣ) : G.C) * β = 1 := by
    rw [← hβ, ← sh_mul', Units.mul_inv, sh_one']
  calc sh G ((β⁻¹ : G.Cˣ) : G.C) = sh G ((β⁻¹ : G.Cˣ) : G.C) * β * ((β⁻¹ : G.Cˣ) : G.C) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [e, one_mul]

end GlobalTheory.CentConj

namespace GlobalTheory.CentConj

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.CentConj
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentSim

variable {p : ℕ} [Fact p.Prime]

theorem commute_conj_sh_sim (G : HTGroup p) (β γ : G.Cˣ) (c₀ : ℚ)
    (h : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c₀ * β) (z : G.C) (hz : Commute z (γ : G.C)) :
    Commute ((β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C)) (γ : G.C) := by
  set y : G.Cˣ := γ with hydef
  set c : G.C := algebraMap ℚ G.C c₀
  set Y := sh G (y : G.C)
  set Yi := sh G ((y⁻¹ : G.Cˣ) : G.C)
  have hYYi : Y * Yi = 1 := by
    simp only [Y, Yi, ← GlobalTheory.CentConj.sh_mul', Units.inv_mul, GlobalTheory.CentConj.sh_one']
  have hzi : Commute z ((y⁻¹ : G.Cˣ) : G.C) := hz.units_inv_right
  have hcomm : Yi * sh G z = sh G z * Yi := by
    simp only [Yi, ← GlobalTheory.CentConj.sh_mul']; rw [hzi.eq]
  have hcc : ∀ w : G.C, c * w = w * c := fun w => Algebra.commutes _ w
  have h1 : (y : G.C) * β = c * β * Yi := by
    calc (y : G.C) * β = (y : G.C) * β * (Y * Yi) := by rw [hYYi, mul_one]
      _ = c * β * Yi := by rw [← mul_assoc, h]
  have h2 : ((β⁻¹ : G.Cˣ) : G.C) * y = c * Yi * ((β⁻¹ : G.Cˣ) : G.C) := by
    calc ((β⁻¹ : G.Cˣ) : G.C) * y = ((β⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * β) * ((β⁻¹ : G.Cˣ) : G.C) := by
          simp only [mul_assoc, Units.mul_inv, mul_one]
      _ = c * Yi * ((β⁻¹ : G.Cˣ) : G.C) := by
          rw [h1, ← mul_assoc, ← mul_assoc, ← hcc, mul_assoc c, Units.inv_mul, mul_one]
  change (β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C) * y = y * ((β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C))
  calc (β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C) * y
        = (β : G.C) * sh G z * (((β⁻¹ : G.Cˣ) : G.C) * y) := by rw [mul_assoc]
    _ = c * (β * (sh G z * Yi)) * ((β⁻¹ : G.Cˣ) : G.C) := by
        rw [h2]; simp only [mul_assoc]
        rw [← mul_assoc (sh G z) c, ← hcc (sh G z), mul_assoc c, ← mul_assoc (β : G.C) c, ← hcc (β : G.C)]
        simp only [mul_assoc]
    _ = c * (β * (Yi * sh G z)) * ((β⁻¹ : G.Cˣ) : G.C) := by rw [hcomm]
    _ = (y : G.C) * β * sh G z * ((β⁻¹ : G.Cˣ) : G.C) := by rw [h1]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

theorem centraliser_field_involution : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β γ : G.Cˣ) (c₀ : ℚˣ), sh G β = β →
    (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c₀ * β → Irreducible (minpoly G.F (γ : G.C)) →
    (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
      Function.Injective ι ∧ (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) ∧
      (∀ x, ι (c x) = β * sh G (ι x) * ((β⁻¹ : G.Cˣ) : G.C)) ∧ ∀ x, c (c x) = x := by
  intro p _ G β γ c₀ hβ hsim hirr hdeg
  obtain ⟨E, _, _, _, j, hj, hcent⟩ := GlobalTheory.CentIrr.centralizer_unit_eq_field p G γ hirr hdeg
  set w : E → G.C := fun e => (β : G.C) * sh G (j e) * ((β⁻¹ : G.Cˣ) : G.C) with hw
  have hex : ∀ e, ∃ e', j e' = w e := fun e =>
    (hcent _).1 (commute_conj_sh_sim G β γ (c₀ : ℚ) hsim (j e) ((hcent _).2 ⟨e, rfl⟩))
  choose t ht using hex
  have tt : ∀ e, t (t e) = e := by
    intro e
    apply hj
    rw [ht, hw]; dsimp only
    rw [ht, GlobalTheory.CentConj.sh_mul', GlobalTheory.CentConj.sh_mul', GlobalTheory.CentConj.sh_sh', hβ,
      GlobalTheory.CentConj.sh_inv_of_sym G β hβ]
    simp only [mul_assoc, Units.mul_inv, mul_one]
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have hm : ∀ a b, t (a * b) = t a * t b := by
    intro a b
    apply hj
    rw [mul_comm a b, ht, map_mul, ht, ht, hw]; dsimp only
    rw [map_mul, GlobalTheory.CentConj.sh_mul']
    simp only [mul_assoc]
    rw [← mul_assoc ((β⁻¹ : G.Cˣ) : G.C) (β : G.C), Units.inv_mul, one_mul]
  have ha : ∀ a b, t (a + b) = t a + t b := by
    intro a b
    apply hj
    rw [ht, map_add, ht, ht, hw]; dsimp only
    rw [map_add, GlobalTheory.CentConj.sh_add']; noncomm_ring
  have h1 : t 1 = 1 := by
    apply hj
    rw [ht, hw]; dsimp only
    rw [map_one, GlobalTheory.CentConj.sh_one', mul_one, Units.mul_inv]
  have h0 : t 0 = 0 := by
    have h := ha 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  let τ : E →+* E := { toFun := t, map_one' := h1, map_mul' := hm, map_zero' := h0, map_add' := ha }
  refine ⟨E, inferInstance, inferInstance, j.toRingHom.toRatAlgHom, τ.toRatAlgHom, hj, ?_, ?_, ?_⟩
  · intro z
    exact hcent z
  · intro x; exact ht x
  · intro x; exact tt x

end GlobalTheory.CentSim

example : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β γ : G.Cˣ) (c₀ : ℚˣ), sh G β = β →
    (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c₀ * β → Irreducible (minpoly G.F (γ : G.C)) →
    (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
      Function.Injective ι ∧ (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) ∧
      (∀ x, ι (c x) = β * sh G (ι x) * ((β⁻¹ : G.Cˣ) : G.C)) ∧ ∀ x, c (c x) = x :=
  GlobalTheory.CentSim.centraliser_field_involution
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numberField_involution_similitudeCentralizer : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β γ : G.Cˣ) (c₀ : ℚˣ), sh G β = β →
    (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c₀ * β → Irreducible (minpoly G.F (γ : G.C)) →
    (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
      Function.Injective ι ∧ (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) ∧
      (∀ x, ι (c x) = β * sh G (ι x) * ((β⁻¹ : G.Cˣ) : G.C)) ∧ ∀ x, c (c x) = x := by
  first | (exact @GlobalTheory.CentSim.centraliser_field_involution) | (exact GlobalTheory.CentSim.centraliser_field_involution) | (intros; apply GlobalTheory.CentSim.centraliser_field_involution  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocTriv

set_option maxHeartbeats 1000000 in

theorem ratio_local_norm_dpair : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω →
    ∀ (P₁ : GlobalTheory.LKDef.DPair G) (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
    Function.Injective ι → (∀ z : G.C, z * P₁.γ = P₁.γ * z ↔ ∃ w, ι w = z) →
    (∀ x, ι (c x) = P₁.β * sh G (ι x) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ), ∀ (P : GlobalTheory.LKDef.DPair G), P.γ = P₁.γ → P.c = P₁.c →
      (∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.toAf x t hx P.self ∈ Ω) →
      ∀ a : L, ι a = ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) → ∀ v ∉ S,
        ∃ (r : (v.adicCompletion ℚ)ˣ) (y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ),
          (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] a = algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L) (r : v.adicCompletion ℚ) *
            ((y : v.adicCompletion ℚ ⊗[ℚ] L) * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c y) := by
  intro p _ G Ω hΩ P₁ L _ _ ι c hinj hcent hc
  obtain ⟨x₁, t₁, hx₁⟩ := P₁.trivAf
  have hβ₁inv := sh_inv_unit G P₁.β P₁.sym
  have hcc : ∀ x, c (c x) = x := fun x => hinj (by
    rw [hc, hc, sh_mul', sh_mul', sh_sh, hβ₁inv, P₁.sym]
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one])
  have hcne : ∃ x, c x ≠ x := by
    obtain ⟨τ⟩ : Nonempty (G.F →+* ℂ) := inferInstance
    obtain ⟨f, -, hf⟩ := G.hKq.2 τ
    have hconj : IsCMField.complexConj G.F f ≠ f := by
      intro h
      apply hf
      have e := IsCMField.complexEmbedding_complexConj G.F τ f
      rw [h] at e
      exact Complex.conj_eq_iff_im.1 e.symm
    obtain ⟨w, hw⟩ := (hcent (algebraMap G.F G.C f)).1 (Algebra.commutes f _)
    refine ⟨w, fun h => hconj ?_⟩
    have e2 : ι (c w) = algebraMap G.F G.C (IsCMField.complexConj G.F f) := by
      rw [hc, hw, sh_algebraMap, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]
    rw [h, hw] at e2
    exact ((algebraMap G.F G.C).injective e2).symm
  obtain ⟨S1, hS1⟩ := exists_finset_of_eventually (GlobalTheory.OrbFinAf.cptInt p G Ω hΩ)
  obtain ⟨S2, hS2⟩ := exists_finset_of_eventually
    (GlobalTheory.OrbFinAf.cptInt p G {P₁.toAf x₁ t₁ hx₁ P₁.self} isCompact_singleton)
  obtain ⟨S3, hS3⟩ := GlobalTheory.T.eventually_adic_integral_span_closed_mul_star G.C G.star _ (Module.finBasis ℚ G.C)
  obtain ⟨S4, hS4⟩ := GlobalTheory.T.eventually_integral_conjugators_differ_by_centralizer p G P₁.γ P₁.reg.1 P₁.reg.2 L ι hinj hcent _ (Module.finBasis ℚ G.C)
  obtain ⟨S5, hS5⟩ := GlobalTheory.T.almost_all_places_twisted_unit_integral G.C L ι hinj _ (Module.finBasis ℚ G.C) _ (Module.finBasis ℚ L)
  obtain ⟨S6, hS6⟩ := GlobalTheory.T.fixed_unit_eq_norm_almost_all_places L c hcc hcne _ (Module.finBasis ℚ L)
  refine ⟨S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ (finite_above p).toFinset, ?_⟩
  intro P hγ hcP hex a ha v hv
  obtain ⟨x, t, hx, hxΩ⟩ := hex
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨⟨⟨⟨⟨hv1, hv2⟩, hv3⟩, hv4⟩, hv5⟩, hv6⟩, hvp⟩ := hv
  have hvp' : v.asIdeal ≠ Ideal.span {(p : ℤ)} := fun h => hvp ((Set.Finite.mem_toFinset _).2 h)
  let w : AwayP p := ⟨v, hvp'⟩
  let K := v.adicCompletion ℚ
  let φ : AfP p ⊗[ℚ] G.C →ₐ[ℚ] K ⊗[ℚ] G.C := Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)
  let ιv : K ⊗[ℚ] L →ₐ[ℚ] K ⊗[ℚ] G.C := Algebra.TensorProduct.map (AlgHom.id ℚ K) ι
  let cv : K ⊗[ℚ] L →ₐ[ℚ] K ⊗[ℚ] L := Algebra.TensorProduct.map (AlgHom.id ℚ K) c
  let X : (K ⊗[ℚ] G.C)ˣ := Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) x
  let X₁ : (K ⊗[ℚ] G.C)ˣ := Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) x₁
  have key : ∀ (Q : GlobalTheory.LKDef.DPair G) (y : (AfP p ⊗[ℚ] G.C)ˣ) (s : (AfP p)ˣ) (hy : Triv G (AfP p) Q.β y s),
      ((((GlobalTheory.OrbFinAf.piV G w (Q.toAf y s hy Q.self) : GlobalTheory.OrbFinAf.Gv G w) :
        (K ⊗[ℚ] G.C)ˣ × Kˣ).1 : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) =
        ↑(Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) y) * ((1 : K) ⊗ₜ[ℚ] (Q.γ : G.C)) *
          ↑(Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) y)⁻¹ := by
    intro Q y s hy
    show φ (↑y * ((1 : AfP p) ⊗ₜ[ℚ] (Q.γ : G.C)) * ↑y⁻¹) = _
    rw [map_mul, map_mul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    rfl
  have hXg : IsIntB v (Module.finBasis ℚ G.C) (↑X * ((1 : K) ⊗ₜ[ℚ] (P₁.γ : G.C)) * ↑X⁻¹) := by
    have h := (hS1 w hv1 ⟨_, hxΩ, rfl⟩).1
    rw [key P x t hx, hγ] at h
    exact h
  have hX₁g : IsIntB v (Module.finBasis ℚ G.C) (↑X₁ * ((1 : K) ⊗ₜ[ℚ] (P₁.γ : G.C)) * ↑X₁⁻¹) := by
    have h := (hS2 w hv2 ⟨_, rfl, rfl⟩).1
    rw [key P₁ x₁ t₁ hx₁] at h
    exact h

  obtain ⟨m, hm1, hm2⟩ := hS4 v hv4 X X₁ hXg hX₁g
  obtain ⟨hmul, hstar⟩ := hS3 v hv3
  let T : Kˣ := Units.map (AfP.eval w : AfP p →* K) t
  let T₁ : Kˣ := Units.map (AfP.eval w : AfP p →* K) t₁
  let β₁v : (K ⊗[ℚ] G.C)ˣ :=
    Units.map ((Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] K ⊗[ℚ] G.C) : G.C →* K ⊗[ℚ] G.C) P₁.β
  have hiota_a : ιv ((1 : K) ⊗ₜ[ℚ] a) * (β₁v : K ⊗[ℚ] G.C) = (1 : K) ⊗ₜ[ℚ] (P.β : G.C) := by
    show (1 : K) ⊗ₜ[ℚ] ι a * (1 : K) ⊗ₜ[ℚ] (P₁.β : G.C) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ha, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  have htriv : ∀ (Q : GlobalTheory.LKDef.DPair G) (y : (AfP p ⊗[ℚ] G.C)ˣ) (s : (AfP p)ˣ), Triv G (AfP p) Q.β y s →
      (↑(Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) y) : K ⊗[ℚ] G.C) * ((1 : K) ⊗ₜ[ℚ] (Q.β : G.C)) *
        (starT G.star K ↑(Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) y)).unop =
        algebraMap K (K ⊗[ℚ] G.C) (AfP.eval w (s : AfP p)) := by
    intro Q y s hy
    have hy' : (y : AfP p ⊗[ℚ] G.C) * inC G (AfP p) Q.β * (starT G.star (AfP p) y).unop =
        algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s := hy
    have h := congrArg (Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)) hy'
    rw [map_mul, map_mul, map_starT] at h
    have e1 : Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (inC G (AfP p) Q.β) =
        (1 : K) ⊗ₜ[ℚ] (Q.β : G.C) := by
      simp [inC, Algebra.TensorProduct.map_tmul]
    have e2 : Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s) =
        algebraMap K (K ⊗[ℚ] G.C) (AfP.eval w (s : AfP p)) := by
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
    rw [e1, e2] at h
    exact h
  have h1 : (X : K ⊗[ℚ] G.C) * (ιv ((1 : K) ⊗ₜ[ℚ] a) * β₁v) * (starT G.star K X).unop =
      algebraMap K (K ⊗[ℚ] G.C) (T : K) := by
    rw [hiota_a]; exact htriv P x t hx
  have h2 : (X₁ : K ⊗[ℚ] G.C) * β₁v * (starT G.star K X₁).unop = algebraMap K (K ⊗[ℚ] G.C) (T₁ : K) :=
    htriv P₁ x₁ t₁ hx₁
  have hιR : ∀ r : K, ιv (algebraMap K (K ⊗[ℚ] L) r) = algebraMap K (K ⊗[ℚ] G.C) r := by
    intro r; simp [ιv, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  have hcm : ιv (cv ↑m) = ↑β₁v * (starT G.star K (ιv ↑m)).unop * ↑β₁v⁻¹ := map_conj_ext G K ι c P₁.β hc ↑m
  have hcore := selfDual_conj_eq_one (R := K) (ιv : K ⊗[ℚ] L →+* K ⊗[ℚ] G.C) hιR (starT G.star K) (cv : K ⊗[ℚ] L →+* K ⊗[ℚ] L)
    β₁v X X₁ T T₁ ((1 : K) ⊗ₜ[ℚ] a) m hcm h1 h2
  simp only [RingHom.coe_coe] at hcore

  have hu'u : ((X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹) * ((X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹) = 1 := by
    calc ((X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹) * ((X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹)
        = (X₁ : K ⊗[ℚ] G.C) * (ιv ↑m⁻¹ * ((↑X⁻¹ : K ⊗[ℚ] G.C) * ↑X) * ιv ↑m) * ↑X₁⁻¹ := by
          simp only [mul_assoc]
      _ = 1 := by rw [Units.inv_mul, mul_one, ← map_mul, Units.inv_mul, map_one, mul_one, Units.mul_inv]
  have hshu : (starT G.star K ((X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹)).unop *
      (starT G.star K ((X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, hu'u, map_one, MulOpposite.unop_one]
  set u := (X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹ with hu
  set u' := (X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹ with hu'
  set E := algebraMap K (K ⊗[ℚ] L) (↑T⁻¹ * ↑T₁) * ((1 : K) ⊗ₜ[ℚ] a) * (↑m⁻¹ * cv ↑m⁻¹) with hE
  set wv := (X₁ : K ⊗[ℚ] G.C) * ιv E * ↑X₁⁻¹ with hwvdef
  have hwv : wv = u' * (starT G.star K u').unop := by
    calc wv = (u' * u) * wv * ((starT G.star K u).unop * (starT G.star K u').unop) := by
          rw [hu'u, hshu, one_mul, mul_one]
      _ = u' * (u * wv * (starT G.star K u).unop) * (starT G.star K u').unop := by simp only [mul_assoc]
      _ = _ := by rw [hcore, mul_one]
  have hwvI : IsIntB v (Module.finBasis ℚ G.C) wv := hwv ▸ hmul _ _ hm2 (hstar _ hm2)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (Units.ne_zero _) ha.symm
  obtain ⟨Eu, hEu⟩ : ∃ Eu : (K ⊗[ℚ] L)ˣ, (Eu : K ⊗[ℚ] L) = E :=
    ⟨Units.map (algebraMap K (K ⊗[ℚ] L) : K →* K ⊗[ℚ] L) (T⁻¹ * T₁) *
      Units.map ((Algebra.TensorProduct.includeRight : L →ₐ[ℚ] K ⊗[ℚ] L) : L →* K ⊗[ℚ] L) (Units.mk0 a ha0) *
        (m⁻¹ * Units.map (cv : K ⊗[ℚ] L →* K ⊗[ℚ] L) m⁻¹), by
      simp only [Units.val_mul, Units.coe_map, Units.val_mk0, hE, map_mul]
      rfl⟩
  have h_a : ((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹) * wv = 1 := by
    rw [hwvdef, ← hEu]
    calc ((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹) * ((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu * ↑X₁⁻¹)
        = (X₁ : K ⊗[ℚ] G.C) * (ιv ↑Eu⁻¹ * ((↑X₁⁻¹ : K ⊗[ℚ] G.C) * ↑X₁) * ιv ↑Eu) * ↑X₁⁻¹ := by
          simp only [mul_assoc]
      _ = 1 := by rw [Units.inv_mul X₁, mul_one, ← map_mul ιv, Units.inv_mul Eu, map_one, mul_one, Units.mul_inv X₁]
  have h_b : wv * ((starT G.star K u).unop * u) = 1 := by
    calc wv * ((starT G.star K u).unop * u) = (u' * u) * wv * (starT G.star K u).unop * u := by
          rw [hu'u, one_mul]; simp only [mul_assoc]
      _ = u' * (u * wv * (starT G.star K u).unop) * u := by simp only [mul_assoc]
      _ = 1 := by rw [hcore, mul_one, hu'u]
  have hwv' : (X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹ = (starT G.star K u).unop * u := by
    calc (X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹
        = ((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹) * (wv * ((starT G.star K u).unop * u)) := by rw [h_b, mul_one]
      _ = (((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹) * wv) * ((starT G.star K u).unop * u) := by
          rw [← mul_assoc]
      _ = _ := by rw [h_a, one_mul]
  have hE1 : IsIntB v (Module.finBasis ℚ L) (Eu : K ⊗[ℚ] L) := hS5 v hv5 X₁ _ (by rw [hEu]; exact hwvI)
  have hE2 : IsIntB v (Module.finBasis ℚ L) ((Eu⁻¹ : (K ⊗[ℚ] L)ˣ) : K ⊗[ℚ] L) :=
    hS5 v hv5 X₁ _ (by rw [hwv']; exact hmul _ _ (hstar _ hm1) hm1)
  have hca : c a = a := hinj (by
    rw [hc, ha, Units.val_mul, sh_mul', hβ₁inv, P.sym]
    simp only [mul_assoc, Units.mul_inv_cancel_left])
  have hcalg : ∀ r : K, cv (algebraMap K (K ⊗[ℚ] L) r) = algebraMap K (K ⊗[ℚ] L) r := by
    intro r; simp [cv, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  have hcinv : cv (cv ↑m⁻¹) = ↑m⁻¹ := map_invol c hcc _
  have hfix : cv ↑Eu = ↑Eu := by
    have : cv ((1 : K) ⊗ₜ[ℚ] a) = (1 : K) ⊗ₜ[ℚ] a := by
      show (1 : K) ⊗ₜ[ℚ] c a = _
      rw [hca]
    rw [hEu, hE]
    simp only [map_mul, hcalg, hcinv, this]
    ring
  obtain ⟨y₀, hy₀⟩ := hS6 v hv6 Eu hfix hE1 hE2
  refine ⟨T * T₁⁻¹, m * y₀, ?_⟩
  rw [hEu, hE, map_mul] at hy₀
  have hm' : (m : K ⊗[ℚ] L) * ↑m⁻¹ = 1 := Units.mul_inv m
  have hcm' : cv ↑m * cv ↑m⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hT : algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hT₁ : algebraMap K (K ⊗[ℚ] L) ↑T₁ * algebraMap K (K ⊗[ℚ] L) ↑T₁⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  show (1 : K) ⊗ₜ[ℚ] a = algebraMap K (K ⊗[ℚ] L) ↑(T * T₁⁻¹) * (↑(m * y₀) * cv ↑(m * y₀))
  rw [Units.val_mul, Units.val_mul, map_mul, map_mul]
  linear_combination (algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T₁⁻¹ * ↑m * cv ↑m) * hy₀ -
    ((1 : K) ⊗ₜ[ℚ] a) * hT - ((1 : K) ⊗ₜ[ℚ] a) * algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ * hT₁ -
    ((1 : K) ⊗ₜ[ℚ] a) * algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ *
      algebraMap K (K ⊗[ℚ] L) ↑T₁ * algebraMap K (K ⊗[ℚ] L) ↑T₁⁻¹ * hm' -
    ((1 : K) ⊗ₜ[ℚ] a) * algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ *
      algebraMap K (K ⊗[ℚ] L) ↑T₁ * algebraMap K (K ⊗[ℚ] L) ↑T₁⁻¹ * ↑m * ↑m⁻¹ * hcm'

end GlobalTheory.LocTriv
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definitePairs_ratio_locally_rational_times_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω →
    ∀ (P₁ : GlobalTheory.LKDef.DPair G) (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
    Function.Injective ι → (∀ z : G.C, z * P₁.γ = P₁.γ * z ↔ ∃ w, ι w = z) →
    (∀ x, ι (c x) = P₁.β * sh G (ι x) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ), ∀ (P : GlobalTheory.LKDef.DPair G), P.γ = P₁.γ → P.c = P₁.c →
      (∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.toAf x t hx P.self ∈ Ω) →
      ∀ a : L, ι a = ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) → ∀ v ∉ S,
        ∃ (r : (v.adicCompletion ℚ)ˣ) (y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ),
          (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] a = algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L) (r : v.adicCompletion ℚ) *
            ((y : v.adicCompletion ℚ ⊗[ℚ] L) * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c y) := by
  first | (exact @GlobalTheory.LocTriv.ratio_local_norm_dpair) | (exact GlobalTheory.LocTriv.ratio_local_norm_dpair) | (intros; apply GlobalTheory.LocTriv.ratio_local_norm_dpair  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKDefFin

open GlobalTheory.LKDef GlobalTheory.LKMid.PairConj

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem form_conj (v : InfinitePlace G.F) (β y : G.Cˣ) (x : Fin G.n → ℂ) :
    star x ⬝ᵥ ((G.gram v * G.psi v (((y * β * shU G y)⁻¹ : G.Cˣ) : G.C)) *ᵥ x) =
      star (G.psi v ((y⁻¹ : G.Cˣ) : G.C) *ᵥ x) ⬝ᵥ
        ((G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *ᵥ (G.psi v ((y⁻¹ : G.Cˣ) : G.C) *ᵥ x)) := by
  have e1 : (((y * β * shU G y)⁻¹ : G.Cˣ) : G.C) =
      sh G ((y⁻¹ : G.Cˣ) : G.C) * (((β⁻¹ : G.Cˣ) : G.C) * ((y⁻¹ : G.Cˣ) : G.C)) := by
    simp only [_root_.mul_inv_rev, Units.val_mul]; rfl
  have e2 : G.psi v (sh G ((y⁻¹ : G.Cˣ) : G.C)) =
      (G.gram v)⁻¹ * (G.psi v ((y⁻¹ : G.Cˣ) : G.C))ᴴ * G.gram v := G.psi_star v _
  have hg : G.gram v * (G.gram v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (Ne.isUnit (G.gram_det v))
  have e3 : G.gram v * G.psi v (((y * β * shU G y)⁻¹ : G.Cˣ) : G.C) =
      (G.psi v ((y⁻¹ : G.Cˣ) : G.C))ᴴ * (G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)) *
        G.psi v ((y⁻¹ : G.Cˣ) : G.C) := by
    rw [e1, map_mul, map_mul, e2]
    calc G.gram v * ((G.gram v)⁻¹ * (G.psi v ((y⁻¹ : G.Cˣ) : G.C))ᴴ * G.gram v *
          (G.psi v ((β⁻¹ : G.Cˣ) : G.C) * G.psi v ((y⁻¹ : G.Cˣ) : G.C)))
        = (G.gram v * (G.gram v)⁻¹) * (G.psi v ((y⁻¹ : G.Cˣ) : G.C))ᴴ * G.gram v *
          (G.psi v ((β⁻¹ : G.Cˣ) : G.C) * G.psi v ((y⁻¹ : G.Cˣ) : G.C)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg, Matrix.one_mul]; simp only [Matrix.mul_assoc]
  rw [e3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

def conjD (P : DPair G) (y : G.Cˣ) : DPair G where
  β := y * P.β * shU G y
  γ := y * P.γ * y⁻¹
  c := P.c
  sym := by
    simp only [Units.val_mul, shU_val, sh_mul, sh_sh, P.sym, mul_assoc]
  sim := by
    have hs := P.sim
    have h1 := unop_mul_inv G.star y
    simp only [Units.val_mul, shU_val, sh_mul]
    calc _ = (y : G.C) * (P.γ * (((y⁻¹ : G.Cˣ) : G.C) * y) * P.β * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C)) * sh G P.γ) *
            sh G y := by simp only [mul_assoc]
      _ = y * ((P.γ : G.C) * P.β * sh G P.γ) * sh G y := by
            rw [Units.inv_mul, show sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 from h1, mul_one, mul_one]
      _ = _ := by
            rw [hs, ← mul_assoc, ← mul_assoc, ← Algebra.commutes, mul_assoc _ (y : G.C), mul_assoc, mul_assoc]
  reg := by
    have e : ((y * P.γ * y⁻¹ : G.Cˣ) : G.C) = conjAlg G y P.γ := by simp [conjAlg]
    rw [e, minpoly.algHom_eq (conjAlg G y) (conjAlg_injective G y)]
    exact P.reg
  trivAf := by
    obtain ⟨x, t, hx⟩ := P.trivAf
    have h := triv_conj_unit (AfP p) (P.β : G.C) y x t hx
    rw [← conj_val] at h
    exact ⟨_, t, h⟩
  posR := by
    intro v x hx
    have hM : G.psi v ((y⁻¹ : G.Cˣ) : G.C) *ᵥ x ≠ 0 := by
      intro h0; apply hx
      have e : G.psi v (y : G.C) *ᵥ (G.psi v ((y⁻¹ : G.Cˣ) : G.C) *ᵥ x) = x := by
        rw [Matrix.mulVec_mulVec, ← map_mul, Units.mul_inv, map_one, Matrix.one_mulVec]
      rw [← e, h0, Matrix.mulVec_zero]
    rw [form_conj]
    exact P.posR v _ hM

theorem conjD_β (P : DPair G) (y : G.Cˣ) :
    (((conjD P y).β : G.Cˣ) : G.C) = (y : G.C) * P.β * sh G y := conj_val P.β y

theorem exists_conj (P : DPair G) (y : G.Cˣ) :
    ∃ P' : DPair G, P.Rel P' ∧ P'.γ = y * P.γ * y⁻¹ ∧ P'.c = P.c ∧
      ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t),
        ∃ (x' : (AfP p ⊗[ℚ] G.C)ˣ) (hx' : Triv G (AfP p) P'.β x' t),
          P'.toAf x' t hx' P'.self = P.toAf x t hx P.self := by
  refine ⟨conjD P y, ⟨y, 1, one_pos, ?_, rfl⟩, rfl, rfl, ?_⟩
  · rw [map_one, one_mul, conjD_β]
  · intro x t hx
    have h := triv_conj_unit (AfP p) (P.β : G.C) y x t hx
    rw [← conjD_β] at h
    refine ⟨_, h, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · show (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹) *
          Units.map (inC G (AfP p)).toMonoidHom (y * P.γ * y⁻¹) *
          (x * (Units.map (inC G (AfP p)).toMonoidHom y)⁻¹)⁻¹ =
        x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹
      simp only [map_mul, map_inv]
      group
    · rfl

theorem norm_sim (P : DPair G) :
    Algebra.norm ℚ (P.γ : G.C) * Algebra.norm ℚ (sh G P.γ) = (P.c : ℚ) ^ Module.finrank ℚ G.C := by
  have h := congrArg (Algebra.norm ℚ) P.sim
  rw [map_mul, map_mul, map_mul, Algebra.norm_algebraMap] at h
  have hb : Algebra.norm ℚ (P.β : G.C) ≠ 0 := (P.β.isUnit.map (Algebra.norm ℚ)).ne_zero
  apply mul_right_cancel₀ hb
  rw [← h]; ring

theorem c_eq_or_eq_neg (P P' : DPair G) (hγ : P'.γ = P.γ) : P'.c = P.c ∨ P'.c = -P.c := by
  have h1 := norm_sim P
  have h2 := norm_sim P'
  rw [hγ, h1] at h2
  have hN : Module.finrank ℚ G.C ≠ 0 := Module.finrank_pos.ne'
  rcases (pow_eq_pow_iff_of_ne_zero hN).1 h2.symm with h | ⟨h, _⟩
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by rw [h, Units.val_neg]))

theorem exists_ne_zero_of_term_ne_zero (P : DPair G) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) (h : P.term Kf f r K φ ≠ 0) :
    ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf),
      f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0 := by
  unfold DPair.term at h
  split_ifs at h with hd
  · unfold DPair.termAt pointSum at h
    obtain ⟨q, hq⟩ := not_forall.1 (fun hc => h (finsum_eq_zero_of_forall_eq_zero hc))
    refine ⟨_, _, P.trivAf.choose_spec.choose_spec, (Quotient.out q).1, fun h0 => hq ?_⟩
    rw [h0, zero_mul, mul_zero]
  · exact absurd rfl h

end GlobalTheory.LKDefFin

noncomputable section

namespace GlobalTheory.LKDefFin

open GlobalTheory.LKDef

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem exists_triv_toAf_eq_conj (P : DPair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) P.β x t) (g : G.GAf) : ∃ (x' : (AfP p ⊗[ℚ] G.C)ˣ) (t' : (AfP p)ˣ)
    (hx' : Triv G (AfP p) P.β x' t'), P.toAf x' t' hx' P.self = g⁻¹ * P.toAf x t hx P.self * g := by
  refine ⟨g.1.1⁻¹ * x, t * g.1.2⁻¹, ?_, ?_⟩
  · exact mul_triv_star (starT G.star (AfP p)) (inC G (AfP p) P.β) ((g.1.1⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)
      (x : AfP p ⊗[ℚ] G.C) (t : AfP p) ((g.1.2⁻¹ : (AfP p)ˣ) : AfP p) hx (mem_uGroup.1 (g⁻¹).2)
  · apply Subtype.ext
    apply Prod.ext
    · change (g.1.1⁻¹ * x) * Units.map (inC G (AfP p)).toMonoidHom P.γ * (g.1.1⁻¹ * x)⁻¹ =
        g.1.1⁻¹ * (x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹) * g.1.1
      group
    · change Units.map (algebraMap ℚ (AfP p)).toMonoidHom P.c =
        g.1.2⁻¹ * Units.map (algebraMap ℚ (AfP p)).toMonoidHom P.c * g.1.2
      rw [mul_comm g.1.2⁻¹, inv_mul_cancel_right]

theorem quot_commute_and_fixed (P Q : DPair G) (hγ : P.γ = Q.γ) (hc : P.c = Q.c) :
    ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * Q.γ = Q.γ * ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) ∧
    (Q.β : G.C) * sh G ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * ((Q.β⁻¹ : G.Cˣ) : G.C) = ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) := by
  have hmul : ∀ x y : G.C, sh G (x * y) = sh G y * sh G x := fun x y => by
    simp only [sh, map_mul, MulOpposite.unop_mul]
  have hinv : ∀ y : G.Cˣ, sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := fun y => by
    rw [← hmul, Units.inv_mul, sh_one_eq]
  have hP := P.sim
  have hQ := Q.sim
  rw [hγ, hc] at hP
  refine ⟨?_, ?_⟩
  · have e1 : ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * Q.γ * (Q.β * sh G Q.γ) = algebraMap ℚ G.C Q.c * P.β := by
      calc ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * Q.γ * (Q.β * sh G Q.γ)
          = ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * (Q.γ * Q.β * sh G Q.γ) := by simp only [mul_assoc]
        _ = algebraMap ℚ G.C Q.c * (((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * Q.β) := by
          rw [hQ]; simp only [← Algebra.smul_def, mul_smul_comm]
        _ = _ := by rw [Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
    have e2 : (Q.γ : G.C) * ((P.β * Q.β⁻¹ : G.Cˣ) : G.C) * (Q.β * sh G Q.γ) = algebraMap ℚ G.C Q.c * P.β := by
      rw [← hP, Units.val_mul]
      simp only [mul_assoc, Units.inv_mul_cancel_left]
    have e3 : (Q.β : G.C) * sh G Q.γ * (sh G ((Q.γ⁻¹ : G.Cˣ) : G.C) * ((Q.β⁻¹ : G.Cˣ) : G.C)) = 1 := by
      rw [mul_assoc, ← mul_assoc (sh G Q.γ), hinv, one_mul, Units.mul_inv]
    have e4 := congrArg (· * (sh G ((Q.γ⁻¹ : G.Cˣ) : G.C) * ((Q.β⁻¹ : G.Cˣ) : G.C))) (e1.trans e2.symm)
    rwa [mul_assoc _ (_ * sh G _), mul_assoc _ (_ * sh G _), e3, mul_one, mul_one] at e4
  · have h := hinv Q.β
    rw [Q.sym] at h
    rw [Units.val_mul, hmul, P.sym, ← mul_assoc, h, one_mul]

theorem rel_of_ratio (P Q P₁ : DPair G) (y : G.Cˣ) (s : ℚ) (hs : 0 < s)
    (hP : P.γ = P₁.γ) (hQ : Q.γ = P₁.γ) (hy : (y : G.C) * P₁.γ = P₁.γ * y)
    (ha : ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) * y = y * ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C))
    (hr : ((Q.β * P₁.β⁻¹ : G.Cˣ) : G.C) = algebraMap ℚ G.C s * ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) *
      ((y : G.C) * ((P₁.β : G.C) * sh G y * ((P₁.β⁻¹ : G.Cˣ) : G.C)))) : DPair.Rel P Q := by
  refine ⟨y, s, hs, ?_, ?_⟩
  · have h1 : ((Q.β * P₁.β⁻¹ : G.Cˣ) : G.C) * (P₁.β : G.C) = Q.β := by
      rw [← Units.val_mul, inv_mul_cancel_right]
    have h2 : ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) * (P₁.β : G.C) = P.β := by
      rw [← Units.val_mul, inv_mul_cancel_right]
    rw [← h1, hr, ← h2]
    generalize ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) = a at ha ⊢
    calc algebraMap ℚ G.C s * a * ((y : G.C) * ((P₁.β : G.C) * sh G y * ((P₁.β⁻¹ : G.Cˣ) : G.C))) * P₁.β
        = algebraMap ℚ G.C s * ((a * y) * ((P₁.β : G.C) * sh G y) *
            (((P₁.β⁻¹ : G.Cˣ) : G.C) * P₁.β)) := by simp only [mul_assoc]
      _ = _ := by rw [Units.inv_mul, mul_one, ha]; simp only [mul_assoc]
  · have hy' : y * P₁.γ = P₁.γ * y := Units.ext (by simpa using hy)
    rw [hQ, hP, hy', mul_inv_cancel_right]

theorem supp_compact (L : G.Level) (f : G.GAf → ℂ)
    (hT : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) :
    ∃ Ω : Set G.GAf, IsCompact Ω ∧ ∀ g, f g ≠ 0 → g ∈ Ω := by
  obtain ⟨-, -, -, S, hS⟩ := hT
  refine ⟨⋃ s ∈ S, (fun k : G.GAf × G.GAf => k.1 * s * k.2) '' ((L.K : Set G.GAf) ×ˢ (L.K : Set G.GAf)),
    S.isCompact_biUnion fun s _ => (L.compact.prod L.compact).image (by fun_prop), fun g hg => ?_⟩
  obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
  exact Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩

theorem finite_of_compact (Ω : Set G.GAf) (hΩ : IsCompact Ω) (γ₀ : G.Cˣ)
    (hirr : Irreducible (minpoly G.F (γ₀ : G.C))) (c₀ : ℚˣ) :
    {q : DCls G | ∃ P : DPair G, (Quot.mk DPair.Rel P : DCls G) = q ∧ P.γ = γ₀ ∧ P.c = c₀ ∧
      ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.toAf x t hx P.self ∈ Ω}.Finite := by
  set Y : Set (DPair G) := {P | P.γ = γ₀ ∧ P.c = c₀ ∧
      ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.toAf x t hx P.self ∈ Ω} with hYdef
  have hset : {q : DCls G | ∃ P : DPair G, (Quot.mk DPair.Rel P : DCls G) = q ∧ P.γ = γ₀ ∧ P.c = c₀ ∧
      ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.toAf x t hx P.self ∈ Ω} =
      Quot.mk DPair.Rel '' Y := by
    ext q; constructor
    · rintro ⟨P, rfl, h⟩; exact ⟨P, h, rfl⟩
    · rintro ⟨P, h, rfl⟩; exact ⟨P, rfl, h⟩
  rw [hset]
  rcases Y.eq_empty_or_nonempty with hY | ⟨P₁, hP₁⟩
  · rw [hY, Set.image_empty]; exact Set.finite_empty
  have hirr₁ : Irreducible (minpoly G.F (P₁.γ : G.C)) := by rw [hP₁.1]; exact hirr
  obtain ⟨L, _, _, ι, c, hinj, hcent, hc, hcc⟩ :=
    GlobalTheory.T.exists_numberField_involution_similitudeCentralizer p G P₁.β P₁.γ P₁.c P₁.sym P₁.sim hirr₁ P₁.reg.1
  obtain ⟨S, hloc⟩ := GlobalTheory.T.definitePairs_ratio_locally_rational_times_norm p G Ω hΩ P₁ L ι c hinj hcent hc
  have hγ : ∀ P ∈ Y, P.γ = P₁.γ := fun P hP => hP.1.trans hP₁.1.symm
  have hcc' : ∀ P ∈ Y, P.c = P₁.c := fun P hP => hP.2.1.trans hP₁.2.1.symm
  have ha : ∀ P ∈ Y, ∃ a : L, ι a = ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) := fun P hP =>
    (hcent _).1 (quot_commute_and_fixed P P₁ (hγ P hP) (hcc' P hP)).1
  set X : Set L := {a | ∃ P ∈ Y, ι a = ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C)} with hXdef
  obtain ⟨R, hR⟩ := GlobalTheory.FixedNormCls.finite_classes_mod_rat_norms L c hcc S X (by
    rintro a ⟨P, hP, hPa⟩
    refine ⟨fun h0 => ?_, hinj ?_, fun v hv => hloc P (hγ P hP) (hcc' P hP) hP.2.2 a hPa v hv⟩
    · rw [h0, map_zero] at hPa
      exact (P.β * P₁.β⁻¹).ne_zero hPa.symm
    · rw [hc, hPa]; exact (quot_commute_and_fixed P P₁ (hγ P hP) (hcc' P hP)).2)
  let good : L → Prop → DPair G → Prop := fun b s P => P ∈ Y ∧ ∃ (a : L) (q : ℚ) (z : L),
    ι a = ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) ∧ (0 < q ↔ s) ∧ q ≠ 0 ∧ z ≠ 0 ∧ a = algebraMap ℚ L q * b * (z * c z)
  let rep : L × Bool → DPair G := fun bs => if h : ∃ P, good bs.1 (bs.2 = true) P then h.choose else P₁
  refine ((R ×ˢ (Finset.univ : Finset Bool) : Finset (L × Bool)).finite_toSet.image
    (fun bs => Quot.mk DPair.Rel (rep bs))).subset ?_
  rintro _ ⟨P, hP, rfl⟩
  obtain ⟨a, hPa⟩ := ha P hP
  obtain ⟨b, hb, q, z, hq, hz, hab⟩ := hR a ⟨P, hP, hPa⟩
  have hex : ∃ P', good b (decide (0 < q) = true) P' := ⟨P, hP, a, q, z, hPa, decide_eq_true_iff.symm, hq, hz, hab⟩
  refine ⟨(b, decide (0 < q)), Finset.mem_coe.2 (Finset.mem_product.2 ⟨hb, Finset.mem_univ _⟩), ?_⟩
  have hrep : rep (b, decide (0 < q)) = hex.choose := dif_pos hex
  obtain ⟨hP', a', q', z', hPa', hsgn, hq', hz', hab'⟩ := hex.choose_spec
  simp only [hrep]
  apply Quot.sound
  set P' := hex.choose
  have hpos : 0 < q / q' := by
    have hs : (0 < q' ↔ 0 < q) := by simpa using hsgn
    rcases lt_or_gt_of_ne hq with h | h
    · exact div_pos_of_neg_of_neg h (lt_of_le_of_ne (not_lt.1 (fun h' => absurd (hs.1 h') (not_lt.2 h.le))) hq')
    · exact div_pos h (hs.2 h)
  set w : L := z / z' with hw
  have hw0 : w ≠ 0 := div_ne_zero hz hz'
  let y : G.Cˣ := Units.map ι.toMonoidHom (Units.mk0 w hw0)
  have hy : (y : G.C) = ι w := rfl
  have hrat : a = algebraMap ℚ L (q / q') * a' * (w * c w) := by
    rw [hab, hab', hw, map_div₀, map_div₀]
    have hcz' : c z' ≠ 0 := by
      intro h; apply hz'; have := congrArg c h; rwa [hcc, map_zero] at this
    have hq'' : algebraMap ℚ L q' ≠ 0 := (map_ne_zero _).2 hq'
    field_simp
  apply rel_of_ratio P' P P₁ y (q / q') hpos (hγ P' hP') (hγ P hP)
  · rw [hy]; exact ((hcent _).2 ⟨w, rfl⟩)
  · rw [hy, ← hPa', ← map_mul, ← map_mul, mul_comm]
  · rw [← hPa, hrat, hy, ← hPa', ← hc, map_mul, map_mul, map_mul, AlgHom.commutes]

theorem finite_classes_fixed_gamma (L : G.Level) (f : G.GAf → ℂ)
    (hT : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) (γ₀ : G.Cˣ)
    (hirr : Irreducible (minpoly G.F (γ₀ : G.C))) (c₀ : ℚˣ) :
    {q : DCls G | ∃ P : DPair G, (Quot.mk DPair.Rel P : DCls G) = q ∧ P.γ = γ₀ ∧ P.c = c₀ ∧
      ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf),
        f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0}.Finite := by
  obtain ⟨Ω, hΩ, hf⟩ := supp_compact L f hT
  refine (finite_of_compact Ω hΩ γ₀ hirr c₀).subset ?_
  rintro q ⟨P, rfl, hγ, hc, x, t, hx, g, hne⟩
  obtain ⟨x', t', hx', he⟩ := exists_triv_toAf_eq_conj P x t hx g
  exact ⟨P, rfl, hγ, hc, x', t', hx', he ▸ hf _ hne⟩

end GlobalTheory.LKDefFin

open GlobalTheory.LKDef GlobalTheory.LKDefFin in

theorem GlobalTheory.LKDefFin.finite_classes_of_pol : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      ∀ P0 : Polynomial G.F, {q : GlobalTheory.LKDef.DCls G | (Quot.out q).pol = P0 ∧ Irreducible (Quot.out q).pol ∧
        (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  intro p _ G _ L f hf _ K' f' _ _ P0
  by_cases hne : {q : DCls G | (Quot.out q).pol = P0 ∧ Irreducible (Quot.out q).pol ∧
      (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Nonempty
  · obtain ⟨q₀, hq₀⟩ := hne
    have hirr₀ : Irreducible (minpoly G.F ((Quot.out q₀).γ : G.C)) := hq₀.2.1
    refine ((finite_classes_fixed_gamma L f hf (Quot.out q₀).γ hirr₀ (Quot.out q₀).c).union
      (finite_classes_fixed_gamma L f hf (Quot.out q₀).γ hirr₀ (-(Quot.out q₀).c))).subset ?_
    intro q hq
    obtain ⟨x, t, hx, g, hg⟩ := exists_ne_zero_of_term_ne_zero _ _ _ _ _ _ hq.2.2
    have hpol : minpoly G.F ((Quot.out q₀).γ : G.C) = minpoly G.F ((Quot.out q).γ : G.C) :=
      hq₀.1.trans hq.1.symm
    have hirrq : Irreducible (minpoly G.F ((Quot.out q).γ : G.C)) := hq.2.1
    obtain ⟨y, hy⟩ := GlobalTheory.LKCx.units_conj_of_minpoly_eq_of_irreducible p G (Quot.out q₀).γ (Quot.out q).γ hpol hirrq
    obtain ⟨P', hrel, hγ, hc', htr⟩ := exists_conj (Quot.out q) y
    obtain ⟨x', hx', he⟩ := htr x t hx
    have hq' : (Quot.mk DPair.Rel P' : DCls G) = q := by
      rw [← Quot.sound hrel]; exact Quot.out_eq q
    have hγ' : P'.γ = (Quot.out q₀).γ := by
      rw [hγ]; apply Units.ext; rw [hy]; simp
    have hg' : f (g⁻¹ * P'.toAf x' t hx' P'.self * g) ≠ 0 := by rw [he]; exact hg
    rcases c_eq_or_eq_neg (Quot.out q₀) P' hγ' with hc | hc
    · exact Or.inl ⟨P', hq', hγ', hc, x', t, hx', g, hg'⟩
    · exact Or.inr ⟨P', hq', hγ', hc, x', t, hx', g, hg'⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]; exact Set.finite_empty
end
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_definitePair_classes_fixed_minpoly_degree_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      ∀ P0 : Polynomial G.F, {q : GlobalTheory.LKDef.DCls G | (Quot.out q).pol = P0 ∧ Irreducible (Quot.out q).pol ∧
        (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  first | (exact @GlobalTheory.LKDefFin.finite_classes_of_pol) | (exact GlobalTheory.LKDefFin.finite_classes_of_pol) | (intros; apply GlobalTheory.LKDefFin.finite_classes_of_pol <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef.FinPairs

theorem finite_classes_irr_term_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      {q : GlobalTheory.LKDef.DCls G | Irreducible (Quot.out q).pol ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  intro p _ G ha L f hf hfb K' f' hf' hfb'
  refine ((GlobalTheory.T.finite_minpoly_definitePairs_term_ne_zero p G ha L f hf hfb K' f' hf' hfb').biUnion
    (fun P0 _ => GlobalTheory.T.finite_definitePair_classes_fixed_minpoly_degree_one p G ha L f hf hfb K' f' hf' hfb' P0)).subset ?_
  intro q hq
  exact Set.mem_biUnion (x := (Quot.out q).pol) ⟨Quot.out q, rfl, hq.1, hq.2⟩ ⟨rfl, hq.1, hq.2⟩

end GlobalTheory.LKDef.FinPairs
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.bi_invariant_conjugacy_classes_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      {q : GlobalTheory.LKDef.DCls G | Irreducible (Quot.out q).pol ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  first | exact @GlobalTheory.LKDef.FinPairs.finite_classes_irr_term_ne_zero | exact GlobalTheory.LKDef.FinPairs.finite_classes_irr_term_ne_zero
end

section
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef.TermPair

theorem finsum_dc_translate {H : Type} [Group H] (A B K : Subgroup H) (u : H)
    (hAB : B = A.map (MulAut.conj u).toMonoidHom) (S₁ S₂ : H → ℂ)
    (hS₂ : ∀ b ∈ B, ∀ k ∈ K, ∀ h, S₂ (b * h * k) = S₂ h) (h12 : ∀ h, S₁ h = S₂ (u * h)) :
    ∑ᶠ q : DoubleCoset.Quotient (A : Set H) (K : Set H), S₁ (Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient (B : Set H) (K : Set H), S₂ (Quotient.out q) := by
  have memB : ∀ a, a ∈ A → u * a * u⁻¹ ∈ B := fun a ha => by
    rw [hAB]; exact ⟨a, ha, by simp [MulAut.conj_apply]⟩
  have memA : ∀ b, b ∈ B → u⁻¹ * b * u ∈ A := fun b hb => by
    rw [hAB] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    simpa [MulAut.conj_apply, mul_assoc] using ha
  let e : DoubleCoset.Quotient (A : Set H) (K : Set H) ≃ DoubleCoset.Quotient (B : Set H) (K : Set H) :=
    { toFun := Quotient.map' (u * ·) (fun x y hxy => by
        obtain ⟨a, ha, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hxy
        exact DoubleCoset.rel_iff.2 ⟨u * a * u⁻¹, memB a ha, k, hk, by group⟩)
      invFun := Quotient.map' (u⁻¹ * ·) (fun x y hxy => by
        obtain ⟨b, hb, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hxy
        exact DoubleCoset.rel_iff.2 ⟨u⁻¹ * b * u, memA b hb, k, hk, by group⟩)
      left_inv := fun q => by
        induction q using Quotient.inductionOn' with
        | h x =>
          simp only [Quotient.map'_mk'', inv_mul_cancel_left, mul_inv_cancel_left]
          rfl
      right_inv := fun q => by
        induction q using Quotient.inductionOn' with
        | h x =>
          simp only [Quotient.map'_mk'', inv_mul_cancel_left, mul_inv_cancel_left]
          rfl }
  have hF : ∀ x y : H, DoubleCoset.mk B K x = DoubleCoset.mk B K y → S₂ x = S₂ y := fun x y hxy => by
    obtain ⟨b, hb, k, hk, rfl⟩ := (DoubleCoset.eq B K x y).1 hxy
    exact (hS₂ b hb k hk x).symm
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  rw [h12]
  apply hF
  rw [DoubleCoset.out_eq']
  conv_rhs => rw [← DoubleCoset.out_eq' A K q]
  rfl

theorem card_eq_of_conj {Γ : Type} [Group Γ] (S T : Subgroup Γ) (v : Γ) (h : ∀ w, w ∈ T ↔ v⁻¹ * w * v ∈ S) :
    Nat.card T = Nat.card S :=
  Nat.card_congr
    { toFun := fun w => ⟨v⁻¹ * w * v, (h w).1 w.2⟩
      invFun := fun w => ⟨v * w * v⁻¹, (h _).2 (by simpa [mul_assoc] using w.2)⟩
      left_inv := fun w => by ext; simp [mul_assoc]
      right_inv := fun w => by ext; simp [mul_assoc] }

end GlobalTheory.LKDef.TermPair

namespace GlobalTheory.LKDef.TermPair

theorem mem_map_conj {H : Type} [Group H] (K : Subgroup H) (a x : H) :
    x ∈ K.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ K := by
  rw [Subgroup.mem_map_equiv]; simp [MulAut.conj_symm_apply]

theorem conj_mem_iff {H : Type} [Group H] (K : Subgroup H) (a h k y : H) (hk : k ∈ K) :
    (a * h * k)⁻¹ * y * (a * h * k) ∈ K ↔ h⁻¹ * (a⁻¹ * y * a) * h ∈ K := by
  have e : (a * h * k)⁻¹ * y * (a * h * k) = k⁻¹ * (h⁻¹ * (a⁻¹ * y * a) * h) * k := by group
  rw [e, K.mul_mem_cancel_right hk, K.mul_mem_cancel_left (K.inv_mem hk)]

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem cent_le_grp (P : DPair G) : P.cent ≤ GlobalTheory.LKCx.grp G P.β := fun y hy =>
  ⟨hy.2, DFormPos.sim_pos p G (DForm.ofDPair P) y.1 y.2 hy.2⟩

theorem centralizer_eq (P : DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β) :
    Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} =
      (Subgroup.inclusion (cent_le_grp P)).range := by
  ext v
  rw [Subgroup.mem_centralizer_singleton_iff, MonoidHom.mem_range]
  constructor
  · intro h
    have h' := congrArg (fun w : GlobalTheory.LKCx.grp G P.β => (w : G.Cˣ × ℚˣ).1) h
    simp only [Subgroup.coe_mul, Prod.fst_mul] at h'
    exact ⟨⟨v, h', v.2.1⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    apply Subtype.ext
    exact Prod.ext w.2.1 (mul_comm _ _)

end GlobalTheory.LKDef.TermPair

namespace GlobalTheory.LKDef.TermPair
variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem termAt_eq (P : DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ)
    (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ)
    (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (δ z : Gr G 1)
    (hδ : IsNrm G 1 P.atP δ z) :
    P.termAt Kf f 1 K' f' x t hx δ z =
      centSum (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) Kf K' 1 f f'
        ⟨(P.γ, P.c), hm⟩ := by
  have hδ' : δ = z⁻¹ * inclG G 1 P.atP * z := by simpa [IsNrm, nrmG] using hδ
  have hle := cent_le_grp P
  have e1 : ∀ w, GlobalTheory.LKCx.toAfF G P.β x t hx (Subgroup.inclusion hle w) = P.toAf x t hx w := fun w => rfl
  have e2 : ∀ w, P.toQr 1 z w = z⁻¹ * GlobalTheory.LKCx.toP1 G P.β (Subgroup.inclusion hle w) * z := fun w => by
    simp [DPair.toQr, GlobalTheory.LKCx.toP1, carry, MulAut.conj_apply]
  have eg : Subgroup.inclusion hle P.self = ⟨(P.γ, P.c), hm⟩ := rfl
  have hj2g : GlobalTheory.LKCx.toP1 G P.β ⟨(P.γ, P.c), hm⟩ = inclG G 1 P.atP := rfl
  have hC := centralizer_eq P hm
  unfold DPair.termAt pointSum centSum
  refine finsum_dc_translate ((P.toAf x t hx).prod (P.toQr 1 z)).range
    ((Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)}).map
      ((GlobalTheory.LKCx.toAfF G P.β x t hx).prod (GlobalTheory.LKCx.toP1 G P.β))) (Kf.prod K') ((1 : G.GAf), z) ?_
    (fun h => ((Nat.card (stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h) : ℕ) : ℂ)⁻¹ *
      (f (h.1⁻¹ * (P.toAf x t hx) P.self * h.1) * f' (h.2⁻¹ * δ * (sigG G 1) h.2)))
    (fun h => ((Nat.card (stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' h ⊓
      Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} : Subgroup _) : ℕ) : ℂ)⁻¹ *
      term (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) 1 f f' h
        ⟨(P.γ, P.c), hm⟩) ?_ ?_
  · rw [hC, MonoidHom.map_range, MonoidHom.map_range]
    refine congrArg MonoidHom.range (MonoidHom.ext fun w => ?_)
    refine Prod.ext ?_ ?_
    · simp [MulAut.conj_apply, e1]
    · simp [MulAut.conj_apply, e2]
      group
  · rintro b hb k hk h
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hb
    obtain ⟨hk1, hk2⟩ := Subgroup.mem_prod.1 hk
    have hvc : v * (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) = (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * v := Subgroup.mem_centralizer_singleton_iff.1 hv
    have hvg : v⁻¹ * (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * v = (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) := by
      rw [mul_assoc, ← hvc, inv_mul_cancel_left]
    have hcard : Nat.card (stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((GlobalTheory.LKCx.toAfF G P.β x t hx).prod (GlobalTheory.LKCx.toP1 G P.β)) v * h * k) ⊓
        Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} : Subgroup _) =
        Nat.card (stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' h ⊓ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} : Subgroup _) := by
      refine card_eq_of_conj _ _ v fun w => ?_
      simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, mem_map_conj, MonoidHom.prod_apply, Prod.fst_mul,
        Prod.snd_mul]
      rw [conj_mem_iff _ _ _ _ _ hk1, conj_mem_iff _ _ _ _ _ hk2, map_mul, map_mul, map_mul, map_mul, map_inv,
        map_inv]
      have hCv : w ∈ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} ↔ v⁻¹ * w * v ∈ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} := by
        rw [Subgroup.mul_mem_cancel_right _ hv, Subgroup.mul_mem_cancel_left _ (Subgroup.inv_mem _ hv)]
      rw [hCv]
    have ef : ∀ a y : G.GAf, f ((a * h.1 * k.1)⁻¹ * y * (a * h.1 * k.1)) = f (h.1⁻¹ * (a⁻¹ * y * a) * h.1) :=
      fun a y => by
        rw [← hf k.1 hk1 (h.1⁻¹ * (a⁻¹ * y * a) * h.1)]; congr 1; group
    have ef' : ∀ a y : Gr G 1, f' ((a * h.2 * k.2)⁻¹ * y * (a * h.2 * k.2)) =
        f' (h.2⁻¹ * (a⁻¹ * y * a) * h.2) := fun a y => by
      rw [← hf' k.2 hk2 (h.2⁻¹ * (a⁻¹ * y * a) * h.2)]; congr 1; group
    have g1 : ((GlobalTheory.LKCx.toAfF G P.β x t hx) v)⁻¹ * (GlobalTheory.LKCx.toAfF G P.β x t hx) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * (GlobalTheory.LKCx.toAfF G P.β x t hx) v = (GlobalTheory.LKCx.toAfF G P.β x t hx) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) := by
      rw [← map_inv, ← map_mul, ← map_mul, hvg]
    have g2 : ((GlobalTheory.LKCx.toP1 G P.β) v)⁻¹ * ((GlobalTheory.LKCx.toP1 G P.β) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * 1) * (GlobalTheory.LKCx.toP1 G P.β) v = (GlobalTheory.LKCx.toP1 G P.β) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * 1 := by
      rw [mul_one, ← map_inv, ← map_mul, ← map_mul, hvg]
    beta_reduce
    rw [hcard]
    simp only [term, MonoidHom.prod_apply, Prod.fst_mul, Prod.snd_mul, MonoidHom.id_apply]
    rw [ef, ef', g1, g2]
  · intro h
    have hmem : ∀ w, Subgroup.inclusion hle w ∈ stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((1 : G.GAf), z) * h) ↔
        w ∈ stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h := fun w => by
      simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, mem_map_conj, Prod.fst_mul, Prod.snd_mul, one_mul, e1, e2]
      have e3 : (z * h.2)⁻¹ * (GlobalTheory.LKCx.toP1 G P.β) (Subgroup.inclusion hle w) * (z * h.2) =
          h.2⁻¹ * (z⁻¹ * (GlobalTheory.LKCx.toP1 G P.β) (Subgroup.inclusion hle w) * z) * h.2 := by group
      rw [e3]
    have hsub : stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((1 : G.GAf), z) * h) ⊓ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} =
        (stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h).map (Subgroup.inclusion hle) := by
      rw [hC]
      ext v
      simp only [Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map]
      constructor
      · rintro ⟨hv, w, rfl⟩
        exact ⟨w, (hmem w).1 hv, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨(hmem w).2 hw, w, rfl⟩
    have hcard : Nat.card (stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((1 : G.GAf), z) * h) ⊓ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} :
        Subgroup _) = Nat.card (stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h) := by
      rw [hsub]; exact Subgroup.card_map_of_injective (Subgroup.inclusion_injective hle)
    beta_reduce
    rw [hcard]
    simp only [term, Prod.fst_mul, Prod.snd_mul, MonoidHom.id_apply, one_mul, mul_one, GlobalTheory.LKCx.sigG_one]
    rw [← e1 P.self, eg, hδ', ← hj2g]
    congr 3
    group

end GlobalTheory.LKDef.TermPair

namespace GlobalTheory.LKDef.TermPair

theorem term_eq_centSum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : GlobalTheory.LKDef.DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      P.term L.K.toSubgroup f 1 K' f' =
        centSum (GlobalTheory.LKCx.toAfF G P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec)
          (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' ⟨(P.γ, P.c), hm⟩ := by
  intro p _ G P hm L f hf K' f' hf'
  have hex : ∃ dz : Gr G 1 × Gr G 1, IsNrm G 1 P.atP dz.1 dz.2 :=
    ⟨(inclG G 1 P.atP, 1), by simp [IsNrm, nrmG]⟩
  unfold DPair.term
  rw [dif_pos hex]
  exact termAt_eq P hm _ f (fun k hk g => by simpa using hf.2.2.1 k hk g) K' f'
    (fun k hk g => by simpa [GlobalTheory.LKCx.sigG_one] using hf'.2.2.1 k hk g) _ _ _ _ _ hex.choose_spec

end GlobalTheory.LKDef.TermPair
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definitePair_term_eq_centraliser_orbit_sum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : GlobalTheory.LKDef.DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      P.term L.K.toSubgroup f 1 K' f' =
        centSum (GlobalTheory.LKCx.toAfF G P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec)
          (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' ⟨(P.γ, P.c), hm⟩ := by
  atlas_forward_decl GlobalTheory.LKDef.TermPair.term_eq_centSum
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem GlobalTheory.LKDef.Regroup.regroup :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (wt : Polynomial G.F → ℂ)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      GlobalTheory.LKDef.dSumIrr G wt L.K.toSubgroup f 1 K' f' =
        ∑ᶠ q : GlobalTheory.LKDef.DFCls G, ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β),
          if GlobalTheory.LKDef.RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) then
            wt (minpoly G.F (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C)) *
              centSum (GlobalTheory.LKCx.toAfF G (Quot.out q).β (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
                  (Quot.out q).trivAf.choose_spec.choose_spec)
                (GlobalTheory.LKCx.toP1 G (Quot.out q).β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' (Quotient.out c)
          else 0 :=
  GlobalTheory.LKDef.Regroup.regroup_main GlobalTheory.LKDef.DFormPos.sim_pos GlobalTheory.T.bi_invariant_conjugacy_classes_finite GlobalTheory.T.definitePair_term_eq_centraliser_orbit_sum
end
