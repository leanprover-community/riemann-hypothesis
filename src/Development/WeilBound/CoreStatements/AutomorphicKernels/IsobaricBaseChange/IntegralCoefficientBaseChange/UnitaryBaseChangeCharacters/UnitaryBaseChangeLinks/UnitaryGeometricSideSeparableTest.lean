import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralUnitIndicatorEventuallyOneClassStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.UnitaryConjugacySignProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaSignMultiplicative
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.UnitaryMassFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariantStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.EllipticCharpolySelfReciprocal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.LocalTwistContinuousInvolutionIntegralProperties
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CocycleMultiplicative
import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.MemMaxVAIff
import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.WittFN
import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.WittHS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthonormalBasisUnimodularHermitianLocalRi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixCharpolyPreservingHermitianFormCM
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.IntegralConjugacyAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicUnitRootsBoundedDenominatorNumberFiel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIntegerDenominatorOfValuationBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyCoeffDetInvValuationBoundedOfIsCompactGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemSectionConj

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.kappa_sign_multiplicative : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (w : Pl E) (Q₁ Q₂ Q₃ : (w.adicCompletion E)[X]) (γ g : UL n w), γ.1.val.charpoly.Separable → Q₁ * Q₂ ∣ γ.1.val.charpoly → IsCoprime Q₁ Q₂ → IsCsr w Q₁ → IsCsr w Q₂ → kapSign n w (Q₁ * Q₂) γ.1 = kapSign n w Q₁ γ.1 * kapSign n w Q₂ γ.1 ∧ kapSign n w Q₃ (g⁻¹ * γ * g).1 = kapSign n w Q₃ γ.1 ∧ (kapSign n w Q₃ γ.1 = 1 ∨ kapSign n w Q₃ γ.1 = -1) := by
  first | exact @GlobalTheory.KapSignMul.main | (intros; apply GlobalTheory.KapSignMul.main <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
theorem _root_.GlobalTheory.T.finite_twisted_classes_charpoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (Q : (w.adicCompletion E)[X]), Q.Separable → {c : TwCl (thL n w) | (nrmL n w c.rep).val.charpoly = Q}.Finite ∧ {c : TwCl (MonoidHom.id (UL n w)) | c.rep.1.val.charpoly = Q}.Finite := by
  first | exact @GlobalTheory.BCT.ClsFin.classes_finite | (intros; apply GlobalTheory.BCT.ClsFin.classes_finite <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocRatPt

open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem map_mem_UL (hU : Unr E) (w : Pl E) (γ : UE E n) :
    GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ UL n w := by
  unfold UL
  split_ifs with hs
  · exact Subgroup.mem_top _
  · have hc := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs).1
    have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E) * 1 *
        (γ.1 : Matrix (Fin n) (Fin n) E) = 1 := γ.2
    change cT (cj w) ((γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E))) * 1 *
      (γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E)) = 1
    have key : cT (cj w) ((γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E))) =
        (cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E)).map
          (algebraMap E (w.adicCompletion E)) := by
      exact Matrix.ext fun i j => hc _
    rw [key, Matrix.mul_one, ← Matrix.map_mul]
    rw [Matrix.mul_one] at hγ
    rw [hγ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem locPt_val (hU : Unr E) (w : Pl E) (γ : UE E n) :
    (locPt w γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
  rw [locPt, toSub, dif_pos (map_mem_UL hU w γ)]

theorem eventually_valuation_le_one (x : E) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), w.valuation E x ≤ 1 := by
  rw [Filter.eventually_cofinite]
  refine (HeightOneSpectrum.Support.finite (𝓞 E) x).subset fun w hw => ?_
  exact lt_of_not_ge hw

theorem algebraMap_mem_Ov {w : Pl E} {x : E} (h : w.valuation E x ≤ 1) :
    algebraMap E (w.adicCompletion E) x ∈ Ov E w := by
  rw [ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [show Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x from
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x]
  exact h

theorem mem_GLint_of_entries {K : Type} [Field K] {O : Subring K} {x : GL (Fin n) K} (h1 : ∀ i j, x.1 i j ∈ O)
    (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) : x ∈ GLint (Fin n) O := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem eventually_mem_KL (hU : Unr E) (γ : UE E n) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), locPt w γ ∈ KL n w := by
  have h1 : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, w.valuation E ((γ.1 : GL (Fin n) E).1 i j) ≤ 1 ∧
      w.valuation E (((γ.1 : GL (Fin n) E)⁻¹).1 i j) ≤ 1 := by
    simp only [Filter.eventually_all]
    intro i j
    exact (eventually_valuation_le_one _).and (eventually_valuation_le_one _)
  filter_upwards [h1] with w hw
  rw [KL, Subgroup.mem_subgroupOf, locPt_val hU]
  refine mem_GLint_of_entries (fun i j => algebraMap_mem_Ov (hw i j).1) (fun i j => ?_)
  rw [← map_inv]
  exact algebraMap_mem_Ov (hw i j).2

theorem norm_eq_one_of_root (γ : UE E n) (τ : E →+* ℂ) (z : ℂ)
    (hz : z ∈ ((γ.1 : GL (Fin n) E).val.charpoly.map τ).roots) : ‖z‖ = 1 :=
  _root_.UpperTheory.Reformulated.B.CocycleMultiplicative.norm_eq_one_of_root γ τ z hz

theorem charpoly_mem_Ell (γ : UE E n) (hs : (γ.1 : GL (Fin n) E).val.charpoly.Separable) :
    (γ.1 : GL (Fin n) E).val.charpoly ∈ Ell E n :=
  ⟨Matrix.charpoly_monic _, by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin], hs,
    fun τ z hz => norm_eq_one_of_root γ τ z hz⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ : UE E n), (∀ w : Pl E, (locPt w γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1) ∧ (∀ᶠ w in (cofinite : Filter (Pl E)), locPt w γ ∈ KL n w) ∧ (γ.1.val.charpoly.Separable → γ.1.val.charpoly ∈ Ell E n) := by
  intro E _ _ _ hU n γ
  exact ⟨fun w => locPt_val hU w γ, eventually_mem_KL hU γ, charpoly_mem_Ell γ⟩

end GlobalTheory.LocRatPt
end
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_points_integral_almost_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ : UE E n), (∀ w : Pl E, (locPt w γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1) ∧ (∀ᶠ w in (cofinite : Filter (Pl E)), locPt w γ ∈ KL n w) ∧ (γ.1.val.charpoly.Separable → γ.1.val.charpoly ∈ Ell E n) := by
  first | exact @GlobalTheory.LocRatPt.main | exact GlobalTheory.LocRatPt.main | (intros; apply GlobalTheory.LocRatPt.main <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.IntUnitaryPoly

theorem lemGlobal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    ∃ C H : Matrix (Fin n) (Fin n) E, C.charpoly = P ∧ C.det ≠ 0 ∧ H.det ≠ 0 ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom C * H * C = H := GlobalTheory.T.exists_matrix_charpoly_preserving_hermitian_form_CM

theorem lemLocal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → Odd q → ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) L), (∀ i j, H i j ∈ intL L) →
      Valued.v H.det = 1 → cT σ H = H →
      ∃ R ∈ GLint (Fin n) (intL L), cT σ ((R : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * H * ((R : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
  intro L _ _ _ ϖ σ q hU hq n H hint hdet hH
  have hv := hU.2.1
  set O := Formalism.IndefR.LocBrg.VA L
  set s := Formalism.IndefR.LocBrg.sigA σ hv
  have hs : ∀ x, s (s x) = x := Formalism.IndefR.LocBrg.sigA_inv σ hv hU.1
  have h2 : IsUnit (2 : O) := Formalism.IndefR.LocBrg.two_unit_VA hU hq
  have hτ : ∃ τ : O, τ + s τ = 1 := by
    obtain ⟨u, hu⟩ := h2
    refine ⟨((u⁻¹ : Oˣ) : O), ?_⟩
    have hs2 : s 2 = 2 := map_ofNat s 2
    have hfix : s ((u⁻¹ : Oˣ) : O) = ((u⁻¹ : Oˣ) : O) := by
      have e : s ((u⁻¹ : Oˣ) : O) * 2 = 1 := by rw [← hs2, ← map_mul, ← hu, Units.inv_mul, map_one]
      calc s ((u⁻¹ : Oˣ) : O) = s ((u⁻¹ : Oˣ) : O) * (2 * ((u⁻¹ : Oˣ) : O)) := by rw [← hu, Units.mul_inv, mul_one]
        _ = ((u⁻¹ : Oˣ) : O) := by rw [← mul_assoc, e, one_mul]
    rw [hfix, ← two_mul, ← hu, Units.mul_inv]
  have hn : ∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u := fun u hu hsu =>
    Formalism.IndefR.LocBrg.normSurj Formalism.IndefR.LocBrg.finNormSurj Formalism.IndefR.LocBrg.henselSqrt hU hq u hsu hu
  set Q : Matrix (Fin n) (Fin n) O := fun i j =>
    ⟨H i j, Formalism.IndefR.LocBrg.mem_VA.2 (Formalism.IndefR.LocBrg.mem_intL.1 (hint i j))⟩ with hQdef
  have hmap : Q.map O.subtype = H := by ext i j; rfl
  have hQ : cT s Q = Q := by
    ext i j; exact congrFun (congrFun hH i) j
  have hQu : IsUnit Q := by
    rw [Matrix.isUnit_iff_isUnit_det, Formalism.IndefR.LocBrg.isUnit_VA_iff]
    have e : ((Q.det : O) : L) = H.det := by rw [← hmap]; exact RingHom.map_det O.subtype Q
    rw [e]; exact hdet
  obtain ⟨a, ha⟩ := GlobalTheory.Core.Rk.Exh.exists_orthonormal_of_isLocalRing O s hs hτ hn n Q hQ hQu
  let ι : O →+* intL L := O.subtype.codRestrict (intL L)
    (fun x => Formalism.IndefR.LocBrg.mem_intL.2 (Formalism.IndefR.LocBrg.mem_VA.1 x.2))
  refine ⟨bc (n := Fin n) (intL L).subtype (bc (n := Fin n) ι a), ⟨_, rfl⟩, ?_⟩
  have hR : ((bc (n := Fin n) (intL L).subtype (bc (n := Fin n) ι a) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      (a : Matrix (Fin n) (Fin n) O).map O.subtype := by ext i j; rfl
  rw [hR, ← hmap]
  have hc : cT σ ((a : Matrix (Fin n) (Fin n) O).map O.subtype) = (cT s (a : Matrix (Fin n) (Fin n) O)).map O.subtype := by
    ext i j; rfl
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, ha, Matrix.map_one _ (map_zero _) (map_one _)]

theorem lemOdd : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → Valued.v (2 : L) = 1 → Odd q := by
  intro L _ _ ϖ σ q hU h2
  set V := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hcard : Nat.card (IsLocalRing.ResidueField V) = q ^ 2 := hU.2.2.2.2.2.2
  have hq0 : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  haveI : Finite (IsLocalRing.ResidueField V) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hq0)
  have h20 : (2 : L) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
  have hu : IsUnit (2 : V) := by
    have hmem : (2 : L)⁻¹ ∈ V := (Valuation.mem_valuationSubring_iff _ _).2 (by rw [map_inv₀, h2, inv_one])
    have hmul : (2 : V) * ⟨(2 : L)⁻¹, hmem⟩ = 1 := by
      apply Subtype.ext
      first
        | exact mul_inv_cancel₀ h20
        | (show (2 : L) * (2 : L)⁻¹ = 1; exact mul_inv_cancel₀ h20)
        | (push_cast; exact mul_inv_cancel₀ h20)
    exact ⟨⟨2, _, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
  have h2V : (2 : IsLocalRing.ResidueField V) ≠ 0 := by
    intro h
    have hm : (2 : V) ∈ IsLocalRing.maximalIdeal V := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_ofNat]; exact h
    exact (IsLocalRing.mem_maximalIdeal _).1 hm hu
  by_contra hodd
  have heven : Even q := Nat.not_odd_iff_even.1 hodd
  have hdvd : 2 ∣ Nat.card (IsLocalRing.ResidueField V) := by
    rw [hcard]; exact dvd_pow (even_iff_two_dvd.1 heven) two_ne_zero
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' 2 hdvd
  have hx0 : x ≠ 0 := by intro h; rw [h, addOrderOf_zero] at hx; norm_num at hx
  have hmul : (2 : IsLocalRing.ResidueField V) * x = 0 := by
    rw [two_mul, ← two_nsmul, ← hx, addOrderOf_nsmul_eq_zero]
  exact h2V ((mul_eq_zero.1 hmul).resolve_right hx0)

theorem val_alg {E : Type} [Field E] [NumberField E] (w : Pl E) (x : E) :
    Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

theorem ae_int {E : Type} [Field E] [NumberField E] (x : E) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), Valued.v (algebraMap E (w.adicCompletion E) x) ≤ 1 := by
  filter_upwards [(HeightOneSpectrum.Support.finite (𝓞 E) (K := E) x).eventually_cofinite_notMem] with w hw
  have hw' : ¬ 1 < w.valuation E x := hw
  rw [val_alg]
  exact not_lt.1 hw'

theorem ae_unit {E : Type} [Field E] [NumberField E] {x : E} (hx : x ≠ 0) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), Valued.v (algebraMap E (w.adicCompletion E) x) = 1 := by
  filter_upwards [ae_int x, ae_int x⁻¹] with w h1 h2
  rw [map_inv₀, map_inv₀] at h2
  have h0 : Valued.v (algebraMap E (w.adicCompletion E) x) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact (_root_.map_ne_zero _).2 hx
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h2)

theorem mem_GLint {L : Type} [Field L] {O : Subring L} {n : ℕ} (g : GL (Fin n) L)
    (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ O)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ O) :
    g ∈ GLint (Fin n) O := by
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, h2 i j⟩
  have hA : A.map O.subtype = (g : Matrix (Fin n) (Fin n) L) := by ext i j; rfl
  have hB : B.map O.subtype = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by ext i j; rfl
  have inj : ∀ M N : Matrix (Fin n) (Fin n) O, M.map O.subtype = N.map O.subtype → M = N := fun M N h => by
    ext i j; exact congrFun (congrFun h i) j
  have hAB : A * B = 1 := inj _ _ (by
    rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
  have hBA : B * A = 1 := inj _ _ (by
    rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  ext i j; rfl

theorem Ov_eq {E : Type} [Field E] [NumberField E] (w : Pl E) :
    (w.adicCompletionIntegers E).toSubring = intL (w.adicCompletion E) := by
  ext x
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).trans (Valuation.mem_integer_iff _ _).symm

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P ∈ Ell E n →
    (∀ᶠ w in (cofinite : Filter (Pl E)), ∃ y : UL n w, y ∈ KL n w ∧ y.1.val.charpoly = atPl w P) ∧
      ∀ w : Pl E, IsSplitAt w → ∃ y : UL n w, y.1.val.charpoly = atPl w P := by
  intro E _ _ _ hU n P hP
  obtain ⟨C, H, hC, hCd, hHd, hHh, hCH⟩ := lemGlobal E n P hP
  set Ci := C⁻¹ with hCi
  have hCCi : C * Ci = 1 := Matrix.mul_nonsing_inv C (isUnit_iff_ne_zero.2 hCd)
  have hCiC : Ci * C = 1 := Matrix.nonsing_inv_mul C (isUnit_iff_ne_zero.2 hCd)
  let f : ∀ w : Pl E, E →+* w.adicCompletion E := fun w => algebraMap E (w.adicCompletion E)
  let Cw : ∀ w : Pl E, GLw n w := fun w =>
    ⟨C.map (f w), Ci.map (f w), by rw [← Matrix.map_mul, hCCi, Matrix.map_one _ (map_zero _) (map_one _)],
      by rw [← Matrix.map_mul, hCiC, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have hCwv : ∀ w, ((Cw w : GLw n w) : Matrix (Fin n) (Fin n) _) = C.map (f w) := fun w => rfl
  have hCwi : ∀ w, (((Cw w)⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) = Ci.map (f w) := fun w => rfl
  have hchar : ∀ w, (C.map (f w)).charpoly = atPl w P := fun w => by
    rw [Matrix.charpoly_map, hC]
  refine ⟨?_, fun w hs => ⟨⟨Cw w, by rw [UL, if_pos hs]; exact Subgroup.mem_top _⟩, hchar w⟩⟩
  have hall : ∀ M : Matrix (Fin n) (Fin n) E, ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, Valued.v (f w (M i j)) ≤ 1 :=
    fun M => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ae_int (M i j)
  filter_upwards [hall C, hall Ci, hall H, ae_unit hHd, ae_unit (two_ne_zero : (2 : E) ≠ 0)] with w h1 h2 h3 h4 h5
  have hO : ∀ x : w.adicCompletion E, Valued.v x ≤ 1 → x ∈ (w.adicCompletionIntegers E).toSubring :=
    fun x hx => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx
  have hK : Cw w ∈ GlobalTheory.LFun.KGL w n :=
    mem_GLint _ (fun i j => hO _ (h1 i j)) (fun i j => hO _ (h2 i j))
  by_cases hs : IsSplitAt w
  · exact ⟨⟨Cw w, by rw [UL, if_pos hs]; exact Subgroup.mem_top _⟩, Subgroup.mem_subgroupOf.2 hK, hchar w⟩
  · obtain ⟨-, -, -, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨hext, ⟨ϖ, q, hUI, -⟩, -, -⟩ := hns hs
    have h2v : Valued.v (2 : w.adicCompletion E) = 1 := by
      have e : f w 2 = 2 := map_ofNat _ 2
      rw [← e]; exact h5
    have hq := lemOdd _ ϖ (cj w) q hUI h2v
    set Hw := H.map (f w) with hHwdef
    have hHw1 : ∀ i j, Hw i j ∈ intL (w.adicCompletion E) := fun i j => (Valuation.mem_integer_iff _ _).2 (h3 i j)
    have hHw2 : Valued.v Hw.det = 1 := by
      rw [show Hw.det = f w H.det from (RingHom.map_det (f w) H).symm]; exact h4
    have hmapc : ∀ M : Matrix (Fin n) (Fin n) E,
        cT (cj w) (M.map (f w)) = (cT (IsCMField.complexConj E).toRingEquiv.toRingHom M).map (f w) := by
      intro M; refine Matrix.ext fun i j => ?_; simp only [cT, Matrix.map_apply, Matrix.transpose_apply]; exact hext (M j i)
    have hHw3 : cT (cj w) Hw = Hw := by rw [hmapc, hHh]
    have hCHw : cT (cj w) (C.map (f w)) * Hw * C.map (f w) = Hw := by
      rw [hmapc, hHwdef, ← Matrix.map_mul, ← Matrix.map_mul, hCH]
    obtain ⟨R, hR, hRH⟩ := lemLocal (w.adicCompletion E) ϖ (cj w) q hUI hq n Hw hHw1 hHw2 hHw3
    have hRK : R ∈ GlobalTheory.LFun.KGL w n := by
      have e : GlobalTheory.LFun.KGL w n = GLint (Fin n) (intL (w.adicCompletion E)) := by
        show GLint (Fin n) (w.adicCompletionIntegers E).toSubring = _
        rw [Ov_eq]
      rw [e]; exact hR
    refine ⟨⟨R⁻¹ * Cw w * R, ?_⟩, Subgroup.mem_subgroupOf.2 (mul_mem (mul_mem (inv_mem hRK) hK) hRK), ?_⟩
    · rw [UL, if_neg hs]
      show cT (cj w) ((R⁻¹ * Cw w * R : GLw n w) : Matrix (Fin n) (Fin n) _) * 1 *
        ((R⁻¹ * Cw w * R : GLw n w) : Matrix (Fin n) (Fin n) _) = 1
      rw [Units.val_mul, Units.val_mul, hCwv]
      set r := ((R : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
      set ri := (((R⁻¹ : GLw n w)) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
      have hri : r * ri = 1 := Units.mul_inv R
      have hH' : Hw = cT (cj w) ri * ri := by
        calc Hw = cT (cj w) (r * ri) * Hw * (r * ri) := by rw [hri, cT_one, Matrix.one_mul, Matrix.mul_one]
          _ = cT (cj w) ri * (cT (cj w) r * Hw * r) * ri := by rw [cT_mul]; simp only [Matrix.mul_assoc]
          _ = cT (cj w) ri * ri := by rw [hRH, Matrix.mul_one]
      rw [Matrix.mul_one, cT_mul, cT_mul]
      calc cT (cj w) r * (cT (cj w) (C.map (f w)) * cT (cj w) ri) * (ri * C.map (f w) * r)
          = cT (cj w) r * (cT (cj w) (C.map (f w)) * (cT (cj w) ri * ri) * C.map (f w)) * r := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [← hH', hCHw, hRH]
    · have hinv : ((((R⁻¹ : GLw n w)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))⁻¹ =
          ((R : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
        rw [← Matrix.coe_units_inv, inv_inv]
      have e := Matrix.charpoly_units_conj (R⁻¹ : GLw n w) (C.map (f w))
      rw [hinv] at e
      have key : ((R⁻¹ * Cw w * R : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).charpoly = atPl w P := by
        rw [Units.val_mul, Units.val_mul, hCwv, e, hchar]
      exact key

end GlobalTheory.IntUnitaryPoly
end
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_charpoly_local_realisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P ∈ Ell E n → (∀ᶠ w in (cofinite : Filter (Pl E)), ∃ y : UL n w, y ∈ KL n w ∧ y.1.val.charpoly = atPl w P) ∧ ∀ w : Pl E, IsSplitAt w → ∃ y : UL n w, y.1.val.charpoly = atPl w P := by
  first | exact @GlobalTheory.IntUnitaryPoly.main | exact GlobalTheory.IntUnitaryPoly.main | (intros; apply GlobalTheory.IntUnitaryPoly.main <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinPolySupp

theorem int_pts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (y : GLw n w), y ∈ GlobalTheory.LFun.KGL w n → (∀ k, Valued.v (y.val.charpoly.coeff k) ≤ 1) ∧ Valued.v (y⁻¹ : GLw n w).val.det ≤ 1 := by
  intro E _ _ _ n w y hy
  obtain ⟨M, rfl⟩ := hy
  have hint : ∀ z : Ov E w, Valued.v (z : w.adicCompletion E) ≤ 1 := fun z =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 z.2
  refine ⟨fun k => ?_, ?_⟩
  · have : (bc (Ov E w).subtype M).val = (M.val).map (Ov E w).subtype := rfl
    rw [this, Matrix.charpoly_map, coeff_map]; exact hint _
  · rw [← map_inv]
    have : (bc (Ov E w).subtype M⁻¹).val = ((M⁻¹).val).map (Ov E w).subtype := rfl
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hint _
end GlobalTheory.FinPolySupp

namespace GlobalTheory.FinPolySupp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem val_alg (w : Pl E) (x : E) : Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

theorem pl_ext {u u' : Pl E} (h : ∀ x : E, u.valuation E x = u'.valuation E x) : u = u' := by
  apply HeightOneSpectrum.ext
  ext a
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), h]

theorem transfer {n : ℕ} (w : Pl E) (y : GLw n w) (P : E[X]) (hP : y.val.charpoly = atPl w P)
    (γ : WithZero (Multiplicative ℤ))
    (h1 : ∀ k, Valued.v (y.val.charpoly.coeff k) ≤ γ) (h2 : Valued.v (y⁻¹ : GLw n w).val.det ≤ γ) :
    (∀ k, w.valuation E (P.coeff k) ≤ γ) ∧ w.valuation E (P.coeff 0)⁻¹ ≤ γ := by
  have hc : ∀ k, algebraMap E (w.adicCompletion E) (P.coeff k) = y.val.charpoly.coeff k := by
    intro k; rw [hP, atPl, coeff_map]
  refine ⟨fun k => ?_, ?_⟩
  · rw [← val_alg, hc]; exact h1 k
  · rw [← val_alg, map_inv₀, hc]
    have hdet : y.val.det = (-1) ^ Fintype.card (Fin n) * y.val.charpoly.coeff 0 :=
      Matrix.det_eq_sign_charpoly_coeff _
    have hmul : (y⁻¹ : GLw n w).val.det * y.val.det = 1 := by
      rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
    have hinv : (y⁻¹ : GLw n w).val.det = (y.val.det)⁻¹ := eq_inv_of_mul_eq_one_left hmul
    have hv : Valued.v y.val.det = Valued.v (y.val.charpoly.coeff 0) := by
      rw [hdet, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    rw [hinv, map_inv₀, hv] at h2
    rw [map_inv₀]; exact h2

theorem bound_at (n : ℕ) (w : Pl E) (f : UL n w → ℂ) (hf : HasCompactSupport f) :
    ∃ γ : WithZero (Multiplicative ℤ), (f = (KL n w : Set (UL n w)).indicator 1 → γ = 1) ∧
      ∀ P : E[X], (∃ y : UL n w, f y ≠ 0 ∧ y.1.val.charpoly = atPl w P) →
        (∀ k, w.valuation E (P.coeff k) ≤ γ) ∧ w.valuation E (P.coeff 0)⁻¹ ≤ γ := by
  by_cases hind : f = (KL n w : Set (UL n w)).indicator 1
  · refine ⟨1, fun _ => rfl, ?_⟩
    rintro P ⟨y, hy, hP⟩
    have hyK : y ∈ KL n w := by
      by_contra hn
      apply hy
      rw [hind]
      exact Set.indicator_of_notMem hn _
    have hy1 : y.1 ∈ GlobalTheory.LFun.KGL w n := (Subgroup.mem_subgroupOf).1 hyK
    obtain ⟨h1, h2⟩ := int_pts E n w y.1 hy1
    exact transfer w y.1 P hP 1 h1 h2
  · obtain ⟨γ, hγ⟩ := GlobalTheory.T.charpoly_coeff_det_inv_valuation_bounded_of_isCompact_GL E n w (Subtype.val '' tsupport f) (hf.image continuous_subtype_val)
    refine ⟨γ, fun h => absurd h hind, ?_⟩
    rintro P ⟨y, hy, hP⟩
    obtain ⟨h1, h2⟩ := hγ y.1 ⟨y, subset_tsupport f hy, rfl⟩
    exact transfer w y.1 P hP γ h1 h2

theorem conj_coeff (n : ℕ) (P : E[X]) (hP : P ∈ Ell E n) (k : ℕ) :
    IsCMField.complexConj E (P.coeff k) = if k ≤ n then P.coeff (n - k) * (P.coeff 0)⁻¹ else 0 := by
  obtain ⟨h0, hcsr⟩ := GlobalTheory.T.elliptic_charpoly_self_reciprocal E n P hP
  have hdeg : (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).natDegree = n := by
    rw [natDegree_map_eq_of_injective (RingHom.injective _)]; exact hP.2.1
  have key : ∀ j ≤ n, IsCMField.complexConj E (P.coeff 0) * P.coeff j =
      IsCMField.complexConj E (P.coeff (n - j)) := by
    intro j hj
    have := congrArg (fun Q => Q.coeff j) hcsr
    simp only [coeff_C_mul, coeff_reverse, hdeg, coeff_map] at this
    rw [revAt_le hj] at this
    exact this
  have hc0 : IsCMField.complexConj E (P.coeff 0) = (P.coeff 0)⁻¹ := by
    have := key 0 (Nat.zero_le _)
    have hn : P.coeff n = 1 := by rw [← hP.2.1]; exact hP.1
    rw [Nat.sub_zero, hn, map_one] at this
    exact eq_inv_of_mul_eq_one_left this
  split_ifs with hk
  · have := key (n - k) (Nat.sub_le n k)
    rw [Nat.sub_sub_self hk, hc0] at this
    rw [← this]; field_simp
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [hP.2.1]; omega), map_zero]

theorem finpoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ f : ∀ w : Pl E, UL n w → ℂ, (∀ w, HasCompactSupport (f w)) → (∀ᶠ w in (cofinite : Filter (Pl E)), f w = (KL n w : Set (UL n w)).indicator 1) → {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ y : UL n w, f w y ≠ 0 ∧ y.1.val.charpoly = atPl w P}.Finite := by
  intro E _ _ _ _ n S hS f hcpt hev
  choose γ hγ1 hγ using fun w => bound_at n w (f w) (hcpt w)
  have hpart := GlobalTheory.T.exists_mem_section_valuation_eq_conj E S hS
  let p : Pl E → Pl E := fun u => if h : u ∈ S then u else (hpart u h).choose
  have hpS : ∀ u, u ∉ S → p u ∈ S ∧ ∀ x : E, u.valuation E x = (p u).valuation E (IsCMField.complexConj E x) := by
    intro u hu; simp only [p, dif_neg hu]; exact (hpart u hu).choose_spec
  let Γ : Pl E → WithZero (Multiplicative ℤ) := fun u => if u ∈ S then γ u else γ (p u) * γ (p u)
  have hB : {w | ¬ f w = (KL n w : Set (UL n w)).indicator 1}.Finite := Filter.eventually_cofinite.1 hev
  have hΓ : ∀ᶠ u in cofinite, Γ u ≤ 1 := by
    rw [Filter.eventually_cofinite]
    have hsub : {u | ¬ Γ u ≤ 1} ⊆ {w | ¬ f w = (KL n w : Set (UL n w)).indicator 1} ∪
        {u | u ∉ S ∧ p u ∈ {w | ¬ f w = (KL n w : Set (UL n w)).indicator 1}} := by
      intro u hu
      by_cases huS : u ∈ S
      · left; intro hf; apply hu; simp [Γ, huS, hγ1 u hf]
      · right; refine ⟨huS, fun hf => hu ?_⟩; simp [Γ, huS, hγ1 _ hf]
    refine (hB.union ?_).subset hsub
    refine Set.Finite.of_finite_image (f := p) (hB.subset ?_) ?_
    · rintro _ ⟨u, hu, rfl⟩; exact hu.2
    · intro u hu u' hu' he
      apply pl_ext; intro x
      rw [(hpS u hu.1).2, (hpS u' hu'.1).2, he]
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.T.exists_common_integer_denominator_of_valuation_bounds E Γ hΓ
  refine (GlobalTheory.T.finite_monic_unitRoots_bounded_denominator_numberField E n d hd0).subset ?_
  rintro P ⟨hP, hPS⟩
  refine ⟨hP.1, hP.2.1, hP.2.2.2, fun k => hd _ fun u => ?_⟩
  by_cases huS : u ∈ S
  · simp only [Γ, if_pos huS]; exact (hγ u P (hPS u huS)).1 k
  · simp only [Γ, if_neg huS]
    obtain ⟨hpu, hv⟩ := hpS u huS
    obtain ⟨hb1, hb2⟩ := hγ (p u) P (hPS _ hpu)
    rw [hv, conj_coeff n P hP k]
    split_ifs
    · rw [map_mul]; exact mul_le_mul' (hb1 _) hb2
    · rw [map_zero]; exact zero_le'

end GlobalTheory.FinPolySupp
end
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.finite_elliptic_charpolys_support : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ f : ∀ w : Pl E, UL n w → ℂ, (∀ w, HasCompactSupport (f w)) → (∀ᶠ w in (cofinite : Filter (Pl E)), f w = (KL n w : Set (UL n w)).indicator 1) → {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ y : UL n w, f w y ≠ 0 ∧ y.1.val.charpoly = atPl w P}.Finite := by
  first | exact @GlobalTheory.FinPolySupp.finpoly | (intros; apply GlobalTheory.FinPolySupp.finpoly <;> assumption)
end

section
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DivSum

open UniqueFactorizationMonoid

variable {k : Type} [Field k]

theorem monic_of_mem_normalizedFactors {P q : k[X]} (hq : q ∈ normalizedFactors P) : q.Monic := by
  have h0 : q ≠ 0 := (irreducible_of_normalized_factor q hq).ne_zero
  rw [← normalize_normalized_factor q hq]
  exact Polynomial.monic_normalize h0

theorem monic_prod_sub {P : k[X]} (t : Finset k[X]) (ht : t ⊆ (normalizedFactors P).toFinset) :
    (∏ q ∈ t, q).Monic := by
  exact Polynomial.monic_prod_of_monic t id fun q hq => monic_of_mem_normalizedFactors (Multiset.mem_toFinset.1 (ht hq))

theorem normalizedFactors_prod_sub {P : k[X]} (t : Finset k[X]) (ht : t ⊆ (normalizedFactors P).toFinset) :
    normalizedFactors (∏ q ∈ t, q) = t.val := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id',
    normalizedFactors_prod_eq _ fun q hq => irreducible_of_normalized_factor q (Multiset.mem_toFinset.1 (ht hq))]
  conv_rhs => rw [← Multiset.map_id t.val]
  exact Multiset.map_congr rfl fun q hq => normalize_normalized_factor q (Multiset.mem_toFinset.1 (ht hq))

theorem prod_sub_dvd {P : k[X]} (hP : P ≠ 0) (t : Finset k[X])
    (ht : t ⊆ (normalizedFactors P).toFinset) : (∏ q ∈ t, q) ∣ P := by
  have h0 : (∏ q ∈ t, q) ≠ 0 := (monic_prod_sub t ht).ne_zero
  rw [dvd_iff_normalizedFactors_le_normalizedFactors h0 hP, normalizedFactors_prod_sub t ht]
  exact (Multiset.le_iff_subset t.nodup).2 fun q hq => Multiset.mem_toFinset.1 (ht hq)

theorem eq_prod_sub {P Q : k[X]} (hP : P ≠ 0) (hsq : Squarefree P) (hQ : Q.Monic) (hQP : Q ∣ P) :
    (normalizedFactors Q).toFinset ⊆ (normalizedFactors P).toFinset ∧
      Q = ∏ q ∈ (normalizedFactors Q).toFinset, q := by
  have hQ0 := hQ.ne_zero
  have hle := (dvd_iff_normalizedFactors_le_normalizedFactors hQ0 hP).1 hQP
  refine ⟨fun a ha => Multiset.mem_toFinset.2 (Multiset.mem_of_le hle (Multiset.mem_toFinset.1 ha)), ?_⟩
  have hnd : (normalizedFactors Q).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hQ0).1 (hsq.squarefree_of_dvd hQP)
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id', Multiset.toFinset_val, hnd.dedup,
    prod_normalizedFactors_eq hQ0]
  exact ((Polynomial.normalize_eq_self_iff_monic hQ0).2 hQ).symm

end GlobalTheory.DivSum

namespace GlobalTheory.DivSum

open UniqueFactorizationMonoid

variable {k : Type} [Field k]

theorem isCoprime_of_sub {P q : k[X]} (t : Finset k[X]) (ht : t ⊆ (normalizedFactors P).toFinset)
    (hq : q ∈ (normalizedFactors P).toFinset) (hqt : q ∉ t) : IsCoprime q (∏ r ∈ t, r) := by
  refine IsCoprime.prod_right fun r hr => ?_
  have hqP := Multiset.mem_toFinset.1 hq
  have hrP := Multiset.mem_toFinset.1 (ht hr)
  rw [(irreducible_of_normalized_factor q hqP).coprime_iff_not_dvd]
  intro hd
  exact hqt (normalizedFactors_eq_of_dvd P q hqP r hrP hd ▸ hr)

theorem s_prod_sub {P : k[X]} (hP : P ≠ 0) (s : k[X] → ℂ)
    (hmul : ∀ Q₁ Q₂ : k[X], Q₁.Monic → Q₂.Monic → Q₁ * Q₂ ∣ P → IsCoprime Q₁ Q₂ → s (Q₁ * Q₂) = s Q₁ * s Q₂)
    (h1 : s 1 = 1) (t : Finset k[X]) (ht : t ⊆ (normalizedFactors P).toFinset) :
    s (∏ q ∈ t, q) = ∏ q ∈ t, s q := by
  induction t using Finset.induction_on with
  | empty => simp [h1]
  | insert a t ha ih =>
    have ht' : t ⊆ (normalizedFactors P).toFinset := fun x hx => ht (Finset.mem_insert_of_mem hx)
    have haP : a ∈ (normalizedFactors P).toFinset := ht (Finset.mem_insert_self a t)
    have hma : a.Monic := monic_of_mem_normalizedFactors (Multiset.mem_toFinset.1 haP)
    have hd : a * ∏ q ∈ t, q ∣ P := by
      have h := prod_sub_dvd hP _ ht
      rwa [Finset.prod_insert ha] at h
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      hmul _ _ hma (monic_prod_sub t ht') hd (isCoprime_of_sub t ht' haP ha), ih ht']

theorem finsum_monic_divisors_sign : ∀ (k : Type) [Field k] (P : k[X]), P.Monic → P.Separable → ∀ s : k[X] → ℂ,
    (∀ Q₁ Q₂ : k[X], Q₁.Monic → Q₂.Monic → Q₁ * Q₂ ∣ P → IsCoprime Q₁ Q₂ → s (Q₁ * Q₂) = s Q₁ * s Q₂) →
    (∀ Q : k[X], Q.Monic → Q ∣ P → s Q = 1 ∨ s Q = -1) →
    {Q : k[X] | Q.Monic ∧ Q ∣ P}.Finite ∧
      ∑ᶠ Q : {Q : k[X] // Q.Monic ∧ Q ∣ P}, s Q.1 =
        if ∀ Q : k[X], Q.Monic → Q ∣ P → s Q = 1 then 2 ^ nfac P else 0 := by
  intro k _ P hPm hPs s hmul hsgn
  have hP : P ≠ 0 := hPm.ne_zero
  have hsq : Squarefree P := hPs.squarefree
  set F := (normalizedFactors P).toFinset with hF
  have memF : ∀ q ∈ F, q.Monic ∧ q ∣ P := fun q hq =>
    ⟨monic_of_mem_normalizedFactors (Multiset.mem_toFinset.1 hq),
      dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.1 hq)⟩
  have h1 : s 1 = 1 := by
    have hm := hmul 1 1 monic_one monic_one (by rw [one_mul]; exact one_dvd P) isCoprime_one_left
    rw [one_mul] at hm
    rcases hsgn 1 monic_one (one_dvd P) with h | h
    · exact h
    · rw [h] at hm
      norm_num at hm
  let φ : {t // t ∈ F.powerset} → {Q : k[X] // Q.Monic ∧ Q ∣ P} := fun t =>
    ⟨∏ q ∈ t.1, q, monic_prod_sub t.1 (Finset.mem_powerset.1 t.2),
      prod_sub_dvd hP t.1 (Finset.mem_powerset.1 t.2)⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have h := congrArg (fun Q : {Q : k[X] // Q.Monic ∧ Q ∣ P} => normalizedFactors Q.1) hab
    simp only [φ] at h
    rw [normalizedFactors_prod_sub a.1 (Finset.mem_powerset.1 a.2),
      normalizedFactors_prod_sub b.1 (Finset.mem_powerset.1 b.2)] at h
    exact Subtype.ext (Finset.val_injective h)
  have hsurj : Function.Surjective φ := by
    rintro ⟨Q, hQm, hQd⟩
    obtain ⟨hsub, heq⟩ := eq_prod_sub hP hsq hQm hQd
    exact ⟨⟨_, Finset.mem_powerset.2 hsub⟩, Subtype.ext heq.symm⟩
  have hs1 : ∀ q ∈ F, s q = 1 ∨ s q = -1 := fun q hq => hsgn q (memF q hq).1 (memF q hq).2
  refine ⟨?_, ?_⟩
  · have hsub : {Q : k[X] | Q.Monic ∧ Q ∣ P} ⊆ ((F.powerset.image fun t => ∏ q ∈ t, q : Finset k[X]) : Set k[X]) := by
      intro Q hQ
      obtain ⟨⟨t, ht⟩, htQ⟩ := hsurj ⟨Q, hQ⟩
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨t, ht, congrArg Subtype.val htQ⟩)
    exact (Finset.finite_toSet _).subset hsub
  · rw [← finsum_comp_equiv (Equiv.ofBijective φ ⟨hinj, hsurj⟩), finsum_eq_sum_of_fintype]
    have hsum : ∑ t : {t // t ∈ F.powerset}, s (Equiv.ofBijective φ ⟨hinj, hsurj⟩ t).1 = ∏ q ∈ F, (1 + s q) := by
      rw [Finset.prod_one_add, ← Finset.sum_coe_sort F.powerset]
      refine Finset.sum_congr rfl fun t _ => ?_
      exact s_prod_sub hP s hmul h1 t.1 (Finset.mem_powerset.1 t.2)
    rw [hsum]
    split_ifs with hall
    · rw [Finset.prod_congr rfl fun q hq => show 1 + s q = 2 by
        rw [hall q (memF q hq).1 (memF q hq).2]
        norm_num, Finset.prod_const]
      have hnd : (normalizedFactors P).Nodup := (squarefree_iff_nodup_normalizedFactors hP).1 hsq
      rw [hF, Multiset.card_toFinset, hnd.dedup]
      rfl
    · push_neg at hall
      obtain ⟨Q, hQm, hQd, hQs⟩ := hall
      obtain ⟨hsub, heq⟩ := eq_prod_sub hP hsq hQm hQd
      have hsQ := s_prod_sub hP s hmul h1 _ hsub
      rw [← heq] at hsQ
      by_contra hne
      apply hQs
      rw [hsQ]
      refine Finset.prod_eq_one fun q hq => ?_
      rcases hs1 q (hsub hq) with h | h
      · exact h
      · exact absurd (Finset.prod_eq_zero (hsub hq) (by rw [h]; norm_num)) hne

end GlobalTheory.DivSum
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monic_divisor_sign_sum : ∀ (k : Type) [Field k] (P : k[X]), P.Monic → P.Separable → ∀ s : k[X] → ℂ, (∀ Q₁ Q₂ : k[X], Q₁.Monic → Q₂.Monic → Q₁ * Q₂ ∣ P → IsCoprime Q₁ Q₂ → s (Q₁ * Q₂) = s Q₁ * s Q₂) → (∀ Q : k[X], Q.Monic → Q ∣ P → s Q = 1 ∨ s Q = -1) → {Q : k[X] | Q.Monic ∧ Q ∣ P}.Finite ∧ ∑ᶠ Q : {Q : k[X] // Q.Monic ∧ Q ∣ P}, s Q.1 = if ∀ Q : k[X], Q.Monic → Q ∣ P → s Q = 1 then 2 ^ nfac P else 0 := by
  atlas_forward_decl GlobalTheory.DivSum.finsum_monic_divisors_sign
end

section
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem finprod_mem_eq_zero_of_factor {ι : Type} (f : ι → ℂ) (S : Set ι)
    (hfin : {w | f w ≠ 1}.Finite) {w₀ : ι} (hw₀ : w₀ ∈ S) (h0 : f w₀ = 0) :
    ∏ᶠ w ∈ S, f w = 0 := by
  have hs : (S ∩ Function.mulSupport f).Finite := hfin.subset fun w hw => hw.2
  rw [finprod_mem_eq_prod f hs]
  refine Finset.prod_eq_zero (i := w₀) ?_ h0
  rw [Set.Finite.mem_toFinset]
  refine ⟨hw₀, ?_⟩
  rw [Function.mem_mulSupport, h0]
  exact zero_ne_one

theorem finsum_finprod_local_sums_expand : ∀ (ι : Type) (S : Set ι) (Cl : ι → Type) [∀ w, Finite (Cl w)] (D R : Type) [Finite D] (loc : R → ∀ w, Cl w) (O : ∀ w, Cl w → ℂ) (s : D → ∀ w, Cl w → ℂ) (good : ∀ w, Cl w → Prop) (N : ℂ), (∀ᶠ w in (cofinite : Filter ι), (∃! c, good w c) ∧ ∀ c, (O w c = if good w c then 1 else 0) ∧ (good w c → ∀ d, s d w c = 1)) → (∀ w, w ∉ S → Nonempty (Cl w)) → (∀ r, ∀ᶠ w in (cofinite : Filter ι), good w (loc r w)) → (∀ r r', (∀ w ∈ S, loc r w = loc r' w) → r = r') → (∀ x : ∀ w, Cl w, (∀ᶠ w in (cofinite : Filter ι), good w (x w)) → ∑ᶠ d : D, ∏ᶠ w ∈ S, s d w (x w) = if ∃ r, ∀ w ∈ S, loc r w = x w then N else 0) → (Function.support fun r : R => ∏ᶠ w ∈ S, O w (loc r w)).Finite ∧ (∑ᶠ r : R, ∏ᶠ w ∈ S, O w (loc r w)) * N = ∑ᶠ d : D, ∏ᶠ w ∈ S, ∑ᶠ c : Cl w, s d w c * O w c := by
  intro ι S Cl _ D R _ loc O s good N hA hB hC hD hE
  classical
  haveI : ∀ w, Fintype (Cl w) := fun w => Fintype.ofFinite _
  haveI : Fintype D := Fintype.ofFinite D
  obtain ⟨T, hTfin, hTA⟩ : ∃ T : Set ι, T.Finite ∧ ∀ w, w ∉ T →
      ((∃! c, good w c) ∧ ∀ c, (O w c = if good w c then 1 else 0) ∧ (good w c → ∀ d, s d w c = 1)) :=
    ⟨_, Filter.eventually_cofinite.1 hA, fun w hw => not_not.1 hw⟩
  have hO : ∀ w, w ∉ T → ∀ c, O w c = if good w c then 1 else 0 := fun w hw c => ((hTA w hw).2 c).1
  have hs1 : ∀ w, w ∉ T → ∀ c, good w c → ∀ d, s d w c = 1 := fun w hw c => ((hTA w hw).2 c).2
  have huniq : ∀ w, w ∉ T → ∀ c c', good w c → good w c' → c = c' :=
    fun w hw c c' hc hc' => (hTA w hw).1.unique hc hc'
  obtain ⟨F, hF⟩ : ∃ F : Finset ι, ∀ w, w ∈ F ↔ w ∈ S ∧ w ∈ T :=
    ⟨hTfin.toFinset.filter (· ∈ S), fun w => by simp [and_comm]⟩
  obtain ⟨ext, ext_F, ext_good⟩ : ∃ ext : (∀ w : F, Cl w) → ∀ w, Cl w,
      (∀ x (w : F), ext x w = x w) ∧ ∀ x w, w ∉ T → good w (ext x w) := by
    refine ⟨fun x w => if h : w ∈ F then x ⟨w, h⟩ else if hw : w ∈ T then
      (hB w (fun hS => h ((hF w).2 ⟨hS, hw⟩))).some else (hTA w hw).1.exists.choose,
      fun x w => dif_pos w.2, fun x w hw => ?_⟩
    have hwF : w ∉ F := fun h => hw ((hF w).1 h).2
    simp only [dif_neg hwF, dif_neg hw]
    exact (hTA w hw).1.exists.choose_spec
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : R → ∀ w : F, Cl w, ∀ r (w : F), ρ r w = loc r w :=
    ⟨fun r w => loc r w, fun _ _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Set R, ∀ r, r ∈ G ↔ ∀ w ∈ S, w ∉ T → good w (loc r w) :=
    ⟨{r | ∀ w ∈ S, w ∉ T → good w (loc r w)}, fun _ => Iff.rfl⟩
  have prodS : ∀ φ : ι → ℂ, (∀ w ∈ S, w ∉ T → φ w = 1) → ∏ᶠ w ∈ S, φ w = ∏ w : F, φ w := by
    intro φ hφ
    have h1 : S ∩ Function.mulSupport φ ⊆ (F : Set ι) := by
      rintro w ⟨hwS, hw1⟩
      by_contra hwF
      exact hw1 (hφ w hwS fun hT => hwF (Finset.mem_coe.2 ((hF w).2 ⟨hwS, hT⟩)))
    have h2 : (F : Set ι) ⊆ S := fun w hw => ((hF w).1 (Finset.mem_coe.1 hw)).1
    rw [finprod_mem_eq_prod_of_subset φ h1 h2, ← Finset.prod_coe_sort]
  have hR : ∀ d, ∏ᶠ w ∈ S, ∑ᶠ c, s d w c * O w c =
      ∑ x : (∀ w : F, Cl w), (∏ w : F, s d w (x w)) * ∏ w : F, O w (x w) := by
    intro d
    rw [prodS]
    · simp only [finsum_eq_sum_of_fintype]
      rw [Fintype.prod_sum]
      exact Finset.sum_congr rfl fun x _ => Finset.prod_mul_distrib
    · intro w _ hw
      obtain ⟨c0, hc0⟩ := (hTA w hw).1.exists
      rw [finsum_eq_sum_of_fintype, Finset.sum_eq_single c0]
      · rw [hO w hw c0, if_pos hc0, hs1 w hw c0 hc0 d, mul_one]
      · intro c _ hc
        rw [hO w hw c, if_neg (fun hg => hc (huniq w hw c c0 hg hc0)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ c0) h
  have hs_ext : ∀ d x, ∏ᶠ w ∈ S, s d w (ext x w) = ∏ w : F, s d w (x w) := by
    intro d x
    rw [prodS]
    · exact Finset.prod_congr rfl fun w _ => by rw [ext_F]
    · intro w _ hw
      exact hs1 w hw _ (ext_good x w hw) d
  have hEx : ∀ x, ∑ d, ∏ w : F, s d w (x w) = if ∃ r, ∀ w ∈ S, loc r w = ext x w then N else 0 := by
    intro x
    rw [← hE (ext x) ?_, finsum_eq_sum_of_fintype]
    · exact Finset.sum_congr rfl fun d _ => (hs_ext d x).symm
    · exact Filter.eventually_cofinite.2 (hTfin.subset fun w hw => by_contra fun hwT => hw (ext_good x w hwT))
  have hρ : ∀ r ∈ G, ∀ w ∈ S, loc r w = ext (ρ r) w := by
    intro r hr w hwS
    by_cases hwF : w ∈ F
    · have h := ext_F (ρ r) ⟨w, hwF⟩
      rw [hρdef] at h
      exact h.symm
    · have hwT : w ∉ T := fun hT => hwF ((hF w).2 ⟨hwS, hT⟩)
      exact huniq w hwT _ _ ((hG r).1 hr w hwS hwT) (ext_good _ w hwT)
  have hρinj : Set.InjOn ρ G := by
    intro r hr r' hr' h
    apply hD
    intro w hwS
    rw [hρ r hr w hwS, hρ r' hr' w hwS, h]
  have hP0 : ∀ r, r ∉ G → ∏ᶠ w ∈ S, O w (loc r w) = 0 := by
    intro r hr
    rw [hG] at hr
    push_neg at hr
    obtain ⟨w, hwS, hwT, hg⟩ := hr
    refine finprod_mem_eq_zero_of_factor _ S ?_ hwS ?_
    · refine (hTfin.union (Filter.eventually_cofinite.1 (hC r))).subset fun v hv => ?_
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
      exact hv (by rw [hO v hcon.1, if_pos hcon.2])
    · rw [hO w hwT, if_neg hg]
  have hP1 : ∀ r ∈ G, ∏ᶠ w ∈ S, O w (loc r w) = ∏ w : F, O w (ρ r w) := by
    intro r hr
    rw [prodS]
    · exact Finset.prod_congr rfl fun w _ => by rw [hρdef]
    · intro w hwS hwT
      rw [hO w hwT, if_pos ((hG r).1 hr w hwS hwT)]
  have hGfin : G.Finite := Set.Finite.of_finite_image (Set.toFinite _) hρinj
  have hmem : ∀ x, x ∈ ρ '' G ↔ ∃ r, ∀ w ∈ S, loc r w = ext x w := by
    intro x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, hρ r hr⟩
    · rintro ⟨r, hr⟩
      refine ⟨r, ?_, ?_⟩
      · rw [hG]
        intro w hwS hwT
        rw [hr w hwS]
        exact ext_good x w hwT
      · funext w
        rw [hρdef, hr w ((hF w).1 w.2).1, ext_F]
  have hsum : ∑ᶠ r, ∏ᶠ w ∈ S, O w (loc r w) =
      ∑ x : (∀ w : F, Cl w), if ∃ r, ∀ w ∈ S, loc r w = ext x w then ∏ w : F, O w (x w) else 0 := by
    calc ∑ᶠ r, ∏ᶠ w ∈ S, O w (loc r w) = ∑ᶠ r ∈ G, ∏ w : F, O w (ρ r w) := by
          rw [finsum_mem_def]
          apply finsum_congr
          intro r
          by_cases hr : r ∈ G
          · simp only [Set.indicator_apply, hr, if_true]
            exact hP1 r hr
          · simp only [Set.indicator_apply, hr, if_false]
            exact hP0 r hr
      _ = ∑ᶠ x ∈ ρ '' G, ∏ w : F, O w (x w) :=
          (finsum_mem_image (f := fun x : (∀ w : F, Cl w) => ∏ w : F, O w (x w)) hρinj).symm
      _ = _ := by
          rw [finsum_mem_def, finsum_eq_sum_of_fintype]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [Set.indicator_apply, hmem]
  refine ⟨hGfin.subset fun r hr => by_contra fun hrG => hr (hP0 r hrG), ?_⟩
  rw [hsum, finsum_congr hR, finsum_eq_sum_of_fintype, Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul, hEx x]
  split_ifs <;> ring

end GlobalTheory
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_class_count_product : ∀ (ι : Type) (S : Set ι) (Cl : ι → Type) [∀ w, Finite (Cl w)] (D R : Type) [Finite D] (loc : R → ∀ w, Cl w) (O : ∀ w, Cl w → ℂ) (s : D → ∀ w, Cl w → ℂ) (good : ∀ w, Cl w → Prop) (N : ℂ), (∀ᶠ w in (cofinite : Filter ι), (∃! c, good w c) ∧ ∀ c, (O w c = if good w c then 1 else 0) ∧ (good w c → ∀ d, s d w c = 1)) → (∀ w, w ∉ S → Nonempty (Cl w)) → (∀ r, ∀ᶠ w in (cofinite : Filter ι), good w (loc r w)) → (∀ r r', (∀ w ∈ S, loc r w = loc r' w) → r = r') → (∀ x : ∀ w, Cl w, (∀ᶠ w in (cofinite : Filter ι), good w (x w)) → ∑ᶠ d : D, ∏ᶠ w ∈ S, s d w (x w) = if ∃ r, ∀ w ∈ S, loc r w = x w then N else 0) → (Function.support fun r : R => ∏ᶠ w ∈ S, O w (loc r w)).Finite ∧ (∑ᶠ r : R, ∏ᶠ w ∈ S, O w (loc r w)) * N = ∑ᶠ d : D, ∏ᶠ w ∈ S, ∑ᶠ c : Cl w, s d w c * O w c := by
  atlas_forward_decl GlobalTheory.finsum_finprod_local_sums_expand
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PreStabU

section Generic

variable {G : Type} [Group G]

def cls (x : G) : TwCl (MonoidHom.id G) := Quot.mk _ x

theorem cls_eq_iff (x y : G) : cls x = cls y ↔ ∃ g, y = g⁻¹ * x * g := by
  have h : Equivalence fun x y : G => ∃ g, y = g⁻¹ * x * (MonoidHom.id G) g := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp [mul_assoc]⟩
    · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
      exact ⟨g * h, by simp [mul_assoc]⟩
  exact Quot.eq.trans h.eqvGen_iff

theorem cls_rep (c : TwCl (MonoidHom.id G)) : cls c.rep = c := Quot.out_eq c

theorem rep_cls (x : G) : ∃ g, (cls x).rep = g⁻¹ * x * g := (cls_eq_iff _ _).1 (cls_rep _).symm

theorem exists_ne_zero_of_twOrb [TopologicalSpace G] (K : Subgroup G) (δ : G) (f : G → ℂ)
    (h : twOrb (MonoidHom.id G) K δ f ≠ 0) : ∃ g, f (g⁻¹ * δ * g) ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  simp only [twOrb, avg, MonoidHom.id_apply, hc, finsum_zero, mul_zero]

theorem twOrb_conj [TopologicalSpace G] [IsTopologicalGroup G] {K K' : Subgroup G} (hK : IsCompact (K : Set G))
    (hK' : IsLevel (MonoidHom.id G) K K') {f : G → ℂ} (hf : IsHecke K' f) (δ g : G) :
    twOrb (MonoidHom.id G) K (g⁻¹ * δ * g) f = twOrb (MonoidHom.id G) K δ f := by
  refine GlobalTheory.T.twistedOrbitalIntegral_twistedConj_invariant G (MonoidHom.id G) K δ g f fun x => ?_
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := hK'.1.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  have hi : (K'.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine ne_zero_of_dvd_ne_zero hi (Subgroup.index_dvd_of_le fun k hk y => ?_)
  have hk' : (k : G) ∈ K' := hk
  have e : (x * ((y * k : K) : G))⁻¹ * δ * (MonoidHom.id G) (x * ((y * k : K) : G)) =
      (k : G)⁻¹ * (((x * y)⁻¹ * δ * (MonoidHom.id G) (x * y)) * k) := by
    simp only [MonoidHom.id_apply, Subgroup.coe_mul]; group
  show f _ = f _
  rw [e, (hf.2 _ (K'.inv_mem hk') _).1, (hf.2 _ hk' _).2]

end Generic

theorem finsum_subtype_if {α : Type} (p : α → Prop) [DecidablePred p] (u : α → ℂ) :
    ∑ᶠ a : Subtype p, u a.1 = ∑ᶠ a, if p a then u a else 0 := by
  rw [finsum_subtype_eq_finsum_cond]
  exact finsum_congr fun a => finsum_eq_if

theorem finsum_fibres {α β : Type} (u : α → ℂ) (q : α → β) (F : Finset β) (hu : (Function.support u).Finite)
    (hF : ∀ a, u a ≠ 0 → q a ∈ F) : ∑ᶠ a, u a = ∑ b ∈ F, ∑ᶠ a, if q a = b then u a else 0 := by
  rw [← finsum_sum_comm]
  · refine finsum_congr fun a => ?_
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra hc
      exact h (hF a hc)
  · intro b _
    refine hu.subset fun a ha => ?_
    intro h0
    apply ha
    simp [h0]

theorem ne_zero_of_finprod {ι : Type} {S : Set ι} {u : ι → ℂ} (h1 : ∀ᶠ w in cofinite, u w = 1)
    (h : ∏ᶠ w ∈ S, u w ≠ 0) : ∀ w ∈ S, u w ≠ 0 := by
  intro w hw h0
  apply h
  have hf : (Function.mulSupport u).Finite := h1
  rw [finprod_mem_def]
  refine finprod_eq_zero _ w (by simp [hw, h0]) ?_
  refine hf.subset ?_
  rw [Set.mulSupport_mulIndicator]
  exact Set.inter_subset_right

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem charpoly_conj {w : Pl E} (y g : UL n w) : (g⁻¹ * y * g).1.val.charpoly = y.1.val.charpoly := by
  simpa using Matrix.charpoly_units_conj' g.1 y.1.val

theorem charpoly_conj' (y g : UE E n) : (g⁻¹ * y * g).1.val.charpoly = y.1.val.charpoly := by
  simpa using Matrix.charpoly_units_conj' g.1 y.1.val

theorem charpoly_cls {w : Pl E} (y : UL n w) : (cls y).rep.1.val.charpoly = y.1.val.charpoly := by
  obtain ⟨g, hg⟩ := rep_cls y
  rw [hg, charpoly_conj]

theorem charpoly_locPt (hU : Unr E) (w : Pl E) (γ : UE E n) :
    (locPt w γ).1.val.charpoly = atPl w γ.1.val.charpoly := by
  rw [(GlobalTheory.T.local_points_integral_almost_all E hU n γ).1 w]
  exact Matrix.charpoly_map _ _

theorem locPt_conj (hU : Unr E) (w : Pl E) (γ g : UE E n) :
    locPt w (g⁻¹ * γ * g) = (locPt w g)⁻¹ * locPt w γ * locPt w g := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, (GlobalTheory.T.local_points_integral_almost_all E hU n _).1 w, map_mul, map_inv]

theorem atPl_separable {P : E[X]} (hP : P ∈ Ell E n) (w : Pl E) : (atPl w P).Separable := hP.2.2.1.map

theorem csr_one (w : Pl E) : IsCsr w (1 : (w.adicCompletion E)[X]) := by
  by_cases h : IsSplitAt w
  · exact Or.inl h
  · exact Or.inr (by simp [Polynomial.reverse])

theorem kapSign_conj (hU : Unr E) (hn : 1 ≤ n) {w : Pl E} (Q : (w.adicCompletion E)[X]) (y g : UL n w)
    (hy : y.1.val.charpoly.Separable) : kapSign n w Q (g⁻¹ * y * g).1 = kapSign n w Q y.1 :=
  (GlobalTheory.T.kappa_sign_multiplicative E hU n hn w 1 1 Q y g hy (by simp) isCoprime_one_left (csr_one w) (csr_one w)).2.1

abbrev LocCl (n : ℕ) (P : E[X]) (w : Pl E) : Type :=
  {c : TwCl (MonoidHom.id (UL n w)) // c.rep.1.val.charpoly = atPl w P}

def Good {P : E[X]} (w : Pl E) (c : LocCl n P w) : Prop := ∃ g : UL n w, g⁻¹ * c.1.rep * g ∈ KL n w

theorem ae_good (hU : Unr E) (hn : 1 ≤ n) {S : Set (Pl E)} (hS : IsSection S) {P : E[X]} (hP : P ∈ Ell E n)
    {f : ∀ w : Pl E, UL n w → ℂ} (hf : ∀ᶠ w in cofinite, f w = (KL n w : Set (UL n w)).indicator 1) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), (∃! c : LocCl n P w, Good w c) ∧ ∀ c : LocCl n P w,
      (twOrb (MonoidHom.id _) (KL n w) c.1.rep (f w) = if Good w c then 1 else 0) ∧
      (Good w c → ∀ Q : E[X], Q ∣ P → kapSign n w (atPl w Q) c.1.rep.1 = 1) := by
  filter_upwards [hf, GlobalTheory.T.orbitalIntegral_unitIndicator_eventually_oneClass E hU n hn S hS P hP, (GlobalTheory.T.elliptic_charpoly_local_realisation E hU n P hP).1, GlobalTheory.T.integral_conjugacy_almost_all E hU n P hP]
    with w h1 h2 h3 h4
  refine ⟨?_, fun c => ⟨?_, fun hc Q hQ => (h2 _ c.2).2.2 _ (Polynomial.map_dvd _ hQ) hc⟩⟩
  · obtain ⟨y, hy, hyP⟩ := h3
    refine ⟨⟨cls y, (charpoly_cls y).trans hyP⟩, ?_, ?_⟩
    · obtain ⟨g, hg⟩ := rep_cls y
      refine ⟨g⁻¹, ?_⟩
      simpa [hg, mul_assoc] using hy
    · rintro c ⟨g, hg⟩
      apply Subtype.ext
      obtain ⟨h, hh⟩ := h4 _ y hg hy ((charpoly_conj _ _).trans c.2) hyP
      show c.1 = cls y
      rw [← cls_rep c.1, cls_eq_iff]
      exact ⟨g * h, by rw [hh]; group⟩
  · rw [h1]
    exact (h2 _ c.2).1

theorem kapOrb_eq (w : Pl E) {P₁ P₂ P : E[X]} (h : P₁ * P₂ = P) (f : UL n w → ℂ) :
    kapOrb n w (atPl w P₁) (atPl w P₂) f =
      ∑ᶠ c : LocCl n P w, kapSign n w (atPl w P₁) c.1.rep.1 * twOrb (MonoidHom.id _) (KL n w) c.1.rep f := by
  rw [finsum_subtype_if (fun c : TwCl (MonoidHom.id (UL n w)) => c.rep.1.val.charpoly = atPl w P)
    (fun c => kapSign n w (atPl w P₁) c.rep.1 * twOrb (MonoidHom.id _) (KL n w) c.rep f)]
  unfold kapOrb clSum
  subst h
  simp only [Set.mem_ofPred_eq, atPl, Polynomial.map_mul]

theorem kapOrb_support (hU : Unr E) (hn : 1 ≤ n) {S : Set (Pl E)} (hS : IsSection S) {P₁ P₂ : E[X]}
    (hP : P₁ * P₂ ∈ Ell E n) {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ᶠ w in cofinite, f w = (KL n w : Set (UL n w)).indicator 1)
    (h : ∏ᶠ w ∈ S, kapOrb n w (atPl w P₁) (atPl w P₂) (f w) ≠ 0) :
    ∀ w ∈ S, ∃ y : UL n w, f w y ≠ 0 ∧ y.1.val.charpoly = atPl w (P₁ * P₂) := by
  intro w hw
  have h1 : ∀ᶠ w in cofinite, kapOrb n w (atPl w P₁) (atPl w P₂) (f w) = 1 := by
    filter_upwards [ae_good hU hn hS hP hf] with w hw
    obtain ⟨⟨c, hc, hc'⟩, h2⟩ := hw
    rw [kapOrb_eq w rfl, finsum_eq_single _ c]
    · rw [(h2 c).1, if_pos hc, (h2 c).2 hc _ (dvd_mul_right _ _), mul_one]
    · intro x hx
      rw [(h2 x).1, if_neg fun hg => hx (hc' x hg), mul_zero]
  have h2 := ne_zero_of_finprod h1 h w hw
  rw [kapOrb_eq w rfl] at h2
  obtain ⟨c, hc⟩ : ∃ c : LocCl n (P₁ * P₂) w, twOrb (MonoidHom.id _) (KL n w) c.1.rep (f w) ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [hc] at h2
  obtain ⟨g, hg⟩ := exists_ne_zero_of_twOrb _ _ _ hc
  exact ⟨_, hg, (charpoly_conj _ _).trans c.2⟩

theorem orb_support (hU : Unr E) (hn : 1 ≤ n) {S : Set (Pl E)} (hS : IsSection S) {γ : UE E n}
    (hP : γ.1.val.charpoly ∈ Ell E n) {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ᶠ w in cofinite, f w = (KL n w : Set (UL n w)).indicator 1)
    (h : ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w) ≠ 0) :
    ∀ w ∈ S, ∃ y : UL n w, f w y ≠ 0 ∧ y.1.val.charpoly = atPl w γ.1.val.charpoly := by
  intro w hw
  have h1 : ∀ᶠ w in cofinite, twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w) = 1 := by
    filter_upwards [hf, GlobalTheory.T.orbitalIntegral_unitIndicator_eventually_oneClass E hU n hn S hS _ hP, (GlobalTheory.T.local_points_integral_almost_all E hU n γ).2.1] with w h1 h2 h3
    rw [h1, (h2 _ (charpoly_locPt hU w γ)).1, if_pos ⟨1, by simpa using h3⟩]
  obtain ⟨g, hg⟩ := exists_ne_zero_of_twOrb _ _ _ (ne_zero_of_finprod h1 h w hw)
  exact ⟨_, hg, (charpoly_conj _ _).trans (charpoly_locPt hU w γ)⟩

theorem ell_of_dvd {P Q : E[X]} (hP : P ∈ Ell E n) (hQ : Q.Monic) (hQP : Q ∣ P) : Q ∈ Ell E Q.natDegree := by
  refine ⟨hQ, rfl, hP.2.2.1.of_dvd hQP, fun τ z hz => hP.2.2.2 τ z ?_⟩
  have h0 : P.map τ ≠ 0 := (hP.1.map τ).ne_zero
  exact Multiset.mem_of_le (Polynomial.roots.le_of_dvd h0 (Polynomial.map_dvd τ hQP)) hz

theorem csr_at (hU : Unr E) {P Q : E[X]} (hP : P ∈ Ell E n) (hQ : Q.Monic) (hQP : Q ∣ P) (w : Pl E) :
    IsCsr w (atPl w Q) := by
  by_cases hs : IsSplitAt w
  · exact Or.inl hs
  right
  have hg := (GlobalTheory.T.elliptic_charpoly_self_reciprocal E Q.natDegree Q (ell_of_dvd hP hQ hQP)).2
  have hc := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs).1
  have hcomp : (algebraMap E (w.adicCompletion E)).comp (IsCMField.complexConj E).toRingEquiv.toRingHom =
      (cj w).comp (algebraMap E (w.adicCompletion E)) := by
    exact RingHom.ext fun x => (hc x).symm
  have h1 := congrArg (Polynomial.map (algebraMap E (w.adicCompletion E))) hg
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.reverse, ← Polynomial.reflect_map, Polynomial.map_map, hcomp,
    ← Polynomial.map_map] at h1
  have hd1 : (Q.map (IsCMField.complexConj E).toRingEquiv.toRingHom).natDegree = ((atPl w Q).map (cj w)).natDegree := by
    rw [(hQ.map _).natDegree_map, hQ.natDegree_map, hQ.natDegree_map]
  rw [hd1] at h1
  rw [Polynomial.reverse, ← h1, atPl, Polynomial.coeff_map]
  congr 2
  exact hc _

theorem cls_conj {G : Type} [Group G] (x g : G) : cls (g⁻¹ * x * g) = cls x :=
  ((cls_eq_iff _ _).2 ⟨g⁻¹, by group⟩)

theorem isSplit_of_not_mem {S : Set (Pl E)} (hS : IsSection S) {w : Pl E} (hw : w ∉ S) : IsSplitAt w := by
  obtain ⟨u, ⟨hu, hu'⟩, -⟩ := hS w
  exact ⟨u, fun h => hw (h ▸ hu), hu'⟩

abbrev Fac (P : E[X]) : Type := {p : E[X] × E[X] // p.1.Monic ∧ p.2.Monic ∧ p.1 * p.2 = P}

theorem sign_mul (hU : Unr E) (hn : 1 ≤ n) {P Q₁ Q₂ : E[X]} (hP : P ∈ Ell E n) (h1 : Q₁.Monic) (h2 : Q₂.Monic)
    (h12 : Q₁ * Q₂ ∣ P) (hc : IsCoprime Q₁ Q₂) (w : Pl E) (γ : UL n w) (hγ : γ.1.val.charpoly = atPl w P) :
    kapSign n w (atPl w (Q₁ * Q₂)) γ.1 = kapSign n w (atPl w Q₁) γ.1 * kapSign n w (atPl w Q₂) γ.1 := by
  have d1 : Q₁ ∣ P := dvd_trans (dvd_mul_right _ _) h12
  have d2 : Q₂ ∣ P := dvd_trans (dvd_mul_left _ _) h12
  have hcw : IsCoprime (atPl w Q₁) (atPl w Q₂) := by
    have := hc.map (Polynomial.mapRingHom (algebraMap E (w.adicCompletion E)))
    simpa only [Polynomial.coe_mapRingHom] using this
  have hd : atPl w Q₁ * atPl w Q₂ ∣ γ.1.val.charpoly := by
    rw [hγ, atPl, atPl, atPl, ← Polynomial.map_mul]
    exact Polynomial.map_dvd _ h12
  have hs : γ.1.val.charpoly.Separable := by
    rw [hγ]
    exact atPl_separable hP w
  have key := (GlobalTheory.T.kappa_sign_multiplicative E hU n hn w (atPl w Q₁) (atPl w Q₂) 1 γ 1 hs hd hcw (csr_at hU hP h1 d1 w)
    (csr_at hU hP h2 d2 w)).1
  have e : atPl w (Q₁ * Q₂) = atPl w Q₁ * atPl w Q₂ := Polynomial.map_mul _
  rw [e]
  exact key

def locCl (hU : Unr E) {P : E[X]} (r : {c : TwCl (MonoidHom.id (UE E n)) // c.rep.1.val.charpoly = P}) (w : Pl E) :
    LocCl n P w :=
  ⟨cls (locPt w r.1.rep), (charpoly_cls _).trans ((charpoly_locPt hU w _).trans (by rw [r.2]))⟩

set_option maxHeartbeats 800000 in
theorem signs (hU : Unr E) (hn : 1 ≤ n) {S : Set (Pl E)} (hS : IsSection S) {P : E[X]} (hP : P ∈ Ell E n)
    (hgs : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ c : LocCl n P w, Good w c → ∀ Q : E[X], Q ∣ P →
      kapSign n w (atPl w Q) c.1.rep.1 = 1)
    (x : ∀ w, LocCl n P w) (hx : ∀ᶠ w in (cofinite : Filter (Pl E)), Good w (x w)) :
    ∑ᶠ d : Fac P, ∏ᶠ w ∈ S, kapSign n w (atPl w d.1.1) (x w).1.rep.1 =
      if ∃ r, ∀ w ∈ S, locCl hU r w = x w then 2 ^ nfac P else 0 := by
  have hsep : ∀ w : Pl E, (atPl w P).Separable := atPl_separable hP
  let σ : E[X] → ℂ := fun Q => ∏ᶠ w ∈ S, kapSign n w (atPl w Q) (x w).1.rep.1
  have hsepx : ∀ w, (x w).1.rep.1.val.charpoly.Separable := fun w => by rw [(x w).2]; exact hsep w
  have hmfin : ∀ Q : E[X], Q ∣ P → (S ∩ Function.mulSupport fun w => kapSign n w (atPl w Q) (x w).1.rep.1).Finite := by
    intro Q hQ
    have h : ∀ᶠ w in (cofinite : Filter (Pl E)), kapSign n w (atPl w Q) (x w).1.rep.1 = 1 := by
      filter_upwards [hx, hgs] with w h1 h2
      exact h2 (x w) h1 Q hQ
    exact (Filter.eventually_cofinite.1 h).subset Set.inter_subset_right
  have hmul : ∀ Q₁ Q₂ : E[X], Q₁.Monic → Q₂.Monic → Q₁ * Q₂ ∣ P → IsCoprime Q₁ Q₂ → σ (Q₁ * Q₂) = σ Q₁ * σ Q₂ := by
    intro Q₁ Q₂ h1 h2 h12 hc
    have d1 : Q₁ ∣ P := dvd_trans (dvd_mul_right _ _) h12
    have d2 : Q₂ ∣ P := dvd_trans (dvd_mul_left _ _) h12
    show ∏ᶠ w ∈ S, _ = (∏ᶠ w ∈ S, _) * ∏ᶠ w ∈ S, _
    rw [← finprod_mem_mul_distrib' (hmfin Q₁ d1) (hmfin Q₂ d2)]
    refine finprod_mem_congr rfl fun w _ => ?_
    exact sign_mul hU hn hP h1 h2 h12 hc w _ (x w).2
  have hpm : ∀ Q : E[X], Q.Monic → Q ∣ P → σ Q = 1 ∨ σ Q = -1 := by
    intro Q _ _
    refine finprod_mem_induction (fun z : ℂ => z = 1 ∨ z = -1) (Or.inl rfl) ?_ ?_
    · rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
    · intro w _
      exact (GlobalTheory.T.kappa_sign_multiplicative E hU n hn w 1 1 (atPl w Q) (x w).1.rep 1 (hsepx w) (by simp) isCoprime_one_left
        (csr_one w) (csr_one w)).2.2
  have hdiv := (GlobalTheory.T.monic_divisor_sign_sum E P hP.1 hP.2.2.1 σ hmul hpm).2
  have hbij : Function.Bijective (fun d : Fac P => (⟨d.1.1, d.2.1, ⟨d.1.2, d.2.2.2.symm⟩⟩ :
      {Q : E[X] // Q.Monic ∧ Q ∣ P})) := by
    refine ⟨fun d d' h => ?_, fun Q => ?_⟩
    · have h1 : d.1.1 = d'.1.1 := congrArg Subtype.val h
      have h2 : d.1.2 = d'.1.2 := by
        have e := d.2.2.2.trans d'.2.2.2.symm
        rw [h1] at e
        exact mul_left_cancel₀ (d'.2.1.ne_zero) e
      exact Subtype.ext (Prod.ext h1 h2)
    · obtain ⟨R, hR⟩ := Q.2.2
      exact ⟨⟨(Q.1, R), Q.2.1, Q.2.1.of_mul_monic_left (hR ▸ hP.1), hR.symm⟩, rfl⟩
  have hsum : ∑ᶠ d : Fac P, ∏ᶠ w ∈ S, kapSign n w (atPl w d.1.1) (x w).1.rep.1 =
      ∑ᶠ Q : {Q : E[X] // Q.Monic ∧ Q ∣ P}, σ Q.1 :=
    finsum_comp_equiv (Equiv.ofBijective _ hbij) (f := fun Q : {Q : E[X] // Q.Monic ∧ Q ∣ P} => σ Q.1)
  have key : (∀ Q : E[X], Q.Monic → Q ∣ P → σ Q = 1) ↔ ∃ r, ∀ w ∈ S, locCl hU r w = x w := by
    constructor
    · intro hall
      let y : ∀ w, UL n w := fun w =>
        if h : Good w (x w) then h.choose⁻¹ * (x w).1.rep * h.choose else (x w).1.rep
      have hy1 : ∀ w, ∃ g, y w = g⁻¹ * (x w).1.rep * g := by
        intro w
        by_cases h : Good w (x w)
        · exact ⟨_, dif_pos h⟩
        · exact ⟨1, by rw [show y w = (x w).1.rep from dif_neg h]; group⟩
      have hyP : ∀ w, (y w).1.val.charpoly = atPl w P := by
        intro w
        obtain ⟨g, hg⟩ := hy1 w
        rw [hg, charpoly_conj, (x w).2]
      have hyK : ∀ᶠ w in (cofinite : Filter (Pl E)), y w ∈ KL n w := by
        filter_upwards [hx] with w h
        rw [show y w = _ from dif_pos h]
        exact h.choose_spec
      have hyS : ∀ P₁ : E[X], P₁.Monic → P₁ ∣ P → ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (y w).1 = 1 := by
        intro P₁ h1 h2
        rw [← hall P₁ h1 h2]
        refine finprod_mem_congr rfl fun w _ => ?_
        obtain ⟨g, hg⟩ := hy1 w
        rw [hg]
        exact kapSign_conj hU hn _ _ _ (hsepx w)
      obtain ⟨γ, hγP, hγ⟩ := (GlobalTheory.T.unitary_conjugacy_sign_product E hU n hn S hS P hP).2.2 y hyP hyK hyS
      obtain ⟨h, hh⟩ := rep_cls γ
      refine ⟨⟨cls γ, by rw [hh, charpoly_conj', hγP]⟩, fun w hw => ?_⟩
      apply Subtype.ext
      show cls (locPt w (cls γ).rep) = (x w).1
      obtain ⟨g, hg⟩ := hγ w hw
      obtain ⟨k, hk⟩ := hy1 w
      rw [hh, locPt_conj hU, cls_conj, hg, cls_conj, hk, cls_conj, cls_rep]
    · rintro ⟨r, hr⟩ Q hQ hQP
      rw [← (GlobalTheory.T.unitary_conjugacy_sign_product E hU n hn S hS P hP).2.1 r.1.rep r.2 Q hQ hQP]
      refine finprod_mem_congr rfl fun w hw => ?_
      have e : (x w).1 = cls (locPt w r.1.rep) := (congrArg Subtype.val (hr w hw)).symm
      obtain ⟨g, hg⟩ := rep_cls (locPt w r.1.rep)
      have hs' : (locPt w r.1.rep).1.val.charpoly.Separable := by
        rw [charpoly_locPt hU, r.2]
        exact hsep w
      rw [e, hg]
      exact kapSign_conj hU hn _ _ _ hs'
  rw [hsum, hdiv]
  by_cases h : ∀ Q : E[X], Q.Monic → Q ∣ P → σ Q = 1
  · rw [if_pos h, if_pos (key.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (key.2 h'))]

set_option maxHeartbeats 800000 in
theorem fixedP (hU : Unr E) (hn : 1 ≤ n) {S : Set (Pl E)} (hS : IsSection S) {P : E[X]} (hP : P ∈ Ell E n)
    {K' : ∀ w : Pl E, Subgroup (UL n w)} (hK' : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K')
    {f : ∀ w : Pl E, UL n w → ℂ} (hf : IsTest (KL n) K' f) :
    (Function.support fun c : TwCl (MonoidHom.id (UE E n)) => if c.rep.1.val.charpoly = P then
      ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w c.rep) (f w) else 0).Finite ∧
    (∑ᶠ c : TwCl (MonoidHom.id (UE E n)), if c.rep.1.val.charpoly = P then
      ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w c.rep) (f w) else 0) * 2 ^ nfac P =
    ∑ᶠ p : E[X] × E[X], if p.1.Monic ∧ p.2.Monic ∧ p.1 * p.2 = P then
      ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w) else 0 := by
  have hsep : ∀ w : Pl E, (atPl w P).Separable := atPl_separable hP
  haveI : ∀ w, Finite (LocCl n P w) := fun w =>
    ((GlobalTheory.T.finite_twisted_classes_charpoly E hU n w (atPl w P) (hsep w)).2).to_subtype
  have hdivs := (GlobalTheory.T.monic_divisor_sign_sum E P hP.1 hP.2.2.1 (fun _ => 1) (fun _ _ _ _ _ _ => by simp) (fun _ _ _ => Or.inl rfl)).1
  have hP0 : P ≠ 0 := hP.1.ne_zero
  haveI : Finite (Fac P) := by
    haveI := hdivs.to_subtype
    refine Finite.of_injective (fun d : Fac P => (⟨d.1.1, d.2.1, ⟨d.1.2, d.2.2.2.symm⟩⟩ :
      {Q : E[X] | Q.Monic ∧ Q ∣ P})) fun d d' h => ?_
    have h1 : d.1.1 = d'.1.1 := congrArg Subtype.val h
    have h2 : d.1.2 = d'.1.2 := by
      have e := d.2.2.2.trans d'.2.2.2.symm
      rw [h1] at e
      exact mul_left_cancel₀ (d'.2.1.ne_zero) e
    exact Subtype.ext (Prod.ext h1 h2)
  have hKc : ∀ w, IsCompact (KL n w : Set (UL n w)) := fun w => (GlobalTheory.T.localTwist_continuous_involution_integral_properties E hU n w).2.2.2.2.2.2.2.1
  have hgood := ae_good hU hn hS hP hf.2
  have E1 := GlobalTheory.T.adelic_class_count_product (Pl E) S (LocCl n P) (Fac P) {c : TwCl (MonoidHom.id (UE E n)) // c.rep.1.val.charpoly = P}
    (locCl hU) (fun w c => twOrb (MonoidHom.id _) (KL n w) c.1.rep (f w))
    (fun d w c => kapSign n w (atPl w d.1.1) c.1.rep.1) (fun w c => Good w c) (2 ^ nfac P) ?h1 ?h2 ?h3 ?h4 ?h5
  case h1 =>
    filter_upwards [hgood] with w hw
    exact ⟨hw.1, fun c => ⟨(hw.2 c).1, fun hc d => (hw.2 c).2 hc _ ⟨d.1.2, d.2.2.2.symm⟩⟩⟩
  case h2 =>
    intro w hw
    obtain ⟨y, hy⟩ := (GlobalTheory.T.elliptic_charpoly_local_realisation E hU n P hP).2 w (isSplit_of_not_mem hS hw)
    exact ⟨⟨cls y, (charpoly_cls y).trans hy⟩⟩
  case h3 =>
    intro r
    filter_upwards [(GlobalTheory.T.local_points_integral_almost_all E hU n r.1.rep).2.1] with w hw
    obtain ⟨g, hg⟩ := rep_cls (locPt w r.1.rep)
    refine ⟨g⁻¹, ?_⟩
    show g⁻¹⁻¹ * (cls (locPt w r.1.rep)).rep * g⁻¹ ∈ KL n w
    rw [hg]
    simpa [mul_assoc] using hw
  case h4 =>
    intro r r' h
    have := (GlobalTheory.T.unitary_conjugacy_sign_product E hU n hn S hS P hP).1 r.1.rep r'.1.rep r.2 r'.2 fun w hw => by
      have e := congrArg Subtype.val (h w hw)
      exact (cls_eq_iff _ _).1 e
    obtain ⟨g, hg⟩ := this
    apply Subtype.ext
    rw [← cls_rep r.1, ← cls_rep r'.1]
    exact (cls_eq_iff _ _).2 ⟨g, hg⟩
  case h5 =>
    intro x hx
    exact signs hU hn hS hP (by filter_upwards [hgood] with w hw; exact fun c hc => (hw.2 c).2 hc) x hx
  obtain ⟨Efin, Eeq⟩ := E1
  have hO : ∀ r : {c : TwCl (MonoidHom.id (UE E n)) // c.rep.1.val.charpoly = P},
      ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locCl hU r w).1.rep (f w) =
      ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w r.1.rep) (f w) := by
    intro r
    refine finprod_mem_congr rfl fun w _ => ?_
    obtain ⟨g, hg⟩ := rep_cls (locPt w r.1.rep)
    show twOrb _ _ (cls (locPt w r.1.rep)).rep _ = _
    rw [hg, twOrb_conj (hKc w) (hK'.1 w) (hf.1 w)]
  simp only [hO] at Efin Eeq
  have hR : ∀ u : TwCl (MonoidHom.id (UE E n)) → ℂ,
      ∑ᶠ r : {c : TwCl (MonoidHom.id (UE E n)) // c.rep.1.val.charpoly = P}, u r.1 =
      ∑ᶠ c, if c.rep.1.val.charpoly = P then u c else 0 := fun u => finsum_subtype_if _ u
  refine ⟨?_, ?_⟩
  · refine (Efin.image Subtype.val).subset fun c hc => ?_
    by_cases h : c.rep.1.val.charpoly = P
    · refine ⟨⟨c, h⟩, ?_, rfl⟩
      simpa [h] using hc
    · exact absurd (by simp [h]) hc
  · rw [← hR (fun c => ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w c.rep) (f w)), Eeq]
    rw [← finsum_subtype_if (fun p : E[X] × E[X] => p.1.Monic ∧ p.2.Monic ∧ p.1 * p.2 = P)]
    refine finsum_congr fun d => finprod_mem_congr rfl fun w _ => ?_
    rw [kapOrb_eq w d.2.2.2]

theorem coprime_of_sep {k : Type} [Field k] {p q : k[X]} (h : (p * q).Separable) : IsCoprime p q := by
  refine isCoprime_of_dvd _ _ ?_ fun z hz _ hzp hzq => ?_
  · rintro ⟨rfl, -⟩
    rw [zero_mul] at h
    exact Polynomial.not_separable_zero h
  · exact (mem_nonunits_iff.1 hz) (h.squarefree z (mul_dvd_mul hzp hzq))

theorem fac_finite {P : E[X]} (hP : P ∈ Ell E n) :
    {p : E[X] × E[X] | p.1.Monic ∧ p.2.Monic ∧ p.1 * p.2 = P}.Finite := by
  have hdivs := (GlobalTheory.T.monic_divisor_sign_sum E P hP.1 hP.2.2.1 (fun _ => 1) (fun _ _ _ _ _ _ => by simp) (fun _ _ _ => Or.inl rfl)).1
  refine (hdivs.image fun Q => (Q, P /ₘ Q)).subset fun p hp => ⟨p.1, ⟨hp.1, ⟨p.2, hp.2.2.symm⟩⟩, ?_⟩
  refine Prod.ext rfl ?_
  show P /ₘ p.1 = p.2
  rw [← hp.2.2]
  exact Polynomial.mul_divByMonic_cancel_left _ hp.1

theorem geomURat_eq_geomU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)),
    IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f →
    (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) →
    geomURat lam (fun γ => ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w)) = geomU S lam f := by
  intro E _ _ _ hU n hn S hS lam K' hK' f hf _
  have hFin := GlobalTheory.T.finite_elliptic_charpolys_support E hU n S hS f (fun w => (hf.1 w).1) hf.2
  let F := hFin.toFinset
  have hmemF : ∀ P, P ∈ F ↔ P ∈ Ell E n ∧ ∀ w ∈ S, ∃ y : UL n w, f w y ≠ 0 ∧ y.1.val.charpoly = atPl w P :=
    fun P => hFin.mem_toFinset
  let orb : UE E n → ℂ := fun γ => ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w)

  have hL : geomURat lam orb = ∑ P ∈ F, kap P * chW lam P *
      ((∑ᶠ c : TwCl (MonoidHom.id (UE E n)), if c.rep.1.val.charpoly = P then orb c.rep else 0) * 2 ^ nfac P) := by
    have hterm : ∀ c : TwCl (MonoidHom.id (UE E n)), (if c.rep.1.val.charpoly.Separable then
        mass (MonoidHom.id _) (ratFinU E n) (finPt c.rep) * chW lam c.rep.1.val.charpoly * orb c.rep else 0) =
        if c.rep.1.val.charpoly ∈ Ell E n then kap c.rep.1.val.charpoly * 2 ^ nfac c.rep.1.val.charpoly *
          chW lam c.rep.1.val.charpoly * orb c.rep else 0 := by
      intro c
      by_cases h : c.rep.1.val.charpoly.Separable
      · have he := (GlobalTheory.T.local_points_integral_almost_all E hU n c.rep).2.2 h
        rw [if_pos h, if_pos he, GlobalTheory.T.unitary_mass_formula E hU n hn c.rep he]
      · rw [if_neg h, if_neg fun h' => h h'.2.2.1]
    have hsupp : ∀ c : TwCl (MonoidHom.id (UE E n)), (if c.rep.1.val.charpoly ∈ Ell E n then
        kap c.rep.1.val.charpoly * 2 ^ nfac c.rep.1.val.charpoly * chW lam c.rep.1.val.charpoly * orb c.rep else 0) ≠ 0 →
        c.rep.1.val.charpoly ∈ F ∧ orb c.rep ≠ 0 := by
      intro c hc
      by_cases h : c.rep.1.val.charpoly ∈ Ell E n
      · rw [if_pos h] at hc
        have ho : orb c.rep ≠ 0 := right_ne_zero_of_mul hc
        exact ⟨(hmemF _).2 ⟨h, orb_support hU hn hS h hf.2 ho⟩, ho⟩
      · rw [if_neg h] at hc
        exact absurd rfl hc
    unfold geomURat
    rw [finsum_congr hterm, finsum_fibres _ (fun c => c.rep.1.val.charpoly) F ?_ fun c hc => (hsupp c hc).1]
    · refine Finset.sum_congr rfl fun P hP => ?_
      have hPE : P ∈ Ell E n := ((hmemF P).1 hP).1
      rw [mul_comm _ ((2 : ℂ) ^ nfac P), ← mul_assoc, mul_finsum]
      refine finsum_congr fun c => ?_
      by_cases h : c.rep.1.val.charpoly = P
      · rw [if_pos h, if_pos h, h, if_pos hPE]
        ring
      · rw [if_neg h, if_neg h, mul_zero]
    · refine ((F.finite_toSet.biUnion fun P hP => (fixedP hU hn hS ((hmemF P).1 hP).1 hK' hf).1)).subset fun c hc => ?_
      obtain ⟨h1, h2⟩ := hsupp c hc
      exact Set.mem_biUnion h1 (by simp only [Function.mem_support, if_pos rfl]; exact h2)

  let A : Set (E[X] × E[X]) := {p | p.1.Monic ∧ p.2.Monic ∧ p.1 * p.2 ∈ Ell E n}
  let V : E[X] × E[X] → ℂ := fun p => if p ∈ A then kap (p.1 * p.2) * chW lam (p.1 * p.2) *
    ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w) else 0
  have hVs : ∀ p, V p ≠ 0 → p.1 * p.2 ∈ F ∧ p ∈ A := by
    intro p hp
    by_cases h : p ∈ A
    · have hp' : kap (p.1 * p.2) * chW lam (p.1 * p.2) * ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w) ≠ 0 := by
        simpa only [V, if_pos h] using hp
      exact ⟨(hmemF _).2 ⟨h.2.2, kapOrb_support hU hn hS h.2.2 hf.2 (right_ne_zero_of_mul hp')⟩, h⟩
    · exact absurd (by simp only [V, if_neg h]) hp
  have hVfin : (Function.support V).Finite := by
    refine (F.finite_toSet.biUnion fun P hP => fac_finite ((hmemF P).1 hP).1).subset fun p hp => ?_
    obtain ⟨h1, h2⟩ := hVs p hp
    exact Set.mem_biUnion h1 ⟨h2.1, h2.2.1, rfl⟩
  have hA : ∀ a ∈ Finset.range (n + 1), ∀ p : E[X] × E[X],
      p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E (n - a) ∧ IsCoprime p.1 p.2} ↔ p ∈ A ∧ p.1.natDegree = a := by
    intro a ha p
    have han : a ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
    constructor
    · rintro ⟨h1, h2, hc⟩
      have := (GlobalTheory.T.kappaConstant_mul_of_coprime_ellipticPolynomials E hU a (n - a) p.1 p.2 h1 h2 hc).2.2
      rw [Nat.add_sub_cancel' han] at this
      exact ⟨⟨h1.1, h2.1, this⟩, h1.2.1⟩
    · rintro ⟨⟨m1, m2, he⟩, hd⟩
      have hdeg : p.1.natDegree + p.2.natDegree = n := by
        rw [← he.2.1, Polynomial.natDegree_mul m1.ne_zero m2.ne_zero]
      have e1 := ell_of_dvd he m1 (dvd_mul_right _ _)
      have e2 := ell_of_dvd he m2 (dvd_mul_left _ _)
      rw [hd] at e1
      rw [show p.2.natDegree = n - a by omega] at e2
      exact ⟨e1, e2, coprime_of_sep he.2.2.1⟩
  have hR : geomU S lam f = ∑ P ∈ F, kap P * chW lam P * ∑ᶠ p : E[X] × E[X],
      if p.1.Monic ∧ p.2.Monic ∧ p.1 * p.2 = P then ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w) else 0 := by
    unfold geomU
    have h1 : ∀ a ∈ Finset.range (n + 1),
        (∑ᶠ p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E (n - a) ∧ IsCoprime p.1 p.2},
          kap (p.1 * p.2) * chW lam (p.1 * p.2) * ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w)) =
        ∑ᶠ p : E[X] × E[X], if p.1.natDegree = a then V p else 0 := by
      intro a ha
      rw [finsum_mem_def]
      refine finsum_congr fun p => ?_
      rw [Set.indicator_apply]
      by_cases h : p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E (n - a) ∧ IsCoprime p.1 p.2}
      · obtain ⟨hpA, hd⟩ := (hA a ha p).1 h
        rw [if_pos h, if_pos hd]
        simp only [V, if_pos hpA]
      · rw [if_neg h]
        by_cases hd : p.1.natDegree = a
        · rw [if_pos hd]
          have hpA : p ∉ A := fun hpA => h ((hA a ha p).2 ⟨hpA, hd⟩)
          simp only [V, if_neg hpA]
        · rw [if_neg hd]
    rw [Finset.sum_congr rfl h1, ← finsum_sum_comm]
    · have h2 : ∀ p : E[X] × E[X], ∑ a ∈ Finset.range (n + 1), (if p.1.natDegree = a then V p else 0) = V p := by
        intro p
        rw [Finset.sum_ite_eq]
        split_ifs with h
        · rfl
        · by_contra hV
          obtain ⟨-, hpA⟩ := hVs p (Ne.symm hV)
          apply h
          have hdeg : p.1.natDegree + p.2.natDegree = n := by
            rw [← hpA.2.2.2.1, Polynomial.natDegree_mul hpA.1.ne_zero hpA.2.1.ne_zero]
          exact Finset.mem_range.2 (by omega)
      rw [finsum_congr h2, finsum_fibres V (fun p => p.1 * p.2) F hVfin fun p hp => (hVs p hp).1]
      refine Finset.sum_congr rfl fun P hP => ?_
      have hPE : P ∈ Ell E n := ((hmemF P).1 hP).1
      rw [mul_finsum]
      refine finsum_congr fun p => ?_
      by_cases h : p.1 * p.2 = P
      · by_cases hm : p.1.Monic ∧ p.2.Monic
        · have hpA : p ∈ A := ⟨hm.1, hm.2, h ▸ hPE⟩
          rw [if_pos h, if_pos ⟨hm.1, hm.2, h⟩]
          simp only [V, if_pos hpA, h]
        · have hpA : p ∉ A := fun hpA => hm ⟨hpA.1, hpA.2.1⟩
          rw [if_pos h, if_neg fun h' => hm ⟨h'.1, h'.2.1⟩, mul_zero]
          simp only [V, if_neg hpA]
      · rw [if_neg h, if_neg fun h' => h h'.2.2, mul_zero]
    · intro a _
      refine hVfin.subset fun p hp => ?_
      by_contra h0
      apply hp
      simp only [Function.mem_support, not_not] at h0
      simp [h0]
  rw [hR]
  show geomURat lam orb = _
  rw [hL]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [(fixedP hU hn hS ((hmemF P).1 hP).1 hK' hf).2]

end GlobalTheory.PreStabU
end
end
