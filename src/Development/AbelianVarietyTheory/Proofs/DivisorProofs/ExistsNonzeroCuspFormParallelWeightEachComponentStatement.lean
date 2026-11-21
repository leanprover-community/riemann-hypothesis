import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesOnEqModel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsProductCuspFormNeZeroArchSupNormBounds
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsRunBound
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsEvenSecEvRNeZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OrthonormalFramesBoundedOfDefinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupAtUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSectionThetaKeyRuleWeightFour
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionFourthRootPerComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionNormComplexPointsEqTwoPiPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemCuspFormsOfBoundedSectionComponent
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.WeightEqZeroOfOneIsSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspNe

section
set_option autoImplicit false

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.ScalarCuspTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem cuspW_congr {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G G' : WTZ E}
    (h : exZ Dw G = exZ Dw G') : cuspW Xo c U G = cuspW Xo c U G' := by
  ext f
  rw [mem_cuspW, mem_cuspW, h]
  exact and_congr_right fun _ => forall₂_congr fun σ hσ => by rw [modelWt_congr (U σ) hσ (hU σ hσ) h]

theorem wtOf_four_fst (τ : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult τ) : (wtOf Dw 0 4).1 (τ, i) = -4 := by
  unfold Datum.mult at hi
  by_cases h : τ (H.rt : E) = H.rt0
  · rw [if_pos h] at hi
    simp only [wtOf, dif_pos h, dif_pos hi, Pi.zero_apply, zero_sub]
  · rw [if_neg h] at hi
    have h' : conjEmb τ (H.rt : E) = H.rt0 := conj_mem h
    simp only [wtOf, dif_neg h, dif_pos h', dif_pos hi, Pi.zero_apply, neg_zero, zero_sub]

theorem exZ_four_add (n : ℕ) :
    exZ Dw (wtZ (fun _ => 4) n + wtOf Dw 0 4) = exZ Dw (wtZ 0 (n + 8)) := by
  funext i
  rcases i with _ | ⟨τ, i⟩
  · show ((n : ℤ) + 2 * 4) = ((n + 8 : ℕ) : ℤ)
    push_cast; ring
  · show ((4 : ℕ) : ℤ) + (wtOf Dw 0 4).1 (τ, i) = ((0 : ℕ) : ℤ)
    rw [wtOf_four_fst τ i i.2]
    simp

theorem exists_twist {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) (Z : Comp Xo c) :
    ∃ s : Rul Xo c, (∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * s ∈ cuspOn U Z (G + wtOf Dw 0 4)) ∧
      ∀ σ, GoodEmb c σ → ∀ z ∈ framesOn (U σ) Z, rdU (U σ) s z.1 z.2 ≠ 0 := by
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := GlobalTheory.KeyFourth.exists_unit_secZ_keyRule κ k₁ k₂ k₆ E H Dw l Xo c _ e hL.pos
  have hσ0 : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨ρ, -⟩ := GlobalTheory.KeyRoot.exists_keySec_pow_four κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hL.unf _ hσ0)
    hL.geo hL.pos hKmem hKval
  have hadd : wtOf Dw 0 4 + wtOf Dw 0 (-4) = 0 := by
    rw [← wtOf_add, add_zero, add_neg_cancel, wtOf_zero]
  have hex : exZ Dw (wtOf Dw 0 4) = -((4 : ℤ) • GlobalTheory.ShFam.keyEx Dw) := by
    rw [← GlobalTheory.KeyArchNorm.exZ_wtOf, ← GlobalTheory.FlatTw.exZ_neg_eq, neg_eq_of_add_eq_zero_left hadd]
  set s : Rul Xo c := idem Z * ((K⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) with hs
  have hsm : s ∈ secZ Xo c (exZ Dw (wtOf Dw 0 4)) := by
    have := mul_mem_secZ (idem_mem_secZ Z) (inv_mem_secZ hKmem)
    rwa [zero_add, ← hex] at this
  have hsupp : s ∈ suppOn Z := by rw [hs, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hsK : s * (K : Rul Xo c) = idem Z := by rw [hs, mul_assoc, Units.inv_mul, mul_one]
  have hnorm : ∀ σ, GoodEmb c σ → ∃ C : ℝ, 0 < C ∧ ∀ z ∈ framesOn (U σ) Z,
      homN (U σ) x (wtOf Dw 0 4) s z * C = 1 := by
    intro σ hσ
    obtain ⟨C, hC0, -, hC⟩ := GlobalTheory.KeyArchNorm.homN_key_const κ k₁ k₂ k₅ E H Dw l Xo c _ e σ r (U σ) x K hσ (hL.unf σ hσ)
      (hL.xi σ hσ) ⟨ρ⟩ hL.pos hKmem hKval
    refine ⟨C, hC0, fun z hz => ?_⟩
    obtain ⟨hy, hlies⟩ := hz
    have h1 : homN (U σ) x (wtOf Dw 0 (-4)) (K : Rul Xo c) z = C := hC z.1 z.2 hy
    have ht := tested_of_homN_ne (U σ) x hy (h1.trans_ne hC0.ne')
    rw [← h1, ← homN_mul (U σ) x (even_wtOf _ _) (even_wtOf _ _) _ _ z hy, hadd, hsK]
    exact homN_idem (U σ) x hy hlies ht
  refine ⟨s, GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z (wtOf Dw 0 4) s ⟨ρ⟩ hL.unf hL.pos (even_wtOf _ _)
    (fun τ i j hij hj => by rw [wtOf_four_fst τ j hj, wtOf_four_fst τ i (hij.trans_lt hj)]) hsm hsupp
    (fun σ hσ => ?_), fun σ hσ z hz h0 => ?_⟩
  · obtain ⟨C, hC0, hC⟩ := hnorm σ hσ
    exact ⟨C⁻¹, fun z hz => (eq_inv_of_mul_eq_one_left (hC z hz)).le⟩
  · obtain ⟨C, -, hC⟩ := hnorm σ hσ
    have h3 := hC z hz
    have h4 : homN (U σ) x (wtOf Dw 0 4) s z = 0 := by
      simp [homN, ptN, Data.pnorm, h0]
    rw [h4, zero_mul] at h3
    exact zero_ne_one h3

theorem exists_scalar_of_four {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) {σ : c.F →+* ℂ}
    (hσ : GoodEmb c σ) (Z : Comp Xo c) {n : ℕ} (hn : Even n) {f : Rul Xo c} (hf : f ∈ cusp Xo c U (fun _ => 4) n)
    {z : Σ k, Frame ((U σ).X k).Ψ r} (hz : z ∈ framesOn (U σ) Z) (hne : rdU (U σ) f z.1 z.2 ≠ 0) :
    ∃ f₀ ∈ cusp Xo c U 0 (n + 8), rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  obtain ⟨s, hs, hs0⟩ := exists_twist hL Z
  obtain ⟨g, hg, -⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hL.unf Z (wtZ (fun _ => 4) n)
    ⟨f, by rw [cuspW_wtZ]; exact hf⟩
  have hev : Even (wtZ (E := E) (fun _ => 4) n).2 := by
    show Even ((n : ℕ) : ℤ)
    exact_mod_cast hn
  have h1 := (hs _ hev g g.2).1
  rw [cuspW_congr hL.unf (exZ_four_add n), cuspW_wtZ] at h1
  refine ⟨_, h1, ?_⟩
  have h2 := hs0 σ hσ z hz
  obtain ⟨hy, hlies⟩ := hz
  have e : rdU (U σ) (g : Rul Xo c) z.1 z.2 = rdU (U σ) f z.1 z.2 := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hy]
    rw [hg _ _ hlies]
  rw [AllWt.rdU_mul, Pi.mul_apply, Pi.mul_apply, e]
  exact mul_ne_zero hne h2

theorem exists_scalar_of_model {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) {σ : c.F →+* ℂ}
    (hσ : GoodEmb c σ) (Z : Comp Xo c) {n : ℕ} (hn : Even n) (hb : 4 * (finrank ℚ E * r) + 4 ≤ n)
    {k : (U σ).Comp} {y : Frame ((U σ).X k).Ψ r} (hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z)
    {P : Frame ((U σ).X k).Ψ r → ℂ} (hP : P ∈ ((U σ).X k).SS (laU (U σ) 0 (n + 8) k)) (hne : P y ≠ 0) :
    ∃ f₀ ∈ cusp Xo c U 0 (n + 8), rdU (U σ) f₀ k y ≠ 0 := by
  classical
  have hla : laU (U σ) (fun _ => 4) n = laU (U σ) 0 (n + 8) := by
    funext k' τ j
    have e : (n + 8) / 2 = n / 2 + 4 := by omega
    simp only [laU, Pi.zero_apply, e]
    split_ifs <;> push_cast <;> ring
  let P₀ : FDSec (U σ).X := Pi.single k (((U σ).X k).dom.indicator P)
  have hQ : P₀ ∈ holSub0 (U σ).X (laU (U σ) (fun _ => 4) n) := by
    rw [hla]
    refine ⟨holCusp_mem_holSub _ _ fun k' => ?_, fun k' y' hy' => ?_⟩
    · by_cases h : k' = k
      · subst h
        simp only [P₀, Pi.single_eq_same]
        exact (GlobalTheory.DomCongr.bddSec_cusp_congr E r _ _ P _ (fun x hx => (Set.indicator_of_mem hx _).symm)).2 hP
      · simp only [P₀, Pi.single_eq_of_ne h]
        exact (siegelSpaceAlgebra_holds (E := E) r ((U σ).X k') (laU (U σ) 0 (n + 8) k') (laU (U σ) 0 (n + 8) k') 0).1.1
    · by_cases h : k' = k
      · subst h
        simp only [P₀, Pi.single_eq_same]
        exact Set.indicator_of_notMem hy' _
      · simp only [P₀, Pi.single_eq_of_ne h, Pi.zero_apply]
  have hQy : P₀ k y ≠ 0 := by
    simp only [P₀, Pi.single_eq_same]
    rw [Set.indicator_of_mem hz.1]; exact hne
  have hspan := hL.onto _ hσ (fun _ => 4) n ⟨fun _ => antitone_const, hn⟩ (fun _ _ _ => by norm_num) hb hQ
  obtain ⟨f, hf, hfy⟩ : ∃ f ∈ cusp Xo c U (fun _ => 4) n, rdU (U σ) f k y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    let ev : FDSec (U σ).X →ₗ[ℂ] ℂ :=
      { toFun := fun P => P k y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hle : Submodule.span ℂ (rdU (U σ) '' (cusp Xo c U (fun _ => 4) n : Set (Rul Xo c))) ≤
        LinearMap.ker ev := by
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact hcon f hf
    exact hQy (hle hspan)
  exact exists_scalar_of_four hL hσ Z hn hf hz hfy

theorem exists_scalar_of_models
    (hP : ∀ X : Data E r, 0 < X.p0 → X.p0 < r → (∀ n : ℕ, Even n → ∀ γ ∈ X.Γ, X.χ (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) γ = 1) → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Even n ∧ ∃ P ∈ X.SS (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)), ∃ y ∈ X.dom, P y ≠ 0)
    {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) {σ : c.F →+* ℂ}
    (hσ : GoodEmb c σ) (Z : Comp Xo c) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ Even n₀ ∧ ∃ f₀ ∈ cusp Xo c U 0 n₀, ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  have hU := hL.unf σ hσ
  have hr : r = Dw.p + Dw.q := hU.1
  obtain ⟨k, hk⟩ := GlobalTheory.FlatCore.framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
  have hp0 : ((U σ).X k).p0 = Dw.q := (hU.2.1 k).1
  have hla : ∀ n : ℕ, laU (U σ) 0 n k = fun (τ : ((U σ).X k).Ψ) (j : Fin r) =>
      if ((U σ).X k).p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ) := fun n => by
    funext τ j
    simp [laU]
  obtain ⟨n, hn, hev, P, hPm, y, hy, hne⟩ := hP ((U σ).X k) (by omega) (by omega)
    (fun n hn γ hγ => by rw [← hla]; exact hL.chi σ hσ 0 n ⟨fun _ => antitone_const, hn⟩ k γ hγ)
    (4 * (finrank ℚ E * r) + 12)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  have hm : Even m := by
    obtain ⟨t, ht⟩ := hev
    exact ⟨t - 4, by omega⟩
  have hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z := by
    rw [hk]; exact ⟨rfl, hy⟩
  rw [← hla] at hPm
  obtain ⟨f, hf, hf0⟩ := exists_scalar_of_model hL hσ Z hm (by omega) hz hPm hne
  exact ⟨m + 8, by omega, hev, f, hf, ⟨k, y⟩, hz, hf0⟩

end GlobalTheory.ScalarCuspTwist
end

section
section
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD

theorem GlobalTheory.ScalarPoin.exists_cusp_ne_some : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → (∀ n : ℕ, Even n → ∀ γ ∈ X.Γ, X.χ (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) γ = 1) → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Even n ∧ ∃ P ∈ X.SS (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)), ∃ y ∈ X.dom, P y ≠ 0 := by
  intro E _ _ _ r X hp0 hpr hχ N
  obtain ⟨y, hy⟩ := GlobalTheory.FlagSecProbe.dom_nonempty X
  obtain ⟨n, hN, -, hev, P, hP, hPy⟩ := GlobalTheory.ScalarPoin.exists_cusp_ne E r X hp0 hpr hχ y hy N
  exact ⟨n, hN, hev, P, hP, y, hy, hPy⟩
end

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_cuspSection_large_evenScalarWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → (∀ n : ℕ, Even n → ∀ γ ∈ X.Γ, X.χ (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) γ = 1) → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Even n ∧ ∃ P ∈ X.SS (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)), ∃ y ∈ X.dom, P y ≠ 0 := by
  atlas_forward_decl GlobalTheory.ScalarPoin.exists_cusp_ne_some
end

section
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.ScalarCuspTwist

theorem exists_scalar_cusp_indefinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → 1 ≤ Dw.p → 1 ≤ Dw.q → ¬ (∃ m : ℕ, 1 ≤ m ∧ m ^ 4 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E ∧ (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ 16 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ (Dw.p ≤ m ∨ Dw.q ≤ m)) → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c), ∃ n₀ : ℕ, 0 < n₀ ∧ Even n₀ ∧ ∃ f₀ ∈ cusp Xo c U 0 n₀, ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U x hL hp hq _ σ hσ Z
  exact exists_scalar_of_models (GlobalTheory.T.exists_nonzero_cuspSection_large_evenScalarWeight E r) hL hp hq hσ Z

end GlobalTheory.ScalarCuspTwist
end

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalar_cuspForm_indefinite_unitaryShimura : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → 1 ≤ Dw.p → 1 ≤ Dw.q → ¬ (∃ m : ℕ, 1 ≤ m ∧ m ^ 4 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E ∧ (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ 16 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ (Dw.p ≤ m ∨ Dw.q ≤ m)) → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c), ∃ n₀ : ℕ, 0 < n₀ ∧ Even n₀ ∧ ∃ f₀ ∈ cusp Xo c U 0 n₀, ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  atlas_forward_decl GlobalTheory.ScalarCuspTwist.exists_scalar_cusp_indefinite
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.ScalarCusp

theorem bdd_of_definite {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (hp : X.p0 = 0 ∨ X.p0 = r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) :
    ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C := by
  obtain ⟨R, hR⟩ := GlobalTheory.orthonormal_frames_bounded_of_definite r X hp
  let K : Set (Frame X.Ψ r) := {x | X.IsOrtho x}
  have hKd : K ⊆ X.dom := fun x hx => PIW.FdPA.orthonormal_domain r X x hx
  have hKc : IsClosed K := by
    have e : K = ⋂ τ : X.Ψ, {x : Frame X.Ψ r | gram τ.1 X.Gm (mat x τ) =
        Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)} := by
      ext x; simp [K, Data.IsOrtho]
    rw [e]
    refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
    unfold gram hermC col mat
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.of_apply]
    fun_prop
  have hKb : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨max R 0, fun x hx => ?_⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun τ => ?_
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun a => ?_
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun b => ?_
    exact (hR x hx τ a b).trans (le_max_left _ _)
  obtain ⟨C, hC⟩ := (Metric.isCompact_of_isClosed_isBounded hKc hKb).exists_bound_of_continuousOn
    (hP.1.continuousOn.mono hKd)
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨b, hb, ho⟩ := (orthonormalFlagTranslate_holds r X).1 x hx
  rw [← (orthonormalFlagTranslate_holds r X).2.1 la P hP.2.1 x hx b hb,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit X la P (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho X ho)]
  exact hC _ ho

end GlobalTheory.ScalarCusp

namespace GlobalTheory.ScalarCusp

theorem exists_scalar_cusp_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c), ∃ n₀ : ℕ, 0 < n₀ ∧ Even n₀ ∧ ∃ f₀ ∈ cusp Xo c U 0 n₀, ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U x hL σ hσ Z
  have hU := hL.unf σ hσ
  have hr : r = Dw.p + Dw.q := hU.1
  obtain ⟨k, hk⟩ := GlobalTheory.FlatCore.framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
  by_cases hdef : Dw.p = 0 ∨ Dw.q = 0
  · obtain ⟨z, hz⟩ := GlobalTheory.FlatLine.framesOn_nonempty hU Z
    have hz' : z.1 = k ∧ z.2 ∈ ((U σ).X z.1).dom := by rw [hk] at hz; exact hz
    obtain ⟨n, hn, he, f, hf, hne⟩ :=
      GlobalTheory.Reg.exists_even_sec_evR_ne_zero E H Dw l Xo c σ ((U σ).un z.1 ⟨z.2, hz'.2⟩)
    have hD : Dom (0 : (E →+* ℂ) × ℕ → ℕ) n := ⟨fun τ i i' _ => le_rfl, he⟩
    refine ⟨n, hn, he, f, ?_, z, hz, ?_⟩
    · rw [mem_cusp]
      refine ⟨hf, fun σ' hσ' => holCusp_mem_holSub _ _ fun j => ?_⟩
      have hU' := hL.unf σ' hσ'
      have hs := hU'.2.2.2.2.1 0 n hD f hf j
      obtain ⟨τ0⟩ : Nonempty ((U σ').X j).Ψ := by
        obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
        by_cases h : τ ∈ ((U σ').X j).Ψ
        · exact ⟨⟨τ, h⟩⟩
        · exact ⟨⟨_, not_not.mp (fun h' => h ((((U σ').X j).cmType τ).mpr h'))⟩⟩
      have hp0 : ((U σ').X j).p0 = 0 ∨ ((U σ').X j).p0 = r := by
        rw [(hU'.2.1 j).1]; omega
      exact GlobalTheory.BoundedCusp.mem_SS_of_definite _ _ τ0 hp0 _ ⟨hs, bdd_of_definite _ hp0 _ _ hs⟩
    · have e : rdU (U σ) f z.1 z.2 = toC (evR Xo c f ((U σ).un z.1 ⟨z.2, hz'.2⟩)) := dif_pos hz'.2
      rw [e]
      exact hne
  · push_neg at hdef
    have hp : 1 ≤ Dw.p := Nat.one_le_iff_ne_zero.2 hdef.1
    have hq : 1 ≤ Dw.q := Nat.one_le_iff_ne_zero.2 hdef.2
    by_cases hrun : ∃ m : ℕ, 1 ≤ m ∧ m ^ 4 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E ∧ (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ 16 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ (Dw.p ≤ m ∨ Dw.q ≤ m)
    · obtain ⟨m, hm1, hm4, hf2, hrd, hpm⟩ := hrun
      have hr2 : 2 ≤ r := by omega
      have hf1 : 1 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E := le_trans (Nat.one_le_pow _ _ hm1) hm4
      have hfr : 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r := by nlinarith
      obtain ⟨q', R0, -, -, hrunOK⟩ := GlobalTheory.RunParametersBound.exists_run_bound E r m hfr hm1 hm4 hf2 hrd
      have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
      obtain ⟨i, J, _, cf, xs, f, hi, -, -, -, hf, -, hnz, -⟩ :=
        GlobalTheory.EtaAn.exists_etaRule_cusp_ne_zero_bounds E H Dw l Xo c r (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) σ
          (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (hL.unf σ hσ)) hσ hT hr2 5 (by decide)
          (by norm_num) 1 q' m R0 hrunOK hpm
      obtain ⟨y, hy, hne⟩ := hnz k
      have hf' : f ∈ cusp Xo c U 0 (2 * 5 ^ 4 * r * i) := hf
      refine ⟨2 * 5 ^ 4 * r * i, by positivity, ⟨5 ^ 4 * r * i, by ring⟩, f, hf', ⟨k, y⟩, ?_, hne⟩
      rw [hk]
      exact ⟨rfl, hy⟩
    · exact GlobalTheory.T.exists_scalar_cuspForm_indefinite_unitaryShimura E H Dw l Xo c r U x hL hp hq hrun σ hσ Z

end GlobalTheory.ScalarCusp
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_scalarWeight_cuspForm_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c), ∃ n₀ : ℕ, 0 < n₀ ∧ Even n₀ ∧ ∃ f₀ ∈ cusp Xo c U 0 n₀, ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  first | exact @GlobalTheory.ScalarCusp.exists_scalar_cusp_ne_zero | exact GlobalTheory.ScalarCusp.exists_scalar_cusp_ne_zero | (intros; apply GlobalTheory.ScalarCusp.exists_scalar_cusp_ne_zero <;> assumption)
end

section
set_option autoImplicit false

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatCore.NonzeroCusp

theorem laU_const {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (V : Unf Xo c σ r) (m n : ℕ) (k : V.Comp) :
    laU V (fun _ => m) n k = laU V 0 (n + 2 * m) k := by
  funext τ j
  have e : (n + 2 * m) / 2 = n / 2 + m := by omega
  simp only [laU, Pi.zero_apply, e]
  split_ifs <;> push_cast <;> ring

theorem exists_cuspOn_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c), ∃ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n ∧ (∀ τ i, i < Dw.mult τ → 2 ≤ a (τ, i)) ∧ 4 * (finrank ℚ E * r) + 4 ≤ n ∧ ∃ f ∈ cuspOn U Z (wtZ a n), f ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U x hL Z
  have hσ : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨n₀, hn₀, hev, f₀, hf₀, ⟨k, y⟩, hz, hne⟩ := GlobalTheory.T.exists_nonzero_scalarWeight_cuspForm_component E H Dw l Xo c r U x hL _ hσ Z
  obtain ⟨hy, hlies⟩ := hz
  have hM : CuspMul Xo c U := cusp_mul_of_M5 siegelSpaceAlgebra_holds U
  have hD0 : ∀ m, Even m → Dom (0 : (E →+* ℂ) × ℕ → ℕ) m := fun m hm => ⟨fun _ => antitone_const, hm⟩
  have hpow : ∀ j : ℕ, f₀ ^ (j + 1) ∈ cusp Xo c U 0 ((j + 1) * n₀) := by
    intro j
    induction j with
    | zero => simpa using hf₀
    | succ j ih =>
      have h := hM 0 0 ((j + 1) * n₀) n₀ (f₀ ^ (j + 1)) f₀ (hD0 _ (hev.mul_left _)) (hD0 _ hev) ih hf₀
      have e1 : ((j + 1) * n₀ + n₀) = (j + 1 + 1) * n₀ := by ring
      rw [add_zero, e1] at h
      rw [pow_succ]
      exact h
  have hrd : ∀ j : ℕ, rdU (U c.F.val.toRingHom) (f₀ ^ (j + 1)) k y = (rdU (U c.F.val.toRingHom) f₀ k y) ^ (j + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Formalism.L2.Pj.rdU_mul, Pi.mul_apply, Pi.mul_apply, ih]
      ring
  set M : ℕ := 4 * (finrank ℚ E * r) + 7 with hMdef
  obtain ⟨t, ht⟩ := hev
  have hMt : (M + 1) * n₀ = (M + 1) * t + (M + 1) * t := by rw [ht]; ring
  have ht1 : 1 ≤ t := by omega
  have hMt1 : M + 1 ≤ (M + 1) * t := Nat.le_mul_of_pos_right _ ht1
  set n : ℕ := (M + 1) * n₀ - 4 with hndef
  have hnev : Even n := ⟨(M + 1) * t - 2, by omega⟩
  have hnb : 4 * (finrank ℚ E * r) + 4 ≤ n := by omega
  have hn4 : n + 2 * 2 = (M + 1) * n₀ := by omega
  have hP : rdU (U c.F.val.toRingHom) (f₀ ^ (M + 1)) ∈
      holSub0 (U c.F.val.toRingHom).X (laU (U c.F.val.toRingHom) (fun _ => 2) n) := by
    have e : laU (U c.F.val.toRingHom) (fun _ => 2) n = laU (U c.F.val.toRingHom) 0 ((M + 1) * n₀) :=
      funext fun k' => by rw [laU_const, hn4]
    rw [e]
    exact ⟨((mem_cusp Xo c U 0 _ _).1 (hpow M)).2 _ hσ, rdU_mem_offZero _ _⟩
  have hspan := hL.onto _ hσ (fun _ => 2) n ⟨fun _ => antitone_const, hnev⟩ (fun _ _ _ => by norm_num) hnb hP
  obtain ⟨f, hf, hfy⟩ : ∃ f ∈ cusp Xo c U (fun _ => 2) n, rdU (U c.F.val.toRingHom) f k y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    let ev : FDSec (U c.F.val.toRingHom).X →ₗ[ℂ] ℂ :=
      { toFun := fun P => P k y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hle : Submodule.span ℂ (rdU (U c.F.val.toRingHom) '' (cusp Xo c U (fun _ => 2) n : Set (Rul Xo c))) ≤
        LinearMap.ker ev := by
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact hcon f hf
    have h0 : ev (rdU (U c.F.val.toRingHom) (f₀ ^ (M + 1))) = 0 := hle hspan
    have h1 : ev (rdU (U c.F.val.toRingHom) (f₀ ^ (M + 1))) = (rdU (U c.F.val.toRingHom) f₀ k y) ^ (M + 1) := hrd M
    exact pow_ne_zero _ hne (h1.symm.trans h0)
  obtain ⟨g, hg, -⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hL.unf Z (wtZ (fun _ => 2) n)
    ⟨f, by rw [cuspW_wtZ]; exact hf⟩
  refine ⟨fun _ => 2, n, ⟨fun _ => antitone_const, hnev⟩, fun _ _ _ => le_rfl, hnb, g, g.2, ?_⟩
  intro h0
  have e : rdU (U c.F.val.toRingHom) (g : Rul Xo c) k y = rdU (U c.F.val.toRingHom) f k y := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hy]
    rw [hg _ _ hlies]
  rw [h0, map_zero] at e
  exact hfy e.symm

end GlobalTheory.FlatCore.NonzeroCusp
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_cuspForm_parallelWeight_each_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c), ∃ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n ∧ (∀ τ i, i < Dw.mult τ → 2 ≤ a (τ, i)) ∧ 4 * (finrank ℚ E * r) + 4 ≤ n ∧ ∃ f ∈ cuspOn U Z (wtZ a n), f ≠ 0 := by
  first | exact @GlobalTheory.FlatCore.NonzeroCusp.exists_cuspOn_ne_zero | exact GlobalTheory.FlatCore.NonzeroCusp.exists_cuspOn_ne_zero | (intros; apply GlobalTheory.FlatCore.NonzeroCusp.exists_cuspOn_ne_zero <;> assumption)
end
