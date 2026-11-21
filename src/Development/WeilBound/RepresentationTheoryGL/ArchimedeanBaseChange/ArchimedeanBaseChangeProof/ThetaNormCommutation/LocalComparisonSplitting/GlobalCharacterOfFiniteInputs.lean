import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountIsInvInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormaliserUnconj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLocallyConstantOfRightInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCoordinate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsScalarOfCentral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConjEqSign
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPFinThetaGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialFiniteAdeles
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsRegEllIffMemEll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwConjugateEquivalence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEigenbasis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactOfBounded
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitPreimageEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRatCentTwConj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfRightInvariant
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualWeylModuleInvRationalPointEqConjCharAt

section
noncomputable section

open NumberField Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

theorem weylat_weylChar_eq_gtChar {n : ℕ} (l : DomWeight n) (γ : Fin n → ℂ) (h0 : ∀ i, γ i ≠ 0)
    (hinj : Function.Injective γ) :
    PositivityTheory.RgBcC.weylChar l.w γ = ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar n l.w γ := by
  have hA : (Matrix.of fun i j : Fin n => γ i ^ (l.w j + ((n - 1 - (j : ℕ) : ℕ) : ℤ))).det =
      ReciprocityTheory.ChartRestriction.TR.Weyl.alt n (l.w + ReciprocityTheory.ChartRestriction.TR.Weyl.delta n) γ := by
    unfold ReciprocityTheory.ChartRestriction.TR.Weyl.alt
    congr 1
    ext i j
    simp only [Matrix.of_apply, Pi.add_apply, ReciprocityTheory.ChartRestriction.TR.Weyl.delta]
    congr 1
    have := j.isLt
    omega
  have hV : (Matrix.of fun i j : Fin n => γ i ^ (n - 1 - (j : ℕ))).det =
      ReciprocityTheory.ChartRestriction.TR.Weyl.alt n (0 + ReciprocityTheory.ChartRestriction.TR.Weyl.delta n) γ := by
    unfold ReciprocityTheory.ChartRestriction.TR.Weyl.alt
    congr 1
    ext i j
    simp only [Matrix.of_apply, Pi.add_apply, Pi.zero_apply, zero_add, ReciprocityTheory.ChartRestriction.TR.Weyl.delta]
    rw [← zpow_natCast]
    congr 1
    have := j.isLt
    omega
  have h1 := ReciprocityTheory.ChartRestriction.TR.Weyl.weylGT ℂ n l.w l.anti γ h0
  have h2 := ReciprocityTheory.ChartRestriction.TR.Weyl.weylGT ℂ n 0 antitone_const γ h0
  rw [ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar_zero, mul_one] at h2
  have hw : ReciprocityTheory.ChartRestriction.TR.Weyl.wden n γ ≠ 0 := by
    unfold ReciprocityTheory.ChartRestriction.TR.Weyl.wden
    refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
    split_ifs with h
    · exact sub_ne_zero.2 fun e => (ne_of_lt h) (hinj e)
    · exact one_ne_zero
  unfold PositivityTheory.RgBcC.weylChar
  rw [hA, hV, ← h1, ← h2, mul_div_cancel_left₀ _ hw]

theorem weylAt_holds : WeylAt := by
  intro n l γ h0 hinj
  let D : GL (Fin n) ℂ := Formalism.BasicNotions.diagGL ℂ n fun i => Units.mk0 _ (h0 i)
  have hD : (D : Matrix (Fin n) (Fin n) ℂ) = diagonal γ := by
    change diagonal (fun a => ((Units.mk0 _ (h0 a) : ℂˣ) : ℂ)) = _
    simp only [Units.val_mk0]
  have hex : ∃ g : GL (Fin n) ℂ, g.val.charpoly = (diagonal γ).charpoly := ⟨D, by rw [hD]⟩
  unfold chAt
  rw [dif_pos hex, GlobalTheory.ContraChar.trace_sqRep_eq_of_charpoly_eq l _ D (hex.choose_spec.trans (by rw [hD])),
    GlobalTheory.ContraChar.trace_sqRep_diag l D γ hD, weylat_weylChar_eq_gtChar l γ h0 hinj]

end PositivityTheory.Rg.BcB.G8

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

open PositivityTheory.Rg.Tf.Loc (quotIntegral IsQuotNormaliser twConj)

theorem termof_twConj_cont {n : ℕ} (hθ : Continuous (thetaR (starRingEnd ℂ) n)) (d : GL (Fin n) ℂ) :
    Continuous fun x : GL (Fin n) ℂ => twConj (thetaR (starRingEnd ℂ) n) x d := by
  show Continuous fun x : GL (Fin n) ℂ => x⁻¹ * d * thetaR (starRingEnd ℂ) n x
  exact (continuous_inv.mul continuous_const).mul hθ

theorem termof_hcs {a b : ℕ} (hEP : EllProper) (ψ : GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ) (hψ : HasCompactSupport ψ)
    (d₁ : GL (Fin a) ℂ) (d₂ : GL (Fin b) ℂ) (h₁ : EllC d₁) (h₂ : EllC d₂) :
    HasCompactSupport fun y : GL (Fin a) ℂ × GL (Fin b) ℂ =>
      ψ (twConj (thetaR (starRingEnd ℂ) a) y.1 d₁, twConj (thetaR (starRingEnd ℂ) b) y.2 d₂) := by
  have hK := (hEP a d₁ h₁ _ (hψ.isCompact.image continuous_fst)).prod
    (hEP b d₂ h₂ _ (hψ.isCompact.image continuous_snd))
  refine HasCompactSupport.intro hK fun y hy => ?_
  by_contra hne
  apply hy
  have hm : (twConj (thetaR (starRingEnd ℂ) a) y.1 d₁, twConj (thetaR (starRingEnd ℂ) b) y.2 d₂) ∈ tsupport ψ :=
    subset_tsupport _ hne
  exact ⟨⟨_, hm, rfl⟩, ⟨_, hm, rfl⟩⟩

theorem termOf_holds : TermOf := by
  intro hQS hHS hTopo hCI hKf hFL hFH hAE hCE hPE hEP
  intro E _ _ _ hU a b _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ ν₁ _ ν₂ _
  obtain ⟨⟨hlcA, hscA, ht2A⟩, ⟨hlcfA, hscfA, ht2fA⟩, ⟨hlcCA, hscCA⟩, hcntA, -, hθA⟩ := hTopo E a
  obtain ⟨⟨hlcB, hscB, ht2B⟩, ⟨hlcfB, hscfB, ht2fB⟩, ⟨hlcCB, hscCB⟩, hcntB, -, hθB⟩ := hTopo E b
  letI mB : MeasurableSpace (Gf E a b) := borel _
  haveI : BorelSpace (Gf E a b) := ⟨rfl⟩
  obtain ⟨e, he⟩ := hCI E a b
  let e' : (GA E a × GA E b) →* (Gi E a b × Gf E a b) := e.toMulEquiv.toMonoidHom
  have he' : ∀ x, e' x = comps x := he
  have hνH : (ν₁.prod ν₂).IsHaarMeasure := inferInstance
  have hνS : SigmaFinite (ν₁.prod ν₂) := inferInstance
  have hαH : (Measure.pi fun _ : InfinitePlace E => ν₁.prod ν₂).IsHaarMeasure := inferInstance
  let α : Measure (Gi E a b) := Measure.pi fun _ => ν₁.prod ν₂
  obtain ⟨β, hβ, hmap⟩ := hHS (GA E a × GA E b) (Gi E a b) (Gf E a b) (μ₁.prod μ₂) α e
  haveI := hβ
  obtain ⟨hKo₁, hKc₁⟩ := hKf E a
  obtain ⟨hKo₂, hKc₂⟩ := hKf E b
  have hKo : IsOpen (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    rw [Subgroup.coe_prod]; exact hKo₁.prod hKo₂
  have hKc : IsCompact (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    rw [Subgroup.coe_prod]; exact hKc₁.prod hKc₂
  refine ⟨(β.real (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) : ℂ), ?_, ?_⟩
  · rw [Complex.ofReal_ne_zero, measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨hKo.measure_ne_zero β ⟨1, Subgroup.one_mem _⟩, hKc.measure_lt_top.ne⟩
  intro S hS u₁ u₂ hu₁ hu₂ l₁ l₂ val ψ φ₁ φ₂ hLef hφ₁ hφ₂ d₁ d₂ hd₁ hd₂
  obtain ⟨hP₁, hPv₁⟩ := hPE E a u₁ hu₁ d₁
  obtain ⟨hP₂, hPv₂⟩ := hPE E b u₂ hu₂ d₂
  have hCE' := hCE E a b u₁ u₂ hu₁ hu₂ d₁ d₂
  let f : InfinitePlace E → GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ := fun v y =>
    ψ v (twConj (thetaR (starRingEnd ℂ) a) y.1 (GeneralLinearGroup.map v.embedding d₁),
      twConj (thetaR (starRingEnd ℂ) b) y.2 (GeneralLinearGroup.map v.embedding d₂))
  let F₁ : Gi E a b → ℂ := fun y => ∏ v, f v (y v)
  let F₂ : Gf E a b → ℂ := orbFn S φ₁ φ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹)
  have hfc : ∀ v, Continuous (f v) := fun v =>
    (hLef v).1.comp (((termof_twConj_cont hθA _).comp continuous_fst).prodMk
      ((termof_twConj_cont hθB _).comp continuous_snd))
  have hfs : ∀ v, HasCompactSupport (f v) := fun v =>
    termof_hcs hEP (ψ v) (hLef v).2.1 _ _ ((hPv₁ v).2 hd₁) ((hPv₂ v).2 hd₂)
  have hint : ∀ v, Integrable (f v) (ν₁.prod ν₂) := fun v => (hfc v).integrable_of_hasCompactSupport (hfs v)
  have hF₁i : Integrable F₁ α := Integrable.fintype_prod hint
  have hF₁m : Measurable F₁ :=
    (continuous_finset_prod _ fun v _ => (hfc v).comp (continuous_apply v)).measurable
  haveI : Countable ↥((ratCent d₁).prod (ratCent d₂)) := by
    have hsub : (((ratCent d₁).prod (ratCent d₂) : Subgroup (GA E a × GA E b)) : Set (GA E a × GA E b)) ⊆
        Set.range (fun p : GL (Fin a) E × GL (Fin b) E => (ratGL E a p.1, ratGL E b p.2)) := by
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_prod] at hx
      obtain ⟨g₁, -, hg₁⟩ := Subgroup.mem_map.1 hx.1
      obtain ⟨g₂, -, hg₂⟩ := Subgroup.mem_map.1 hx.2
      exact ⟨(g₁, g₂), Prod.ext hg₁ hg₂⟩
    exact ((Set.countable_range _).mono hsub).to_subtype
  have hΓ : ((ratCent d₁).prod (ratCent d₂)).map ((MonoidHom.snd _ _).comp e') = gam (d₁ * u₁⁻¹) (d₂ * u₂⁻¹) := by
    ext y
    rw [Subgroup.mem_map, hCE'.1 y]
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨γ, hγ, (congrArg Prod.snd (he' γ)).symm⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨γ, hγ, congrArg Prod.snd (he' γ)⟩
  have hinj : ∀ γ ∈ (ratCent d₁).prod (ratCent d₂), (e' γ).2 = 1 → γ = 1 := by
    intro γ hγ h1
    rw [he'] at h1
    exact (hCE'.2 γ hγ).1 h1
  have hF₁inv : ∀ γ ∈ (ratCent d₁).prod (ratCent d₂), ∀ x, F₁ ((e' γ).1 * x) = F₁ x := by
    intro γ hγ x
    have hc := (hCE'.2 γ hγ).2
    rw [he']
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [f, Pi.mul_apply, Prod.fst_mul, Prod.snd_mul]
    rw [PositivityTheory.Rg.Tf.Loc.twConj_mul_left _ _ (hc v).1, PositivityTheory.Rg.Tf.Loc.twConj_mul_left _ _ (hc v).2]
  have hF₂inv : ∀ γ ∈ gam (d₁ * u₁⁻¹) (d₂ * u₂⁻¹), ∀ y, F₂ (γ * y) = F₂ y := by
    intro γ hγ y
    have h : γ * (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) =
        (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) * thP E a b γ := (Subgroup.mem_inf.1 hγ).2
    simp only [F₂, orbFn]
    congr 1
    generalize (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) = δ at h ⊢
    rw [(thP E a b).map_mul γ y, show (γ * y)⁻¹ * δ * (thP E a b γ * thP E a b y) =
      y⁻¹ * (γ⁻¹ * (δ * thP E a b γ)) * thP E a b y by group, ← h]
    group
  obtain ⟨U, hUo, hUinv⟩ := hFL E hU a b S φ₁ φ₂ hφ₁ hφ₂
  have hF₂U : ∀ u ∈ U, ∀ y, F₂ (y * u) = F₂ y := by
    intro u hu y
    simp only [F₂, orbFn]
    rw [← hUinv u hu (y⁻¹ * (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) * thP E a b y)]
    congr 1
    generalize (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) = δ
    rw [(thP E a b).map_mul y u]
    group
  obtain ⟨hfin, hstab, hdc⟩ :=
    hFH E hU a b S hS φ₁ φ₂ hφ₁ hφ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹) (hP₁.1 hd₁) (hP₂.1 hd₂)
  have hQ := hQS (GA E a × GA E b) (Gi E a b) (Gf E a b) (μ₁.prod μ₂) α β e' (map_continuous e).measurable hmap
    ((ratCent d₁).prod (ratCent d₂)) (gam (d₁ * u₁⁻¹) (d₂ * u₂⁻¹)) ((Kf E a).prod (Kf E b)) U hΓ hinj hKo hKc hUo
    F₁ F₂ hF₁m hF₁i hF₁inv hF₂inv hF₂U hfin hstab
  have hEq : orbTerm2 μ₁ μ₂ (adel S u₁ u₂ ψ φ₁ φ₂) d₁ d₂ = quotIntegral (μ₁.prod μ₂) ((ratCent d₁).prod (ratCent d₂))
      Measure.count (fun x => F₁ (e' x).1 * F₂ (e' x).2) := by
    unfold orbTerm2
    congr 1
    funext x
    rw [hAE E a b S u₁ u₂ hu₁ hu₂ ψ φ₁ φ₂ d₁ d₂ x, he' x]
  have hI : ∫ x, F₁ x ∂α = ∏ v, (val v * starRingEnd ℂ (chAt (l₁ v) ((polE (d₁ * u₁⁻¹)).map v.embedding)) *
      starRingEnd ℂ (chAt (l₂ v) ((polE (d₂ * u₂⁻¹)).map v.embedding))) := by
    rw [integral_fintype_prod_eq_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [(hLef v).2.2 _ _ ((hPv₁ v).2 hd₁) ((hPv₂ v).2 hd₂), (hPv₁ v).1, (hPv₂ v).1]
  rw [hEq, hQ, hI, hdc, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [chW]
  ring

end PositivityTheory.Rg.BcB.G8

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

open PositivityTheory.Rg.Tf.Loc (quotIntegral IsQuotNormaliser twConj)

theorem mul_finsum_eq {α : Type*} (r : ℂ) (f : α → ℂ) : ∑ᶠ i, r * f i = r * ∑ᶠ i, f i := by
  have h := smul_finsum (R := ℂ) (M := ℂ) r f
  simpa only [smul_eq_mul] using h.symm

theorem global_character_of_holds : GlobalCharacterOfInputs := by
  intro hT hO hA hC hP E _ _ _ hU a b _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ ν₁ _ ν₂ _
  obtain ⟨c, hc0, hc⟩ := hT E hU a b μ₁ μ₂ ν₁ ν₂
  refine ⟨c, hc0, ?_⟩
  intro S hS u₁ u₂ hu₁ hu₂ l₁ l₂ val ψ φ₁ φ₂ hL hφ₁ hφ₂
  obtain ⟨e₁, he₁⟩ := hC E a u₁ hu₁
  obtain ⟨e₂, he₂⟩ := hC E b u₂ hu₂
  have hψ : ∀ v, Continuous (ψ v) := fun v => (hL v).1
  unfold ellSum2 geomRat2
  rw [← finsum_comp_equiv (e₁.prodCongr e₂), ← mul_finsum_eq]
  refine finsum_congr fun x => ?_
  obtain ⟨x₁, x₂⟩ := x
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  obtain ⟨g₁, hg₁, hr₁⟩ := he₁ x₁
  obtain ⟨g₂, hg₂, hr₂⟩ := he₂ x₂
  have hiff : (IsRegEll (Quot.out (e₁ x₁)) ∧ IsRegEll (Quot.out (e₂ x₂))) ↔ (pol x₁ ∈ Ell E a ∧ pol x₂ ∈ Ell E b) := by
    rw [hr₁, hr₂, (hP E a u₁ hu₁ _).1, (hP E b u₂ hu₂ _).1, mul_inv_cancel_right, mul_inv_cancel_right]
    exact Iff.rfl
  have horb : orbTerm2 μ₁ μ₂ (adel S u₁ u₂ ψ φ₁ φ₂) (Quot.out (e₁ x₁)) (Quot.out (e₂ x₂)) =
      orbTerm2 μ₁ μ₂ (adel S u₁ u₂ ψ φ₁ φ₂) (x₁.rep * u₁) (x₂.rep * u₂) := by
    rw [hg₁, hg₂, hO E a b μ₁ μ₂ _ _ g₁ _ g₂ (hA E hU a b S u₁ u₂ hu₁ hu₂ ψ φ₁ φ₂ hψ hφ₁ hφ₂ _ _)]
  rw [finsum_eq_if]
  by_cases h : pol x₁ ∈ Ell E a ∧ pol x₂ ∈ Ell E b
  · rw [if_pos (hiff.2 h), if_pos h, horb]
    have ht := hc S hS u₁ u₂ hu₁ hu₂ l₁ l₂ val ψ φ₁ φ₂ hL hφ₁ hφ₂ (x₁.rep * u₁) (x₂.rep * u₂)
      (hr₁.1 (hiff.2 h).1) (hr₂.1 (hiff.2 h).2)
    simp only [mul_inv_cancel_right] at ht
    exact ht
  · rw [if_neg (mt hiff.1 h), if_neg h, mul_zero]

end PositivityTheory.Rg.BcB.G8

end
end

section
namespace PositivityTheory.Rg.BcB.G8

open GlobalTheory.CompanionTheory

theorem translation_existence_holds : TranslEx := LocalThetaTranslation.translEx

theorem lefschetz_pair_holds : LefPair := GlobalTheory.CompanionTheory.LefPair.lefPairOf EllipticTwist.ellDiag weylAt_holds LocalThetaTopology.topo

theorem global_character_of_finite_inputs (hK : KfOC) (hL : FinLevel) (hF : FinHalf) : G4 :=
  have hA : AdelEq := AdelEqProof.adelEqOf TranslAdele.translAd
  global_character_of_holds
    (termOf_holds (QSplitPf.qSplitOf QuotNorm.qIndep) HaarProd.haarSplit LocalThetaTopology.topo CompIsoProof.compIso hK hL hF hA
      TwistCent.centEq NormPoly.polEq (EllProp.ellProperOf EllipticTwist.ellDiag DiagProperProof.diagProper LocalThetaTopology.topo))
    (GlobalTheory.CompanionTheory.OrbInv.orbInvOf (QConjug.qConjOf_holds QuotNorm.qIndep) LocalThetaTopology.topo)
    (GlobalTheory.CompanionTheory.AdelCont.adelContOf hA hL CompIsoProof.compIso LocalThetaTopology.topo) GlobalTheory.CompanionTheory.ClassBij.classBij NormPoly.polEq

end PositivityTheory.Rg.BcB.G8
end
