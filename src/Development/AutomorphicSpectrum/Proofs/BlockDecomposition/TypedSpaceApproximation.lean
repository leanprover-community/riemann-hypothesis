import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.AutomorphicLipschitz.NiceAut
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UpdateLeUpdate
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundConstantTerm
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConjugationDifferences.ExpDivExpEq
import BuildAid.ForwardExisting
import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffDiagonalBlockGLEqVecCoeff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundSiegelSet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLatticePointsSiegel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsExponentPolynomialDiscrete
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariantTotallyComplex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEigenfunctionEquicontinuous
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenLevel

section
section
noncomputable section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open scoped NumberField.AdeleRing Pointwise
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
  GroundTheory.Automorphic.CuspidalSpectrum

namespace GlobalTheory.CompanionTheory.Conc

open PositivityTheory.Rg.Rs.diffstep in

theorem diffStepU (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type)
    (f₀ f₁ : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) (r : ℕ) (hr : 0 < r) (hrn : r < n) (hN : UFam f₁)
    (hlip' : ∀ R : ℝ, ∃ (Q₀ : Set (AdelicGLn.AdelicGL K n)) (C : ℝ), IsCompact Q₀ ∧ 0 ≤ C ∧
      ∀ i g (Y : ArchMatrix K n) (M : ℝ), Y * Y = 0 → ‖Y‖ ≤ R →
        (∀ q ∈ Q₀, ‖f₀ i (g * q)‖ ≤ M) → ‖f₁ i (g * CuspidalSpectrum.archExp Y) - f₁ i g‖ ≤ C * ‖Y‖ * M)
    (hB : UBnd f₀ m) :
    UBnd (fun i g => f₁ i g - An.ctn r (f₁ i) g) (Function.update m r (m r - 1)) := by
  intro ω hω hωB t₀ Q hQ
  obtain ⟨U, hU, hlev⟩ := hN.level
  obtain ⟨M, hM, hMc⟩ := exists_natCast_conj_mem U hU hω hQ r
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_conjArch_le hω hωB hQ (Real.exp_pos (-t₀)) hr hrn
    (isCompact_scaledInfSet (K := K) M)
  obtain ⟨Q₀, C₂, hQ₀, hC₂, hlip⟩ := hlip' (C₁ * Real.exp t₀)
  obtain ⟨C₃, hC₃⟩ := hB ω hω hωB t₀ (Q * Q₀) (hQ.mul hQ₀)
  set C₃' := max C₃ 0 with hC₃'
  have hC₃'0 : 0 ≤ C₃' := le_max_right _ _
  refine ⟨C₂ * C₁ * C₃', ?_⟩
  intro i b hb x hx q hq
  set g := b * An.tor K x * q with hg
  set S := ∑ i ∈ Finset.range n, m i * An.sr x i with hS
  have hsieg := siegel_of_sr hx
  have hpt : ∀ X ∈ scaledUnipFD K n r M, ‖f₁ i g - f₁ i (unipGL X * g)‖ ≤
      C₂ * (C₁ * Real.exp (-An.sr x r)) * (C₃' * Real.exp S) := by
    intro X hX
    set Y := conjArch K n g (truncInf X) with hY
    have hYn : ‖Y‖ ≤ C₁ * Real.exp (-An.sr x r) := by
      have h := hC₁ b hb (fun i => Real.exp (x i)) (fun i => Real.exp_pos _) hsieg q hq (truncInf X)
        (fun p => rfl) (fun p => infinite_mem_scaledInfSet hM hX p)
      rw [exp_div_exp_eq hr hrn x] at h
      exact h
    have hYR : ‖Y‖ ≤ C₁ * Real.exp t₀ :=
      hYn.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [hx r])) hC₁0)
    obtain ⟨u, hu⟩ := hMc b hb (fun i => Real.exp (x i)) (fun i => Real.exp_pos _) q hq (truncFin X)
      (fun p => rfl) (fun p => exists_finite_eq_natCast_mul hM hX p)
    have hu' : g⁻¹ * unipGL (truncFin X) * g =
        finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) := hu
    have hdecomp : unipGL X * g = g * archExp Y * (g⁻¹ * unipGL (truncFin X) * g) := by
      rw [hY, ← conj_unipGL_eq_archExp g (truncInf X) (fun p => rfl)]
      conv_lhs => rw [← truncInf_add_truncFin X, unipGL_add]
      group
    have heq : f₁ i (unipGL X * g) = f₁ i (g * archExp Y) := by rw [hdecomp, hu', hlev]
    have hMg : ∀ q' ∈ Q₀, ‖f₀ i (g * q')‖ ≤ C₃' * Real.exp S := by
      intro q' hq'
      have h := hC₃ i b hb x hx (q * q') (Set.mul_mem_mul hq hq')
      rw [show g * q' = b * An.tor K x * (q * q') by rw [hg, mul_assoc]]
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have hl := hlip i g Y (C₃' * Real.exp S) (conjArch_mul_conjArch _ _ _) hYR hMg
    rw [norm_sub_rev, heq]
    calc _ ≤ C₂ * ‖Y‖ * (C₃' * Real.exp S) := hl
      _ ≤ _ := by gcongr
  have hD := isAddFundamentalDomain_scaledUnipFD (K := K) (n := n) (r := r) hM
  have hD1 := unipMeasure_scaledUnipFD (K := K) (n := n) (r := r) hM
  obtain ⟨Cc, hCc, hDC⟩ := exists_isCompact_superset_scaledUnipFD (K := K) (n := n) r hM
  have hint : IntegrableOn (fun X => f₁ i (unipGL X * g)) (scaledUnipFD K n r M) (unipMeasure K n r) :=
    (((hN.cont i).comp (continuous_unipGL.mul continuous_const)).continuousOn.integrableOn_compact
      hCc).mono_set hDC
  have hfin : unipMeasure K n r (scaledUnipFD K n r M) < ⊤ := by
    rw [hD1]
    exact ENNReal.one_lt_top
  have hct : An.ctn r (f₁ i) g = ∫ X in scaledUnipFD K n r M, f₁ i (unipGL X * g) ∂unipMeasure K n r := by
    rw [An.ctn, measureReal_def, unipMeasure_unipFundamentalDomain, ENNReal.toReal_one,
      Complex.ofReal_one, inv_one, one_mul]
    exact constantTerm_eq_setIntegral (hN.left i) hD g
  have hdiff : f₁ i g - An.ctn r (f₁ i) g =
      ∫ X in scaledUnipFD K n r M, (f₁ i g - f₁ i (unipGL X * g)) ∂unipMeasure K n r := by
    have hconst : IntegrableOn (fun _ => f₁ i g) (scaledUnipFD K n r M) (unipMeasure K n r) :=
      integrableOn_const hfin.ne enorm_ne_top
    rw [hct, integral_sub hconst hint, setIntegral_const, measureReal_def, hD1,
      ENNReal.toReal_one, one_smul]
  change ‖f₁ i g - An.ctn r (f₁ i) g‖ ≤ _
  rw [hdiff]
  refine (norm_setIntegral_le_of_norm_le_const hfin hpt).trans (le_of_eq ?_)
  rw [measureReal_def, hD1, ENNReal.toReal_one, mul_one, sum_update_sub hrn, ← hS, sub_eq_add_neg,
    Real.exp_add]
  ring

end GlobalTheory.CompanionTheory.Conc

end
end

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_bound_of_archimedean_lipschitz : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) (f₀ f₁ : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) (r : ℕ), 0 < r → r < n → UFam f₁ →
  (∀ R : ℝ, ∃ (Q₀ : Set (AdelicGLn.AdelicGL K n)) (C : ℝ), IsCompact Q₀ ∧ 0 ≤ C ∧ ∀ i g (Y : ArchMatrix K n) (M : ℝ), Y * Y = 0 → ‖Y‖ ≤ R →
    (∀ q ∈ Q₀, ‖f₀ i (g * q)‖ ≤ M) → ‖f₁ i (g * CuspidalSpectrum.archExp Y) - f₁ i g‖ ≤ C * ‖Y‖ * M) →
  UBnd f₀ m → UBnd (fun i g => f₁ i g - An.ctn r (f₁ i) g) (Function.update m r (m r - 1)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Conc.diffStepU
end

section
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc

theorem continuous_sm_of_ker : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ)
    [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (f : AdelicGLn.AdelicGL K n → ℂ),
    Ker ν β → Continuous f → Continuous (sm ν β f) := by
  intro K _ _ n _ _ ν _ β f hβ hf
  have hs : IsCompact (tsupport β) := hβ.cpt
  set F : AdelicGLn.AdelicGL K n × archGroup K n → ℂ :=
    fun p => (β p.2 : ℂ) * f (p.1 * infEmb K n p.2) with hFdef
  have hF : Continuous F :=
    (Complex.continuous_ofReal.comp (hβ.cont.comp continuous_snd)).mul
      (hf.comp (continuous_fst.mul (continuous_infEmb.comp continuous_snd)))
  have hFx : ∀ x, Continuous fun y => F (x, y) := fun x =>
    hF.comp (continuous_const.prodMk continuous_id)
  have hint : ∀ x, IntegrableOn (fun y => F (x, y)) (tsupport β) ν := fun x =>
    (hFx x).continuousOn.integrableOn_compact hs
  have e : ∀ x, sm ν β f x = ∫ y in tsupport β, F (x, y) ∂ν := fun x =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      simp [hFdef, image_eq_zero_of_notMem_tsupport hy]).symm
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hc : 0 ≤ ν.real (tsupport β) := measureReal_nonneg
  set δ : ℝ := ε / (ν.real (tsupport β) + 1) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hopen : IsOpen {p : AdelicGLn.AdelicGL K n × archGroup K n | dist (F p) (F (x₀, p.2)) < δ} :=
    isOpen_lt (hF.dist (hF.comp (continuous_const.prodMk continuous_snd))) continuous_const
  obtain ⟨u, v, hu, -, hxu, hsv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := x₀)) hs hopen (by
    rintro ⟨x, y⟩ ⟨hx, -⟩
    obtain rfl : x = x₀ := hx
    simpa using hδ)
  filter_upwards [hu.mem_nhds (hxu rfl)] with x hx
  rw [e, e, dist_eq_norm, ← integral_sub (hint x) (hint x₀)]
  have hb : ‖∫ y in tsupport β, (F (x, y) - F (x₀, y)) ∂ν‖ ≤ δ * ν.real (tsupport β) := by
    refine norm_setIntegral_le_of_norm_le_const hs.measure_lt_top fun y hy => ?_
    have := huv (Set.mk_mem_prod hx (hsv hy))
    simp only [Set.mem_setOf_eq, dist_eq_norm] at this
    exact this.le
  refine lt_of_le_of_lt hb ?_
  rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
  nlinarith

end GlobalTheory.CompanionTheory.Conc
end

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_archimedean_smoothing : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (f : AdelicGLn.AdelicGL K n → ℂ), Ker ν β → Continuous f → Continuous (sm ν β f) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Conc.continuous_sm_of_ker
end

section
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc

open scoped Pointwise

theorem sm_lip_of_sq_zero : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ), Ker ν β → ∀ R : ℝ, ∃ (Q₀ : Set (AdelicGLn.AdelicGL K n)) (C : ℝ), IsCompact Q₀ ∧ 0 ≤ C ∧
  ∀ (f : AdelicGLn.AdelicGL K n → ℂ), Continuous f → ∀ g (Y : ArchMatrix K n) (M : ℝ), Y * Y = 0 → ‖Y‖ ≤ R → (∀ q ∈ Q₀, ‖f (g * q)‖ ≤ M) →
    ‖sm ν β f (g * CuspidalSpectrum.archExp Y) - sm ν β f g‖ ≤ C * ‖Y‖ * M := by
  intro K _ _ n _ _ ν _ β hβ R
  obtain ⟨L, hL0, hL⟩ := hβ.lip
  set e : ArchMatrix K n → archGroup K n :=
    fun Y => (isExpLieAlgebra K n).expG ⟨Y, Submodule.mem_top⟩ with he
  have hec : Continuous e :=
    (isExpLieAlgebra K n).continuous_expG.comp (continuous_id.subtype_mk _)
  have hT₀ : IsCompact (tsupport β) := hβ.cpt
  haveI : ProperSpace (ArchMatrix K n) := FiniteDimensional.proper ℝ _
  have hB : IsCompact (e '' Metric.closedBall 0 R) := (isCompact_closedBall 0 R).image hec
  set T : Set (archGroup K n) := tsupport β ∪ (e '' Metric.closedBall 0 R) * tsupport β with hTdef
  have hT : IsCompact T := hT₀.union (hB.mul hT₀)
  obtain ⟨S, hS0, hS⟩ := (hT.image continuous_mat).isBounded.exists_pos_norm_le
  have hne : (tsupport β).Nonempty := by
    rcases Set.eq_empty_or_nonempty (tsupport β) with h0 | h0
    · exfalso
      have hz : ∀ y, β y = 0 := fun y => image_eq_zero_of_notMem_tsupport (by simp [h0])
      have := hβ.mass
      simp [hz] at this
    · exact h0
  refine ⟨infEmb K n '' T, L * S * ν.real T, hT.image continuous_infEmb, by positivity, ?_⟩
  intro f hf g Y M hYY hYR hM
  obtain ⟨t₀, ht₀⟩ := hne
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ ⟨t₀, Or.inl ht₀, rfl⟩)
  set h : archGroup K n → ℂ := fun y => f (g * infEmb K n y) with hh
  have hhc : Continuous h := hf.comp (continuous_const.mul continuous_infEmb)

  have hexp : mat (e Y) = 1 + Y :=
    (CuspidalSpectrum.coe_expG_top Y).trans (CuspidalSpectrum.exp_eq_one_add_of_mul_self_eq_zero hYY)
  have hmul : ∀ a b : archGroup K n, mat (a * b) = mat a * mat b := fun _ _ => rfl
  have hinv : mat (e Y)⁻¹ = 1 - Y := by
    have h1 : mat (e Y) * (1 - Y) = 1 := by
      have : (1 + Y) * (1 - Y) = 1 - Y * Y := by noncomm_ring
      rw [hexp, this, hYY, sub_zero]
    have h2 : mat (e Y)⁻¹ * mat (e Y) = 1 := by
      rw [← hmul, inv_mul_cancel]; rfl
    calc mat (e Y)⁻¹ = mat (e Y)⁻¹ * (mat (e Y) * (1 - Y)) := by rw [h1, mul_one]
      _ = 1 - Y := by rw [← mul_assoc, h2, one_mul]

  have hz2 : ∀ u, u ∉ T → β u = 0 := fun u hu =>
    image_eq_zero_of_notMem_tsupport fun hc => hu (Or.inl hc)
  have hz1 : ∀ u, u ∉ T → β ((e Y)⁻¹ * u) = 0 := fun u hu =>
    image_eq_zero_of_notMem_tsupport fun hc => hu (Or.inr
      ⟨e Y, ⟨Y, by simpa using hYR, rfl⟩, _, hc, by simp⟩)
  set F₁ : archGroup K n → ℂ := fun u => (β ((e Y)⁻¹ * u) : ℂ) * h u with hF₁
  set F₂ : archGroup K n → ℂ := fun u => (β u : ℂ) * h u with hF₂
  have hF₁c : Continuous F₁ :=
    (Complex.continuous_ofReal.comp (hβ.cont.comp (continuous_const.mul continuous_id))).mul hhc
  have hF₂c : Continuous F₂ := (Complex.continuous_ofReal.comp hβ.cont).mul hhc
  have hF₁z : ∀ u, u ∉ T → F₁ u = 0 := fun u hu => by simp [hF₁, hz1 u hu]
  have hF₂z : ∀ u, u ∉ T → F₂ u = 0 := fun u hu => by simp [hF₂, hz2 u hu]
  have hF₁i : Integrable F₁ ν :=
    hF₁c.integrable_of_hasCompactSupport (HasCompactSupport.intro hT hF₁z)
  have hF₂i : Integrable F₂ ν :=
    hF₂c.integrable_of_hasCompactSupport (HasCompactSupport.intro hT hF₂z)
  have hsm1 : sm ν β f (g * CuspidalSpectrum.archExp Y) = ∫ u, F₁ u ∂ν := by
    rw [← integral_mul_left_eq_self (μ := ν) F₁ (e Y)]
    unfold sm
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hF₁, hh, inv_mul_cancel_left, map_mul]
    rw [CuspidalSpectrum.archExp, mul_assoc]
  have hsm2 : sm ν β f g = ∫ u, F₂ u ∂ν := rfl
  rw [hsm1, hsm2, ← integral_sub hF₁i hF₂i,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := T)
      (fun u hu => by rw [hF₁z u hu, hF₂z u hu, sub_zero])]
  have hpt : ∀ u ∈ T, ‖F₁ u - F₂ u‖ ≤ L * S * ‖Y‖ * M := by
    intro u hu
    have hd : F₁ u - F₂ u = ((β ((e Y)⁻¹ * u) - β u : ℝ) : ℂ) * h u := by
      simp only [hF₁, hF₂]; push_cast; ring
    have hm : mat ((e Y)⁻¹ * u) - mat u = -(Y * mat u) := by
      rw [hmul, hinv]; noncomm_ring
    have h1 : |β ((e Y)⁻¹ * u) - β u| ≤ L * (‖Y‖ * S) := by
      refine (hL _ _).trans (mul_le_mul_of_nonneg_left ?_ hL0)
      rw [hm, norm_neg]
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (hS _ ⟨u, hu, rfl⟩) (norm_nonneg _))
    have h2 : ‖h u‖ ≤ M := hM _ ⟨u, hu, rfl⟩
    rw [hd, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |β ((e Y)⁻¹ * u) - β u| * ‖h u‖ ≤ (L * (‖Y‖ * S)) * M :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = L * S * ‖Y‖ * M := by ring
  have := norm_setIntegral_le_of_norm_le_const (μ := ν) (s := T) hT.measure_lt_top hpt
  refine this.trans (le_of_eq ?_)
  ring

end GlobalTheory.CompanionTheory.Conc
end

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothing_lipschitz_bound : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ), Ker ν β → ∀ R : ℝ, ∃ (Q₀ : Set (AdelicGLn.AdelicGL K n)) (C : ℝ), IsCompact Q₀ ∧ 0 ≤ C ∧
  ∀ (f : AdelicGLn.AdelicGL K n → ℂ), Continuous f → ∀ g (Y : ArchMatrix K n) (M : ℝ), Y * Y = 0 → ‖Y‖ ≤ R → (∀ q ∈ Q₀, ‖f (g * q)‖ ≤ M) →
    ‖sm ν β f (g * CuspidalSpectrum.archExp Y) - sm ν β f g‖ ≤ C * ‖Y‖ * M := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Conc.sm_lip_of_sq_zero
end

section
section
noncomputable section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc

theorem continuous_sm_uFam {K : Type} [Field K] [NumberField K] {n : ℕ}
    [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] {β : archGroup K n → ℝ} (hβ : Ker ν β) {f : AdelicGLn.AdelicGL K n → ℂ}
    (hf : Continuous f) : Continuous (sm ν β f) := by
  have hF : Continuous (Function.uncurry fun (x : AdelicGLn.AdelicGL K n) (y : archGroup K n) =>
      (β y : ℂ) * f (x * infEmb K n y)) := by
    refine (Complex.continuous_ofReal.comp (hβ.cont.comp continuous_snd)).mul (hf.comp ?_)
    exact continuous_fst.mul (continuous_infEmb.comp continuous_snd)
  have h := continuous_parametric_integral_of_continuous (μ := ν) hF hβ.cpt.isCompact
  refine h.congr fun x => ?_
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
  have : β y = 0 := image_eq_zero_of_notMem_tsupport hy
  simp [this]

theorem uFam_sm : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)]
    [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ)
    (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ), Ker ν β → UFam f → UFam (fun i => sm ν β (f i)) := by
  intro K _ _ n _ _ ν _ β ι f hβ hf
  refine ⟨fun i => continuous_sm_uFam ν hβ (hf.cont i), fun i γ x => ?_, ?_⟩
  · simp only [sm, mul_assoc]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [hf.left i γ (x * infEmb K n y)]
  · obtain ⟨U, hU, hlev⟩ := hf.level
    refine ⟨U, hU, fun i g u => ?_⟩
    simp only [sm]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [mul_assoc g, ← infEmb_mul_finEmb_comm, ← mul_assoc, hlev i (g * infEmb K n y) u]

end GlobalTheory.CompanionTheory.Conc

end
end

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_family_smoothing : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ), Ker ν β → UFam f → UFam (fun i => sm ν β (f i)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Conc.uFam_sm
end

section
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

open scoped Pointwise

namespace GlobalTheory.CompanionTheory.Conc

theorem norm_integral_ker_le {K : Type} [Field K] [NumberField K] {n : ℕ}
    [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] {β : archGroup K n → ℝ} (hk : Ker ν β)
    (g : archGroup K n → ℂ) {M : ℝ} (hg : ∀ y ∈ tsupport β, ‖g y‖ ≤ M) :
    ‖∫ y, (β y : ℂ) * g y ∂ν‖ ≤ M := by
  have hint : Integrable (fun y => β y * M) ν :=
    (hk.cont.integrable_of_hasCompactSupport hk.cpt).mul_const M
  have hpt : ∀ y, ‖(β y : ℂ) * g y‖ ≤ β y * M := by
    intro y
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hk.nonneg y)]
    by_cases hy : y ∈ tsupport β
    · exact mul_le_mul_of_nonneg_left (hg y hy) (hk.nonneg y)
    · rw [image_eq_zero_of_notMem_tsupport hy]
      simp
  have h := norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
  rwa [integral_mul_const, hk.mass, one_mul] at h

theorem uBnd_sm (K : Type) [Field K] [NumberField K] (n : ℕ)
    [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (ι : Type)
    (f : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) (hk : Ker ν β) (_hf : ∀ i, Continuous (f i))
    (hb : UBnd f m) : UBnd (fun i => sm ν β (f i)) m := by
  intro ω hω hsub t₀ Q hQ
  have hQ' : IsCompact (Q * infEmb K n '' tsupport β) :=
    hQ.mul (hk.cpt.isCompact.image continuous_infEmb)
  obtain ⟨C, hC⟩ := hb ω hω hsub t₀ _ hQ'
  refine ⟨max C 0, fun i b hbω x hx q hq => ?_⟩
  refine norm_integral_ker_le ν hk _ ?_
  intro y hy
  rw [mul_assoc (b * _) q]
  refine (hC i b hbω x hx _ (Set.mul_mem_mul hq (Set.mem_image_of_mem _ hy))).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

end GlobalTheory.CompanionTheory.Conc
end

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_bound_smoothing : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ), Ker ν β → (∀ i, Continuous (f i)) →
  UBnd f m → UBnd (fun i => sm ν β (f i)) m := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Conc.uBnd_sm
end

section
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

noncomputable section

namespace GlobalTheory.CompanionTheory.Conc.SmKill

theorem ctn_sm {K : Type} [Field K] [NumberField K] {n : ℕ} [MeasurableSpace (archGroup K n)]
    [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] {β : archGroup K n → ℝ}
    (hβ : Continuous β) (hβc : HasCompactSupport β) {f : AdelicGLn.AdelicGL K n → ℂ} (hf : Continuous f)
    (r : ℕ) (g : AdelicGLn.AdelicGL K n) :
    Integrable (fun y => (β y : ℂ) * An.ctn r f (g * infEmb K n y)) ν ∧
      An.ctn r (sm ν β f) g = ∫ y, (β y : ℂ) * An.ctn r f (g * infEmb K n y) ∂ν := by
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ (φ : AdelicGLn.AdelicGL K n → ℂ) (h : AdelicGLn.AdelicGL K n),
      An.ctn r φ h = c * constantTerm r φ h := ⟨_, fun _ _ => rfl⟩
  set F : (UPos n r → AdeleRing (𝓞 K) K) × archGroup K n → ℂ :=
    fun p => c * ((β p.2 : ℂ) * f (unipGL p.1 * g * infEmb K n p.2)) with hF
  have hFc : Continuous F :=
    continuous_const.mul ((Complex.continuous_ofReal.comp (hβ.comp continuous_snd)).mul
      (hf.comp ((continuous_unipGL.comp continuous_fst).mul continuous_const |>.mul
        (continuous_infEmb.comp continuous_snd))))
  have hint : Integrable F ((unipMeasure K n r).restrict (unipFundamentalDomain K n r) |>.prod ν) := by
    have e : ((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod ν =
        ((unipMeasure K n r).prod ν).restrict (unipFundamentalDomain K n r ×ˢ Set.univ) := by
      rw [← Measure.restrict_univ (μ := ν), Measure.prod_restrict, Measure.restrict_univ]
    rw [e]
    refine IntegrableOn.of_forall_sdiff_eq_zero
      (hFc.continuousOn.integrableOn_compact (hC.prod hβc.isCompact))
      (measurableSet_unipFundamentalDomain.prod MeasurableSet.univ) fun p hp => ?_
    have hy : p.2 ∉ tsupport β := fun hy => hp.2 ⟨hDC hp.1.1, hy⟩
    simp [hF, image_eq_zero_of_notMem_tsupport hy]
  have hval : ∀ y, ∫ X in unipFundamentalDomain K n r, F (X, y) ∂unipMeasure K n r =
      (β y : ℂ) * An.ctn r f (g * infEmb K n y) := fun y => by
    simp only [hF, hc, constantTerm, mul_assoc]
    rw [integral_const_mul, integral_const_mul]
    ring
  constructor
  · have := hint.swap.integral_prod_left
    refine this.congr (Eventually.of_forall fun y => ?_)
    exact hval y
  · have h := integral_integral_swap (f := fun X y => F (X, y)) hint
    simp only [hval] at h
    rw [← h]
    simp only [hc, constantTerm, sm, hF]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    simp only [integral_const_mul]

end GlobalTheory.CompanionTheory.Conc.SmKill

open GlobalTheory.CompanionTheory.Conc.SmKill in

theorem GlobalTheory.CompanionTheory.Conc.kill_sm : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (f : AdelicGLn.AdelicGL K n → ℂ) (r : ℕ) (p : ℂ[X]), Ker ν β → 0 < r → r < n → Continuous f →
    An.Kill r f p → An.Kill r (sm ν β f) p := by
  intro K _ _ n _ _ ν _ β f r p hk _ _ hf hkill g
  have h1 : ∀ j ∈ Finset.range (p.natDegree + 1),
      p.coeff j * An.ctn r (sm ν β f) (An.aR K n r j * g) =
        ∫ y, p.coeff j * ((β y : ℂ) * An.ctn r f (An.aR K n r j * g * infEmb K n y)) ∂ν := fun j _ => by
    rw [(ctn_sm ν hk.cont hk.cpt hf r _).2, integral_const_mul]
  rw [Finset.sum_congr rfl h1, ← integral_finset_sum _ fun j _ =>
    ((ctn_sm ν hk.cont hk.cpt hf r _).1).const_mul _]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
  have h2 := hkill (g * infEmb K n y)
  have h3 : ∑ j ∈ Finset.range (p.natDegree + 1),
      p.coeff j * ((β y : ℂ) * An.ctn r f (An.aR K n r j * g * infEmb K n y)) =
      (β y : ℂ) * ∑ j ∈ Finset.range (p.natDegree + 1),
        p.coeff j * An.ctn r f (An.aR K n r j * (g * infEmb K n y)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc (An.aR K n r j)]
    ring
  simp only [Pi.zero_apply]
  rw [h3, h2, mul_zero]

end
end

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.killed_by_polynomial_smoothing : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (f : AdelicGLn.AdelicGL K n → ℂ) (r : ℕ) (p : ℂ[X]), Ker ν β → 0 < r → r < n → Continuous f →
  An.Kill r f p → An.Kill r (sm ν β f) p := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Conc.kill_sm
end

section
section
open scoped ENNReal NNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.BesselPt

theorem sq_tsum_le {ι : Type*} (t : ι → ℝ≥0) (k : ℕ) (h : (Function.support t).encard ≤ k) :
    (∑' i, (t i : ℝ≥0∞)) ^ 2 ≤ k * ∑' i, (t i : ℝ≥0∞) ^ 2 := by
  have hfin : (Function.support t).Finite := Set.finite_of_encard_le_coe h
  set S := hfin.toFinset with hS
  have hcard : S.card ≤ k := by
    have : (S.card : ℕ∞) ≤ k := by
      rw [← Set.encard_coe_eq_coe_finsetCard, hS, hfin.coe_toFinset]; exact h
    exact_mod_cast this
  have hz : ∀ i, i ∉ S → t i = 0 := fun i hi => by simpa [hS] using hi
  have e1 : ∑' i, (t i : ℝ≥0∞) = ∑ i ∈ S, (t i : ℝ≥0∞) :=
    tsum_eq_sum (fun i hi => by simp [hz i hi])
  have e2 : ∑' i, (t i : ℝ≥0∞) ^ 2 = ∑ i ∈ S, (t i : ℝ≥0∞) ^ 2 :=
    tsum_eq_sum (fun i hi => by simp [hz i hi])
  rw [e1, e2]
  have h3 : (∑ i ∈ S, t i) ^ 2 ≤ k * ∑ i ∈ S, t i ^ 2 := by
    have h4 : ((∑ i ∈ S, (t i : ℝ)) ^ 2) ≤ S.card * ∑ i ∈ S, (t i : ℝ) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h5 : (∑ i ∈ S, t i) ^ 2 ≤ S.card * ∑ i ∈ S, t i ^ 2 := by exact_mod_cast h4
    exact h5.trans (by gcongr)
  exact_mod_cast h3

theorem sq_lintegral_mul_le {X : Type*} [MeasurableSpace X] (ν : Measure X) {f g : X → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hg : AEMeasurable g ν) :
    (∫⁻ a, f a * g a ∂ν) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂ν) * ∫⁻ a, g a ^ 2 ∂ν := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hf hg
  simp only [Pi.mul_apply, ENNReal.rpow_ofNat] at h
  refine (pow_le_pow_left' h 2).trans (le_of_eq ?_)
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ _), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  norm_num

theorem encard_support_le {G : Type*} [Group G] [TopologicalSpace G] (Γ : Subgroup G) (α : G → ℂ) (x w : G)
    (k : ℕ)
    (hk : {γ : G | γ ∈ Γ ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k) :
    (Function.support fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊).encard ≤ k := by
  rcases (Function.support fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊).eq_empty_or_nonempty with h0 | ⟨γ₀, h₀⟩
  · simp [h0]
  refine le_trans ?_ hk
  have hinj : Set.InjOn (fun γ : Γ => (γ : G) * (γ₀ : G)⁻¹)
      (Function.support fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊) := by
    intro a _ b _ hab
    exact Subtype.ext (mul_right_cancel hab)
  rw [← hinj.encard_image]
  refine Set.encard_le_encard ?_
  rintro _ ⟨γ, hγ, rfl⟩
  have mem : ∀ c : Γ, c ∈ (Function.support fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊) →
      x⁻¹ * ((c : G) * w) ∈ tsupport α := fun c hc => by
    apply subset_tsupport
    simpa [Function.mem_support] using hc
  refine ⟨Γ.mul_mem γ.2 (Γ.inv_mem γ₀.2), _, mem γ hγ, _, mem γ₀ h₀, ?_⟩
  group

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

theorem sq_lintegral_le (μ : Measure G) [μ.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ] {F : Set G}
    (hF : IsFundamentalDomain Γ F μ) {α ψ : G → ℂ} (hα : Continuous α) (hψ : Continuous ψ)
    (hinv : ∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) (hn : (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1) (x : G) (k : ℕ)
    (hk : {γ : G | γ ∈ Γ ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k) :
    (∫⁻ y, ‖α y‖ₑ * ‖ψ (x * y)‖ₑ ∂μ) ^ 2 ≤ k * ∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ := by
  set a : G → ℝ≥0∞ := fun w => ‖α (x⁻¹ * w)‖ₑ with ha
  have ham : Measurable a := (hα.comp (continuous_const.mul continuous_id)).enorm.measurable
  have hψm : Measurable fun w => ‖ψ w‖ₑ := hψ.enorm.measurable
  have htr : ∀ γ : Γ, Measurable fun w => a ((γ : G) * w) :=
    fun γ => ham.comp (measurable_const_mul _)
  have e1 : ∫⁻ y, ‖α y‖ₑ * ‖ψ (x * y)‖ₑ ∂μ = ∫⁻ w in F, (∑' γ : Γ, a ((γ : G) * w)) * ‖ψ w‖ₑ ∂μ := by
    have h1 := lintegral_mul_left_eq_self (μ := μ) (fun w => a w * ‖ψ w‖ₑ) x
    simp only [ha, inv_mul_cancel_left] at h1
    rw [h1, hF.lintegral_eq_tsum'', ← lintegral_tsum]
    · refine lintegral_congr fun w => ?_
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun γ => ?_
      rw [Subgroup.smul_def, smul_eq_mul, hinv _ γ.2]
    · intro γ
      simp only [Subgroup.smul_def, smul_eq_mul, hinv _ γ.2]
      exact ((htr γ).mul hψm).aemeasurable
  have e2 : ∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ = ∫⁻ w in F, ∑' γ : Γ, a ((γ : G) * w) ^ 2 ∂μ := by
    have h1 := lintegral_mul_left_eq_self (μ := μ) (fun w => a w ^ 2) x
    simp only [ha, inv_mul_cancel_left] at h1
    rw [h1, hF.lintegral_eq_tsum'', ← lintegral_tsum]
    · rfl
    · intro γ
      exact ((htr γ).pow_const 2).aemeasurable
  have hK : Measurable fun w => ∑' γ : Γ, a ((γ : G) * w) := Measurable.ennreal_tsum htr
  rw [e1, e2, ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top k)]
  refine (sq_lintegral_mul_le _ hK.aemeasurable hψm.aemeasurable).trans ?_
  rw [hn, mul_one]
  refine lintegral_mono fun w => ?_
  have := sq_tsum_le (fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊) k (encard_support_le Γ α x w k hk)
  simpa [ha, enorm_eq_nnnorm] using this

theorem pointwise (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (Γ : Subgroup G) [Countable Γ]
    {α : G → ℂ} {δ : ℝ} {F : Set G} (hα : Continuous α) (hc : HasCompactSupport α) (hδ : 0 < δ)
    (hF : IsFundamentalDomain Γ F μ) : ∃ C₀ : ℝ, ∀ ψ : G → ℂ, Continuous ψ → (∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) →
      (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) → (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 →
      ∀ (x : G) (k : ℕ), {γ : G | γ ∈ Γ ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k →
        ‖ψ x‖ ^ 2 ≤ C₀ * k := by
  refine ⟨(δ ^ 2)⁻¹ * (∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ).toReal, ?_⟩
  rintro ψ hψ hinv ⟨s, hs, hrep⟩ hn x k hk
  have hA : (∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ) ≠ ⊤ := by
    have hc2 : HasCompactSupport ((fun z : ℂ => ‖z‖ ^ 2) ∘ α) :=
      HasCompactSupport.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) hc (by simp)
    have hi : Integrable ((fun z : ℂ => ‖z‖ ^ 2) ∘ α) μ :=
      Continuous.integrable_of_hasCompactSupport ((continuous_norm.pow 2).comp hα) hc2
    have := hi.2.ne
    simpa [HasFiniteIntegral, enorm_pow] using this
  have h1 : ‖s‖ₑ * ‖ψ x‖ₑ ≤ ∫⁻ y, ‖α y‖ₑ * ‖ψ (x * y)‖ₑ ∂μ := by
    rw [← enorm_mul, ← hrep x]
    exact (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (by simp only [enorm_mul]))
  have h3 : (‖s‖ₑ * ‖ψ x‖ₑ) ^ 2 ≤ k * ∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ :=
    (pow_le_pow_left' h1 2).trans (sq_lintegral_le μ _ hF hα hψ hinv hn x k hk)
  have h4 : (‖s‖ * ‖ψ x‖) ^ 2 ≤ k * (∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) hA) h3
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm] using this
  have hδ2 : 0 < δ ^ 2 := by positivity
  have h5 : δ ^ 2 * ‖ψ x‖ ^ 2 ≤ (‖s‖ * ‖ψ x‖) ^ 2 := by
    rw [mul_pow]
    gcongr
  have h6 := h5.trans h4
  rw [mul_assoc, inv_mul_eq_div, le_div_iff₀ hδ2]
  nlinarith [h6]

end GlobalTheory.CompanionTheory.Conc.BesselPt

open GlobalTheory.CompanionTheory.Conc.BesselPt in

theorem GlobalTheory.CompanionTheory.Conc.besselPt : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N)), Continuous α → HasCompactSupport α → 0 < δ →
  IsFundamentalDomain (latticeGL E N) F μ → ∃ C₀ : ℝ, ∀ ψ : GA E N → ℂ, Continuous ψ → (∀ γ ∈ latticeGL E N, ∀ g, ψ (γ * g) = ψ g) →
  (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) → (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 →
  ∀ (x : GA E N) (k : ℕ), {γ : GA E N | γ ∈ latticeGL E N ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k →
    ‖ψ x‖ ^ 2 ≤ C₀ * k := by
  intro E _ _ _ N _ _ μ _ α δ F hα hc hδ hF
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  exact pointwise μ (latticeGL E N) hα hc hδ hF
end

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_eigenfunction_bound : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N)), Continuous α → HasCompactSupport α → 0 < δ →
  IsFundamentalDomain (latticeGL E N) F μ → ∃ C₀ : ℝ, ∀ ψ : GA E N → ℂ, Continuous ψ → (∀ γ ∈ latticeGL E N, ∀ g, ψ (γ * g) = ψ g) →
  (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) → (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 →
  ∀ (x : GA E N) (k : ℕ), {γ : GA E N | γ ∈ latticeGL E N ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k →
    ‖ψ x‖ ^ 2 ≤ C₀ * k := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Conc.besselPt
end

section
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.Conc

theorem lintegral_sq_le_of_average {G Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] (F : Set G) (hF : IsFundamentalDomain Γ F μ)
    (ν : Measure Y) (b : Y → ℝ≥0∞) (hb : Measurable b) (hmass : ∫⁻ y, b y ∂ν = 1)
    (k : Y → G) (hk : Continuous k) (f : G → ℂ) (hf : Continuous f)
    (hinv : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) (s : G → ℂ)
    (hs : ∀ x, ‖s x‖ₑ ≤ ∫⁻ y, b y * ‖f (x * k y)‖ₑ ∂ν) :
    ∫⁻ x in F, ‖s x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ := by
  set p := ν.withDensity b with hp
  haveI : IsProbabilityMeasure p := ⟨by rw [hp, withDensity_apply _ MeasurableSet.univ]; simpa using hmass⟩
  have hm : ∀ x, Continuous fun y => f (x * k y) := fun x => hf.comp (continuous_const.mul hk)
  have hsq : ∀ {X : Type _} [MeasurableSpace X] (m : Measure X) (g : X → ℂ),
      eLpNorm g 2 m ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂m := by
    intro X _ m g
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num [ENNReal.rpow_two]
  have hpt : ∀ x, ‖s x‖ₑ ^ 2 ≤ ∫⁻ y, ‖f (x * k y)‖ₑ ^ 2 ∂p := by
    intro x
    have h1 : ∫⁻ y, b y * ‖f (x * k y)‖ₑ ∂ν = ∫⁻ y, ‖f (x * k y)‖ₑ ∂p := by
      rw [hp, lintegral_withDensity_eq_lintegral_mul ν hb (hm x).measurable.enorm]
      rfl
    have h2 := eLpNorm_le_eLpNorm_of_exponent_le (p := 1) (q := 2) (μ := p) (by norm_num)
      (hm x).measurable.aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm] at h2
    rw [← hsq p]
    exact pow_le_pow_left' ((hs x).trans (h1.le.trans h2)) 2
  have hΓ : ∀ (γ : Γ) (x : G), ‖f (γ • x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2 := fun γ x => by
    rw [Subgroup.smul_def, smul_eq_mul, hinv _ γ.2]
  have htr : ∀ h : G, ∫⁻ x in F, ‖f (x * h)‖ₑ ^ 2 ∂μ = ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ := by
    intro h
    have hF' : IsFundamentalDomain Γ (MulOpposite.op h • F) μ := hF.smul_of_comm _
    have e1 := (measurePreserving_mul_right μ h).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.mulRight h).measurableEmbedding (fun z => ‖f z‖ₑ ^ 2) (MulOpposite.op h • F)
    have e2 : (fun x => x * h) ⁻¹' (MulOpposite.op h • F) = F := by
      ext x
      simp [Set.mem_smul_set_iff_inv_smul_mem]
    rw [e2] at e1
    rw [e1]
    exact hF'.setLIntegral_eq hF _ hΓ
  have hjoint : Measurable (Function.uncurry fun (x : G) (y : Y) => ‖f (x * k y)‖ₑ ^ 2) :=
    ((hf.comp (continuous_fst.mul (hk.comp continuous_snd))).measurable.enorm).pow_const 2
  calc ∫⁻ x in F, ‖s x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x in F, ∫⁻ y, ‖f (x * k y)‖ₑ ^ 2 ∂p ∂μ := lintegral_mono hpt
    _ = ∫⁻ y, ∫⁻ x in F, ‖f (x * k y)‖ₑ ^ 2 ∂μ ∂p := lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ _y, ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ ∂p := lintegral_congr fun y => htr (k y)
    _ = ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ := by simp

theorem sm_sq_mass_le : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)] (ν : Measure (archGroup E N)) [ν.IsHaarMeasure] (F : Set (GA E N)) (β : archGroup E N → ℝ), IsFundamentalDomain (latticeGL E N) F μ → Ker ν β →
  ∀ f : GA E N → ℂ, Continuous f → (∀ γ ∈ latticeGL E N, ∀ g, f (γ * g) = f g) →
  ∫⁻ x in F, ‖sm ν β f x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ := by
  intro E _ _ _ N _ _ μ _ _ _ ν _ F β hF hβ f hf hinv
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  haveI : SecondCountableTopology (GA E N) := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E N
  haveI : LocallyCompactSpace (GA E N) := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E N
  haveI : μ.IsMulRightInvariant := GlobalTheory.T.haar_right_invariant_totally_complex E N μ
  refine lintegral_sq_le_of_average μ (latticeGL E N) F hF ν (fun y => ENNReal.ofReal (β y))
    hβ.cont.measurable.ennreal_ofReal ?_ (infEmb E N) continuous_infEmb f hf hinv (sm ν β f) ?_
  · rw [← ofReal_integral_eq_lintegral_ofReal
      (hβ.cont.integrable_of_hasCompactSupport hβ.cpt) (Eventually.of_forall hβ.nonneg), hβ.mass]
    simp
  · intro x
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun y => ?_))
    rw [enorm_mul]
    congr 1
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (hβ.nonneg y)]

end GlobalTheory.CompanionTheory.Conc

end
end

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothing_fundamental_domain_integral : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)] (ν : Measure (archGroup E N)) [ν.IsHaarMeasure] (F : Set (GA E N)) (β : archGroup E N → ℝ), IsFundamentalDomain (latticeGL E N) F μ → Ker ν β →
  ∀ f : GA E N → ℂ, Continuous f → (∀ γ ∈ latticeGL E N, ∀ g, f (γ * g) = f g) →
  ∫⁻ x in F, ‖sm ν β f x‖ₑ ^ 2 ∂μ ≤ ∫⁻ x in F, ‖f x‖ₑ ^ 2 ∂μ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Conc.sm_sq_mass_le
end

section
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

noncomputable section

namespace GlobalTheory.CompanionTheory.Conc

theorem lintegral_sq_le {Y : Type*} [MeasurableSpace Y] (P : Measure Y) [IsProbabilityMeasure P]
    (g : Y → ℝ≥0∞) (hg : AEMeasurable g P) : (∫⁻ y, g y ∂P) ^ 2 ≤ ∫⁻ y, g y ^ 2 ∂P := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two hg
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
  have h2 := pow_le_pow_left' h 2
  have h3 : ((∫⁻ y, g y ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))) ^ 2 = ∫⁻ y, g y ^ (2 : ℝ) ∂P := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [h3] at h2
  simpa [ENNReal.rpow_ofNat] using h2

theorem enorm_sub_sm_sq_le (E : Type) [Field E] [NumberField E] (N : ℕ)
    [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)]
    (ν : Measure (archGroup E N)) [ν.IsHaarMeasure] (β : archGroup E N → ℝ) (hk : Ker ν β)
    (f : AdelicGLn.AdelicGL E N → ℂ) (hf : Continuous f) (x : AdelicGLn.AdelicGL E N) :
    ‖f x - sm ν β f x‖ₑ ^ 2 ≤ ∫⁻ y, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2
      ∂(ν.withDensity fun y => ENNReal.ofReal (β y)) := by
  have hwm : Measurable fun y => ENNReal.ofReal (β y) := hk.cont.measurable.ennreal_ofReal
  have : IsProbabilityMeasure (ν.withDensity fun y => ENNReal.ofReal (β y)) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hk.cont.integrable_of_hasCompactSupport hk.cpt)
        (Eventually.of_forall hk.nonneg), hk.mass, ENNReal.ofReal_one]
  have hc1 : Continuous fun y => f (x * infEmb E N y) :=
    hf.comp (continuous_const.mul continuous_infEmb)
  have hi1 : Integrable (fun y => (β y : ℂ) * f (x * infEmb E N y)) ν :=
    ((Complex.continuous_ofReal.comp hk.cont).mul hc1).integrable_of_hasCompactSupport
      (hk.cpt.comp_left Complex.ofReal_zero |>.mul_right)
  have hi2 : Integrable (fun y => (β y : ℂ) * f x) ν :=
    ((Complex.continuous_ofReal.comp hk.cont).mul continuous_const).integrable_of_hasCompactSupport
      (hk.cpt.comp_left Complex.ofReal_zero |>.mul_right)
  have hmass : ∫ y, (β y : ℂ) * f x ∂ν = f x := by
    rw [integral_mul_const, integral_complex_ofReal, hk.mass]
    simp
  have heq : f x - sm ν β f x = ∫ y, (β y : ℂ) * (f x - f (x * infEmb E N y)) ∂ν := by
    simp only [mul_sub]
    rw [integral_sub hi2 hi1, hmass]
    rfl
  have hgm : Measurable fun y => ‖f (x * infEmb E N y) - f x‖ₑ :=
    (continuous_enorm.comp (hc1.sub continuous_const)).measurable
  have hle : ‖f x - sm ν β f x‖ₑ ≤ ∫⁻ y, ‖f (x * infEmb E N y) - f x‖ₑ
      ∂(ν.withDensity fun y => ENNReal.ofReal (β y)) := by
    rw [heq, lintegral_withDensity_eq_lintegral_mul ν hwm hgm]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    have hb : ‖(β y : ℂ)‖ₑ = ENNReal.ofReal (β y) := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hk.nonneg y)]
    rw [enorm_mul, hb, enorm_sub_rev]
    rfl
  exact (pow_le_pow_left' hle 2).trans (lintegral_sq_le _ _ hgm.aemeasurable)

end GlobalTheory.CompanionTheory.Conc

theorem GlobalTheory.CompanionTheory.Conc.smNear : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)] (ν : Measure (archGroup E N)) [ν.IsHaarMeasure] (F : Set (GA E N)) (β : archGroup E N → ℝ) (c : ℝ≥0∞), IsFundamentalDomain (latticeGL E N) F μ → Ker ν β →
  ∀ f : GA E N → ℂ, Continuous f → (∀ y ∈ tsupport β, ∫⁻ x in F, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2 ∂μ ≤ c) →
  ∫⁻ x in F, ‖f x - sm ν β f x‖ₑ ^ 2 ∂μ ≤ c := by
  intro E _ _ _ N _ _ μ _ _ _ ν _ F β c _ hk f hf hc
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  have : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → Ad E))
  have : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : LocallyCompactSpace (GA E N) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → Ad E))
  have : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (GA E N) := Units.isEmbedding_embedProduct.secondCountableTopology
  have : SigmaCompactSpace (GA E N) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SFinite μ := inferInstance
  have hwm : Measurable fun y => ENNReal.ofReal (β y) := hk.cont.measurable.ennreal_ofReal
  set P : Measure (archGroup E N) := ν.withDensity fun y => ENNReal.ofReal (β y) with hP
  have : IsProbabilityMeasure P := by
    refine ⟨?_⟩
    rw [hP, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hk.cont.integrable_of_hasCompactSupport hk.cpt)
        (Eventually.of_forall hk.nonneg), hk.mass, ENNReal.ofReal_one]
  have hG : Continuous fun p : GA E N × archGroup E N => ‖f (p.1 * infEmb E N p.2) - f p.1‖ₑ ^ 2 :=
    (ENNReal.continuous_pow 2).comp (continuous_enorm.comp
      ((hf.comp (continuous_fst.mul (continuous_infEmb.comp continuous_snd))).sub
        (hf.comp continuous_fst)))
  have hae : ∀ᵐ y ∂P, y ∈ tsupport β := by
    rw [hP, ae_withDensity_iff hwm]
    refine Eventually.of_forall fun y hy => subset_tsupport _ ?_
    intro h0
    exact hy (by rw [h0, ENNReal.ofReal_zero])
  calc ∫⁻ x in F, ‖f x - sm ν β f x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in F, ∫⁻ y, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2 ∂P ∂μ :=
        lintegral_mono fun x => enorm_sub_sm_sq_le E N ν β hk f hf x
    _ = ∫⁻ y, ∫⁻ x in F, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2 ∂μ ∂P :=
        lintegral_lintegral_swap hG.measurable.aemeasurable
    _ ≤ ∫⁻ _, c ∂P := lintegral_mono_ae (hae.mono fun y hy => hc y hy)
    _ = c := by simp
end
end

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothing_fundamental_domain_bound : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)] (ν : Measure (archGroup E N)) [ν.IsHaarMeasure] (F : Set (GA E N)) (β : archGroup E N → ℝ) (c : ℝ≥0∞), IsFundamentalDomain (latticeGL E N) F μ → Ker ν β →
  ∀ f : GA E N → ℂ, Continuous f → (∀ y ∈ tsupport β, ∫⁻ x in F, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2 ∂μ ≤ c) →
  ∫⁻ x in F, ‖f x - sm ν β f x‖ₑ ^ 2 ∂μ ≤ c := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Conc.smNear
end

section
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.LevelU

theorem exists_level : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (L : Subgroup (GL (Fin N) (Af E))), IsOpen (L : Set (GL (Fin N) (Af E))) →
  ∃ U : Subgroup (AdelicGLn.integralFiniteGL E N), IsOpen (U : Set (AdelicGLn.integralFiniteGL E N)) ∧ ∀ u : U, ∃ k ∈ L,
    finEmb E N ((u : AdelicGLn.integralFiniteGL E N) : AdelicGLn.FiniteAdelicGL E N) = finGL E N k := by
  intro E _ _ _ N L hL
  refine ⟨L.subgroupOf (AdelicGLn.integralFiniteGL E N), hL.preimage continuous_subtype_val, ?_⟩
  intro u
  exact ⟨_, Subgroup.mem_subgroupOf.1 u.2, GlobalTheory.CompanionTheory.AutLevel.finEmb_eq_finGL E N _⟩

end GlobalTheory.CompanionTheory.Conc.LevelU
end

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_integral_subgroup : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (L : Subgroup (GL (Fin N) (Af E))), IsOpen (L : Set (GL (Fin N) (Af E))) →
  ∃ U : Subgroup (AdelicGLn.integralFiniteGL E N), IsOpen (U : Set (AdelicGLn.integralFiniteGL E N)) ∧ ∀ u : U, ∃ k ∈ L,
    finEmb E N ((u : AdelicGLn.integralFiniteGL E N) : AdelicGLn.FiniteAdelicGL E N) = finGL E N k := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Conc.LevelU.exists_level
end

section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

noncomputable section

namespace GlobalTheory.CompanionTheory.Conc

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem ubnd_mono {ι : Type*} {f : ι → AdelicGLn.AdelicGL K n → ℂ} {m m' : ℕ → ℝ}
    (hm : ∀ r, 0 < r → r < n → m r ≤ m' r) (h : UBnd f m) : UBnd f m' := by
  intro ω hω hB t₀ Q hQ
  obtain ⟨C, hC⟩ := h ω hω hB t₀ Q hQ
  refine ⟨max C 0 * Real.exp (∑ r ∈ Finset.range n,
    (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)), ?_⟩
  intro i b hb x hx q hq
  have h1 := hC i b hb x hx q hq
  have hs : ∑ r ∈ Finset.range n, m r * An.sr x r ≤
      (∑ r ∈ Finset.range n, (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)) +
        ∑ r ∈ Finset.range n, m' r * An.sr x r := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    by_cases hr : 0 < r ∧ r < n
    · rw [if_pos hr]
      have := mul_le_mul_of_nonneg_left (hx r) (sub_nonneg.2 (hm r hr.1 hr.2))
      nlinarith
    · rw [if_neg hr, GlobalTheory.CompanionTheory.AnBoot.sr_eq_zero x hr]
      simp
  calc ‖f i (b * An.tor K x * q)‖ ≤ C * Real.exp (∑ r ∈ Finset.range n, m r * An.sr x r) := h1
    _ ≤ max C 0 * Real.exp (∑ r ∈ Finset.range n, m r * An.sr x r) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C 0 * Real.exp ((∑ r ∈ Finset.range n,
          (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)) +
            ∑ r ∈ Finset.range n, m' r * An.sr x r) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hs) (le_max_right _ _)
    _ = max C 0 * Real.exp (∑ r ∈ Finset.range n,
          (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)) *
            Real.exp (∑ r ∈ Finset.range n, m' r * An.sr x r) := by
        rw [Real.exp_add, mul_assoc]

theorem ubnd_add {ι : Type*} {f g : ι → AdelicGLn.AdelicGL K n → ℂ} {m : ℕ → ℝ} (hf : UBnd f m) (hg : UBnd g m) :
    UBnd (fun i y => f i y + g i y) m := by
  intro ω hω hB t₀ Q hQ
  obtain ⟨C, hC⟩ := hf ω hω hB t₀ Q hQ
  obtain ⟨D, hD⟩ := hg ω hω hB t₀ Q hQ
  refine ⟨C + D, fun i b hb x hx q hq => ?_⟩
  have h1 := hC i b hb x hx q hq
  have h2 := hD i b hb x hx q hq
  calc ‖f i (b * An.tor K x * q) + g i (b * An.tor K x * q)‖
      ≤ ‖f i (b * An.tor K x * q)‖ + ‖g i (b * An.tor K x * q)‖ := norm_add_le _ _
    _ ≤ C * Real.exp (∑ r ∈ Finset.range n, m r * An.sr x r) +
          D * Real.exp (∑ r ∈ Finset.range n, m r * An.sr x r) := add_le_add h1 h2
    _ = (C + D) * Real.exp (∑ r ∈ Finset.range n, m r * An.sr x r) := by ring

section Iter

variable [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]

theorem step {β : archGroup K n → ℝ} (hβ : Ker ν β) {ι : Type} {f : ι → AdelicGLn.AdelicGL K n → ℂ} {m : ℕ → ℝ}
    {r D : ℕ} {κ' κ : ℝ} {p : ι → ℂ[X]} (h0 : 0 < r) (h1 : r < n) (hf : UFam f) (hb : UBnd f m) (hk : κ' < κ)
    (hp : ∀ i, (p i).Monic ∧ (p i).natDegree ≤ D ∧ An.Kill r (sm ν β (f i)) (p i) ∧
      ∀ z, (p i).IsRoot z → ‖z‖ ≤ Real.exp κ') :
    UBnd (fun i => sm ν β (f i)) (Function.update m r (max (m r - 1) κ)) := by
  have hf₁ : UFam (fun i => sm ν β (f i)) := GlobalTheory.T.uniform_family_smoothing K n ν β ι f hβ hf
  have hb₁ : UBnd (fun i => sm ν β (f i)) m := GlobalTheory.T.uniform_bound_smoothing K n ν β ι f m hβ hf.cont hb
  have hct := GlobalTheory.T.uniform_bound_constant_term K n ι (fun i => sm ν β (f i)) m r D κ' κ p h0 h1 hf₁ hb₁ hk hp
  have hdiff := GlobalTheory.T.uniform_bound_of_archimedean_lipschitz K n ι f (fun i => sm ν β (f i)) m r h0 h1 hf₁ (fun R => by
    obtain ⟨Q₀, C, hQ₀, hC, h⟩ := GlobalTheory.T.smoothing_lipschitz_bound K n ν β hβ R
    exact ⟨Q₀, C, hQ₀, hC, fun i g Y M hY hR hM => h (f i) (hf.cont i) g Y M hY hR hM⟩) hb
  have a : UBnd (fun i g => sm ν β (f i) g - An.ctn r (sm ν β (f i)) g) (Function.update m r (max (m r - 1) κ)) :=
    ubnd_mono (fun s _ _ => GlobalTheory.CompanionTheory.AnBoot.update_le_update m r (le_max_left _ _) s) hdiff
  have b : UBnd (fun i => An.ctn r (sm ν β (f i))) (Function.update m r (max (m r - 1) κ)) :=
    ubnd_mono (fun s _ _ => GlobalTheory.CompanionTheory.AnBoot.update_le_update m r (le_max_right _ _) s) hct
  have c := ubnd_add a b
  simpa using c

theorem iter_fam {β : archGroup K n → ℝ} (hβ : Ker ν β) {ι : Type} {f : ι → AdelicGLn.AdelicGL K n → ℂ}
    (hf : UFam f) (j : ℕ) : UFam (fun i => (sm ν β)^[j] (f i)) := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
    simp only [Function.iterate_succ_apply']
    exact GlobalTheory.T.uniform_family_smoothing K n ν β ι _ hβ ih

theorem iter_kill {β : archGroup K n → ℝ} (hβ : Ker ν β) {ι : Type} {f : ι → AdelicGLn.AdelicGL K n → ℂ} {r : ℕ}
    {p : ℂ[X]} (h0 : 0 < r) (h1 : r < n) (hf : UFam f) (i : ι) (hk : An.Kill r (f i) p) (j : ℕ) :
    An.Kill r ((sm ν β)^[j] (f i)) p := by
  induction j with
  | zero => simpa using hk
  | succ j ih =>
    simp only [Function.iterate_succ_apply']
    exact GlobalTheory.T.killed_by_polynomial_smoothing K n ν β _ r p hβ h0 h1 ((iter_fam ν hβ hf j).cont i) ih

theorem iter_one {β : archGroup K n → ℝ} (hβ : Ker ν β) {ι : Type} {f : ι → AdelicGLn.AdelicGL K n → ℂ} {m : ℕ → ℝ}
    {r D : ℕ} {κ' κ : ℝ} {p : ι → ℂ[X]} (h0 : 0 < r) (h1 : r < n) (hf : UFam f) (hb : UBnd f m) (hk : κ' < κ)
    (hp : ∀ i, (p i).Monic ∧ (p i).natDegree ≤ D ∧ An.Kill r (f i) (p i) ∧
      ∀ z, (p i).IsRoot z → ‖z‖ ≤ Real.exp κ') (j : ℕ) :
    UBnd (fun i => (sm ν β)^[j] (f i)) (Function.update m r (max (m r - j) κ)) := by
  induction j with
  | zero =>
    refine ubnd_mono (fun s _ _ => ?_) hb
    by_cases hs : s = r
    · subst hs
      simp
    · simp [Function.update_of_ne hs]
  | succ j ih =>
    have := step ν hβ (r := r) (D := D) (κ' := κ') (κ := κ) (p := p) h0 h1 (iter_fam ν hβ hf j) ih hk
      (fun i => ⟨(hp i).1, (hp i).2.1, by
        have := iter_kill ν hβ h0 h1 hf i (hp i).2.2.1 (j + 1)
        rwa [Function.iterate_succ_apply'] at this, (hp i).2.2.2⟩)
    simp only [Function.iterate_succ_apply']
    rw [Function.update_self, Function.update_idem] at this
    refine ubnd_mono (fun s _ _ => GlobalTheory.CompanionTheory.AnBoot.update_le_update m r ?_ s) this
    push_cast
    refine max_le ?_ (le_max_right _ _)
    rcases le_total (m r - j) κ with h' | h'
    · rw [max_eq_right h']
      exact le_trans (by linarith) (le_max_right _ _)
    · rw [max_eq_left h']
      exact le_trans (by linarith) (le_max_left _ _)

theorem iterU {ι : Type} {f : ι → AdelicGLn.AdelicGL K n → ℂ} {M : ℝ} {κ' κ : ℕ → ℝ} {D : ℕ} {p : ℕ → ι → ℂ[X]}
    (hf : UFam f) (hb : UBnd f fun _ => M)
    (hp : ∀ r, 0 < r → r < n → κ' r < κ r ∧ ∀ i, (p r i).Monic ∧ (p r i).natDegree ≤ D ∧ An.Kill r (f i) (p r i) ∧
      ∀ z, (p r i).IsRoot z → ‖z‖ ≤ Real.exp (κ' r)) :
    ∃ k : ℕ, ∀ β, Ker ν β → UBnd (fun i => (sm ν β)^[k] (f i)) κ := by
  classical
  have key : ∀ s : Finset ℕ, (∀ r ∈ s, 0 < r ∧ r < n) → ∃ k : ℕ, ∀ β, Ker ν β →
      UBnd (fun i => (sm ν β)^[k] (f i)) (fun r => if r ∈ s then κ r else M) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨0, fun β _ => by simpa using hb⟩
    | insert a s ha ih =>
      intro hs
      obtain ⟨k, hk⟩ := ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))
      obtain ⟨h0, h1⟩ := hs a (Finset.mem_insert_self a s)
      obtain ⟨j, hj⟩ := exists_nat_ge (M - κ a)
      refine ⟨j + k, fun β hβ => ?_⟩
      have hfk := iter_fam ν hβ hf k
      have := iter_one ν hβ (D := D) (κ' := κ' a) (κ := κ a) (p := p a) h0 h1 hfk (hk β hβ) (hp a h0 h1).1
        (fun i => ⟨((hp a h0 h1).2 i).1, ((hp a h0 h1).2 i).2.1,
          iter_kill ν hβ h0 h1 hf i ((hp a h0 h1).2 i).2.2.1 k, ((hp a h0 h1).2 i).2.2.2⟩) j
      simp only [Function.iterate_add_apply]
      refine ubnd_mono (fun r _ _ => ?_) this
      have hna : a ∉ s := ha
      by_cases hr : r = a
      · subst hr
        simp only [Function.update_self, Finset.mem_insert, true_or, if_true, hna, if_false]
        exact max_le (by linarith) le_rfl
      · simp [Function.update_of_ne hr, Finset.mem_insert, hr]
  obtain ⟨k, hk⟩ := key (Finset.Ioo 0 n) (fun r hr => Finset.mem_Ioo.1 hr)
  refine ⟨k, fun β hβ => ubnd_mono (fun r h0 h1 => ?_) (hk β hβ)⟩
  simp [h0, h1]

end Iter

theorem initU (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)]
    [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N))
    (hα : Continuous α) (hαc : HasCompactSupport α) (hδ : 0 < δ) (hF : IsFundamentalDomain (latticeGL E N) F μ) :
    ∃ M : ℝ, ∀ (ι : Type) (f : ι → GA E N → ℂ), (∀ i, Continuous (f i)) →
      (∀ i, ∀ γ ∈ latticeGL E N, ∀ g, f i (γ * g) = f i g) →
      (∀ i, ∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * f i (x * y) ∂μ = s * f i x) →
      (∀ i, (∫⁻ x in F, ‖f i x‖ₑ ^ 2 ∂μ) = 1) → UBnd f (fun _ => M) := by
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.T.kernel_eigenfunction_bound E N μ α δ F hα hαc hδ hF
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.T.finite_lattice_points_siegel E N
  refine ⟨M / 2, fun ι f hc hl hs hn ω hω hωB t₀ Q hQ => ?_⟩
  obtain ⟨C, hC⟩ := hM (tsupport α) ω t₀ Q hαc hω hωB hQ
  set c : ℝ := Real.exp (M * ((N : ℝ) * |t₀|)) with hc'
  refine ⟨Real.sqrt (|C₀| * (|C| + c)), fun i b hb x hx q hq => ?_⟩
  set S : ℝ := ∑ r ∈ Finset.range N, An.sr x r with hS
  have hsum : ∑ r ∈ Finset.range N, (M / 2) * An.sr x r = M / 2 * S := by rw [hS, Finset.mul_sum]
  have hS0 : -((N : ℝ) * |t₀|) ≤ S := by
    have : ∑ r ∈ Finset.range N, (-|t₀|) ≤ S := Finset.sum_le_sum fun r _ => by
      have := hx r
      have := le_abs_self t₀
      linarith
    simpa using this
  set g := b * An.tor E x * q with hg
  set k : ℕ := ⌈C * Real.exp (M * S)⌉₊ with hk
  have h1 := hC₀ (f i) (hc i) (hl i) (hs i) (hn i) g k (by
    refine le_trans (Set.encard_le_encard ?_) (hC b hb x hx q hq)
    intro γ hγ
    exact hγ)
  have hE : 0 < Real.exp (M * S) := Real.exp_pos _
  have hone : 1 ≤ c * Real.exp (M * S) := by
    rw [hc', ← Real.exp_add]
    apply Real.one_le_exp
    nlinarith
  have hkle : (k : ℝ) ≤ (|C| + c) * Real.exp (M * S) := by
    have h3 : C * Real.exp (M * S) ≤ |C| * Real.exp (M * S) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hE.le
    have h4 : 0 ≤ |C| * Real.exp (M * S) := by positivity
    have h5 : k ≤ ⌈|C| * Real.exp (M * S)⌉₊ := Nat.ceil_mono h3
    have h6 : (k : ℝ) ≤ |C| * Real.exp (M * S) + 1 :=
      (Nat.cast_le.2 h5).trans (Nat.ceil_lt_add_one h4).le
    nlinarith
  have hsq : ‖f i g‖ ^ 2 ≤ |C₀| * (|C| + c) * Real.exp (M * S) := by
    calc ‖f i g‖ ^ 2 ≤ C₀ * k := h1
      _ ≤ |C₀| * k := mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg _)
      _ ≤ |C₀| * ((|C| + c) * Real.exp (M * S)) := mul_le_mul_of_nonneg_left hkle (abs_nonneg _)
      _ = _ := by ring
  rw [hsum]
  have e : Real.exp (M / 2 * S) ^ 2 = Real.exp (M * S) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hA : 0 ≤ |C₀| * (|C| + c) := by positivity
  refine abs_le_of_sq_le_sq' ?_ ?_ |>.2
  · rw [mul_pow, Real.sq_sqrt hA, e]; exact hsq
  · positivity

theorem enorm_sq_le (a b : ℂ) : ‖a‖ₑ ^ 2 ≤ 2 * ‖a - b‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  have h : ‖a‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    have h1 : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by simpa using norm_add_le (a - b) b
    have h2 := norm_nonneg a
    nlinarith [sq_nonneg (‖a - b‖ - ‖b‖)]
  have e : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [e, e, e]
  calc ENNReal.ofReal (‖a‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖a - b‖ ^ 2 + 2 * ‖b‖ ^ 2) := ENNReal.ofReal_le_ofReal h
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num)]
      simp

section Approx

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
  [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)] (ν : Measure (archGroup E N)) [ν.IsHaarMeasure]

theorem sm_integrable {β : archGroup E N → ℝ} (hβ : Ker ν β) {f : GA E N → ℂ} (hf : Continuous f) (x : GA E N) :
    Integrable (fun y => (β y : ℂ) * f (x * infEmb E N y)) ν := by
  refine Continuous.integrable_of_hasCompactSupport
    ((Complex.continuous_ofReal.comp hβ.cont).mul (hf.comp (continuous_const.mul continuous_infEmb))) ?_
  exact (hβ.cpt.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)).mul_right

theorem sm_sub {β : archGroup E N → ℝ} (hβ : Ker ν β) {f g : GA E N → ℂ} (hf : Continuous f) (hg : Continuous g)
    (x : GA E N) : sm ν β (fun x => f x - g x) x = sm ν β f x - sm ν β g x := by
  unfold sm
  rw [← integral_sub (sm_integrable ν hβ hf x) (sm_integrable ν hβ hg x)]
  simp only [mul_sub]

theorem iter_cont {β : archGroup E N → ℝ} (hβ : Ker ν β) {f : GA E N → ℂ} (hf : Continuous f) (j : ℕ) :
    Continuous ((sm ν β)^[j] f) := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact GlobalTheory.T.continuous_archimedean_smoothing E N ν β _ hβ ih

theorem iter_left {β : archGroup E N → ℝ} {f : GA E N → ℂ} (hf : ∀ γ ∈ latticeGL E N, ∀ g, f (γ * g) = f g) (j : ℕ) :
    ∀ γ ∈ latticeGL E N, ∀ g, (sm ν β)^[j] f (γ * g) = (sm ν β)^[j] f g := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
    intro γ hγ g
    rw [Function.iterate_succ_apply']
    simp only [sm, mul_assoc]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [ih γ hγ]

theorem approxU [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure]
    (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N)) (hα : Continuous α) (hαc : HasCompactSupport α) (hδ : 0 < δ)
    (hF : IsFundamentalDomain (latticeGL E N) F μ) (η : ℝ≥0∞) (hη : 0 < η) (k : ℕ) :
    ∃ β, Ker ν β ∧ ∀ ψ : GA E N → ℂ, Continuous ψ → (∀ γ ∈ latticeGL E N, ∀ g, ψ (γ * g) = ψ g) →
      (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) → (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 →
      ∫⁻ x in F, ‖ψ x - (sm ν β)^[k] ψ x‖ₑ ^ 2 ∂μ ≤ η := by
  have h4 : (4 : ℝ≥0∞) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have h4' : (4 : ℝ≥0∞) ^ k ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  set e : ℝ≥0∞ := η / 4 ^ k with he
  have he0 : 0 < e := ENNReal.div_pos hη.ne' h4'
  obtain ⟨U, hU, hUψ⟩ := GlobalTheory.T.kernel_eigenfunction_equicontinuous E N μ α δ F hα hαc hδ hF e he0
  have hU' : (infEmb E N) ⁻¹' U ∈ 𝓝 (1 : archGroup E N) := by
    refine continuous_infEmb.continuousAt.preimage_mem_nhds ?_
    rwa [map_one]
  obtain ⟨β, hβ, hsupp⟩ := exists_ker ν hU'
  refine ⟨β, hβ, fun ψ hc hl hs hn => ?_⟩
  have hnear : ∫⁻ x in F, ‖ψ x - sm ν β ψ x‖ₑ ^ 2 ∂μ ≤ e :=
    GlobalTheory.T.smoothing_fundamental_domain_bound E N μ ν F β e hF hβ ψ hc fun y hy => hUψ ψ hc hl hs hn _ (hsupp hy)
  have key : ∀ j : ℕ, ∫⁻ x in F, ‖ψ x - (sm ν β)^[j] ψ x‖ₑ ^ 2 ∂μ ≤ 4 ^ j * e := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hcj := iter_cont ν hβ hc j
      have hcj1 := iter_cont ν hβ hc (j + 1)
      have hh : Continuous fun x => ψ x - (sm ν β)^[j] ψ x := hc.sub hcj
      have hcontr := GlobalTheory.T.smoothing_fundamental_domain_integral E N μ ν F β hF hβ _ hh (fun γ hγ g => by
        simp only [hl γ hγ g, iter_left ν hl j γ hγ g])
      have hS1 : Continuous (sm ν β ψ) := GlobalTheory.T.continuous_archimedean_smoothing E N ν β ψ hβ hc
      have hpt : ∀ x, ‖ψ x - (sm ν β)^[j + 1] ψ x‖ₑ ^ 2 ≤
          2 * ‖ψ x - sm ν β ψ x‖ₑ ^ 2 + 2 * ‖sm ν β (fun x => ψ x - (sm ν β)^[j] ψ x) x‖ₑ ^ 2 := by
        intro x
        have h := enorm_sq_le (ψ x - (sm ν β)^[j + 1] ψ x) (sm ν β (fun x => ψ x - (sm ν β)^[j] ψ x) x)
        have e1 : ψ x - (sm ν β)^[j + 1] ψ x - sm ν β (fun x => ψ x - (sm ν β)^[j] ψ x) x = ψ x - sm ν β ψ x := by
          rw [sm_sub ν hβ hc hcj, Function.iterate_succ_apply']
          ring
        rwa [e1] at h
      have hm1 : Measurable fun x => 2 * ‖ψ x - sm ν β ψ x‖ₑ ^ 2 :=
        (((hc.sub hS1).enorm.measurable).pow_const 2).const_mul 2
      calc ∫⁻ x in F, ‖ψ x - (sm ν β)^[j + 1] ψ x‖ₑ ^ 2 ∂μ
          ≤ ∫⁻ x in F, (2 * ‖ψ x - sm ν β ψ x‖ₑ ^ 2 + 2 * ‖sm ν β (fun x => ψ x - (sm ν β)^[j] ψ x) x‖ₑ ^ 2) ∂μ :=
            lintegral_mono hpt
        _ = 2 * ∫⁻ x in F, ‖ψ x - sm ν β ψ x‖ₑ ^ 2 ∂μ +
              2 * ∫⁻ x in F, ‖sm ν β (fun x => ψ x - (sm ν β)^[j] ψ x) x‖ₑ ^ 2 ∂μ := by
            rw [lintegral_add_left hm1, lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
        _ ≤ 2 * e + 2 * (4 ^ j * e) := by gcongr; exact hcontr.trans ih
        _ ≤ 4 ^ (j + 1) * e := by
            have h1 : (1 : ℝ≥0∞) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
            calc 2 * e + 2 * (4 ^ j * e) ≤ 2 * (4 ^ j * e) + 2 * (4 ^ j * e) := by
                  gcongr
                  calc e = 1 * e := (one_mul e).symm
                    _ ≤ 4 ^ j * e := by gcongr
              _ = 4 ^ (j + 1) * e := by rw [pow_succ]; ring
  calc _ ≤ 4 ^ k * e := key k
    _ = η := by rw [he, ENNReal.mul_div_cancel h4 h4']

end Approx

section Half

variable {G : Type} [Group G] [TopologicalSpace G] [T2Space G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]

theorem half_of_cover {F Ω Sl : Set (G)} (hF : IsFundamentalDomain (Γ) F μ) (hΩ : IsCompact Ω)
    (hS : ∀ x, ∃ γ ∈ Γ, γ * x ∈ Sl) {ψ f : G → ℂ} (hψ : Continuous ψ) (hf : Continuous f)
    (lψ : ∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) (lf : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g)
    (h1 : (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1) (h2 : ∫⁻ x in F, ‖ψ x - f x‖ₑ ^ 2 ∂μ ≤ 1 / 8)
    (h3 : ∫⁻ x in Sl \ Ω, ‖f x‖ₑ ^ 2 ∂μ ≤ 1 / 8) : 1 ≤ 2 * ∫⁻ x in Ω, ‖ψ x‖ₑ ^ 2 ∂μ := by
  have : MeasurableConstSMul (Γ) (G) := ⟨fun γ => measurable_const_mul (γ : G)⟩
  have : SMulInvariantMeasure (Γ) (G) μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  set T : Set (G) := ⋃ γ : Γ, (fun g => (γ : G) * g) ⁻¹' Ω with hTdef
  have hT : MeasurableSet T := MeasurableSet.iUnion fun γ => (measurable_const_mul _) hΩ.measurableSet
  have hmem : ∀ x, x ∈ T ↔ ∃ γ : Γ, (γ : G) * x ∈ Ω := fun x => by
    simp [hTdef, Set.mem_iUnion]
  have hTinv : ∀ (γ : Γ) x, γ • x ∈ T ↔ x ∈ T := by
    intro γ x
    rw [hmem, hmem]
    constructor
    · rintro ⟨γ', h⟩
      refine ⟨γ' * γ, ?_⟩
      simpa [Subgroup.smul_def, mul_assoc] using h
    · rintro ⟨γ', h⟩
      refine ⟨γ' * γ⁻¹, ?_⟩
      simpa [Subgroup.smul_def, mul_assoc] using h
  have hΩT : Ω ⊆ T := fun x hx => (hmem x).2 ⟨1, by simpa using hx⟩
  have hmψ : Measurable fun x => ‖ψ x‖ₑ ^ 2 := (hψ.enorm.measurable).pow_const 2
  have hmf : Measurable fun x => ‖f x‖ₑ ^ 2 := (hf.enorm.measurable).pow_const 2
  set u : G → ℝ≥0∞ := T.indicator fun x => ‖ψ x‖ₑ ^ 2 with hu
  set w : G → ℝ≥0∞ := Tᶜ.indicator fun x => ‖ψ x‖ₑ ^ 2 with hw
  set v : G → ℝ≥0∞ := Tᶜ.indicator fun x => ‖f x‖ₑ ^ 2 with hv
  have invI : ∀ (A : Set (G)) (h : G → ℝ≥0∞), (∀ (γ : Γ) x, γ • x ∈ A ↔ x ∈ A) →
      (∀ (γ : Γ) x, h (γ • x) = h x) → ∀ (γ : Γ) x, A.indicator h (γ • x) = A.indicator h x := by
    intro A h hA hh γ x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hA γ x).2 hx), hh]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx ((hA γ x).1 h'))]
  have hinvψ : ∀ (γ : Γ) x, ‖ψ (γ • x)‖ₑ ^ 2 = ‖ψ x‖ₑ ^ 2 := fun γ x => by
    rw [Subgroup.smul_def, smul_eq_mul, lψ γ.1 γ.2 x]
  have hinvf : ∀ (γ : Γ) x, ‖f (γ • x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2 := fun γ x => by
    rw [Subgroup.smul_def, smul_eq_mul, lf γ.1 γ.2 x]
  have hTcinv : ∀ (γ : Γ) x, γ • x ∈ Tᶜ ↔ x ∈ Tᶜ := fun γ x => not_congr (hTinv γ x)

  have A : ∫⁻ x in F, u x ∂μ ≤ ∫⁻ x in Ω, ‖ψ x‖ₑ ^ 2 ∂μ := by
    have c1 : ∫⁻ x in F, u x ∂μ ≤ ∫⁻ x in Ω ∪ Tᶜ, u x ∂μ := by
      refine JSqIntGlue.setLIntegral_le_of_cover hF (fun x => ?_) u (invI _ _ hTinv hinvψ)
      by_cases hx : x ∈ T
      · obtain ⟨γ, hγ⟩ := (hmem x).1 hx
        exact ⟨γ, Or.inl hγ⟩
      · exact ⟨1, Or.inr (by simpa using hx)⟩
    have c2 : ∫⁻ x in Tᶜ, u x ∂μ = 0 := by
      rw [setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) hT.compl fun x hx => Set.indicator_of_notMem hx _]
      simp
    calc _ ≤ _ := c1
      _ ≤ ∫⁻ x in Ω, u x ∂μ + ∫⁻ x in Tᶜ, u x ∂μ := lintegral_union_le _ _ _
      _ = ∫⁻ x in Ω, u x ∂μ := by rw [c2, add_zero]
      _ ≤ _ := lintegral_mono (Set.indicator_le_self _ _)

  have B : ∫⁻ x in F, v x ∂μ ≤ 1 / 8 := by
    have c1 : ∫⁻ x in F, v x ∂μ ≤ ∫⁻ x in Sl, v x ∂μ := by
      refine JSqIntGlue.setLIntegral_le_of_cover hF (fun x => ?_) v (invI _ _ hTcinv hinvf)
      obtain ⟨γ, hγ, h⟩ := hS x
      exact ⟨⟨γ, hγ⟩, h⟩
    have c2 : ∫⁻ x in Ω, v x ∂μ = 0 := by
      rw [setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) hΩ.measurableSet
        fun x hx => Set.indicator_of_notMem (Set.notMem_compl_iff.2 (hΩT hx)) _]
      simp
    calc _ ≤ _ := c1
      _ ≤ ∫⁻ x in (Sl \ Ω) ∪ Ω, v x ∂μ := lintegral_mono_set fun x hx => by
          by_cases h : x ∈ Ω
          · exact Or.inr h
          · exact Or.inl ⟨hx, h⟩
      _ ≤ ∫⁻ x in Sl \ Ω, v x ∂μ + ∫⁻ x in Ω, v x ∂μ := lintegral_union_le _ _ _
      _ = ∫⁻ x in Sl \ Ω, v x ∂μ := by rw [c2, add_zero]
      _ ≤ ∫⁻ x in Sl \ Ω, ‖f x‖ₑ ^ 2 ∂μ := lintegral_mono (Set.indicator_le_self _ _)
      _ ≤ _ := h3
  have C : ∫⁻ x in F, w x ∂μ ≤ 1 / 2 := by
    have hpt : ∀ x, w x ≤ 2 * ‖ψ x - f x‖ₑ ^ 2 + 2 * v x := by
      intro x
      by_cases hx : x ∈ Tᶜ
      · simp only [hw, hv, Set.indicator_of_mem hx]
        exact enorm_sq_le _ _
      · simp only [hw, Set.indicator_of_notMem hx]
        exact zero_le
    have hm1 : Measurable fun x => 2 * ‖ψ x - f x‖ₑ ^ 2 := (((hψ.sub hf).enorm.measurable).pow_const 2).const_mul 2
    calc ∫⁻ x in F, w x ∂μ ≤ ∫⁻ x in F, (2 * ‖ψ x - f x‖ₑ ^ 2 + 2 * v x) ∂μ := lintegral_mono hpt
      _ = 2 * ∫⁻ x in F, ‖ψ x - f x‖ₑ ^ 2 ∂μ + 2 * ∫⁻ x in F, v x ∂μ := by
          rw [lintegral_add_left hm1, lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ 2 * (1 / 8) + 2 * (1 / 8) := by gcongr
      _ = 1 / 2 := by
          have e8 : (2 : ℝ≥0∞) * (1 / 8) = 1 / 4 := by
            rw [mul_one_div, ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
            norm_num
          rw [e8]
          have e4 : (1 / 4 : ℝ≥0∞) + 1 / 4 = 1 / 2 := by
            rw [ENNReal.div_add_div_same, ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
            norm_num
          exact e4
  have D : (1 : ℝ≥0∞) ≤ ∫⁻ x in Ω, ‖ψ x‖ₑ ^ 2 ∂μ + 1 / 2 := by
    have e : ∀ x, ‖ψ x‖ₑ ^ 2 = u x + w x := fun x => by
      by_cases hx : x ∈ T
      · simp [hu, hw, hx]
      · simp [hu, hw, hx]
    have hmu : Measurable u := hmψ.indicator hT
    calc (1 : ℝ≥0∞) = ∫⁻ x in F, (u x + w x) ∂μ := by rw [← h1]; exact lintegral_congr e
      _ = ∫⁻ x in F, u x ∂μ + ∫⁻ x in F, w x ∂μ := lintegral_add_left hmu _
      _ ≤ _ := add_le_add A C
  have h12 : (1 / 2 : ℝ≥0∞) + 1 / 2 ≤ ∫⁻ x in Ω, ‖ψ x‖ₑ ^ 2 ∂μ + 1 / 2 := by
    rwa [ENNReal.add_halves]
  have h5 : (1 / 2 : ℝ≥0∞) ≤ ∫⁻ x in Ω, ‖ψ x‖ₑ ^ 2 ∂μ :=
    (ENNReal.add_le_add_iff_right (by simp)).1 h12
  calc (1 : ℝ≥0∞) = 2 * (1 / 2) := by
        rw [mul_one_div, ENNReal.div_self (by norm_num) (by norm_num)]
    _ ≤ _ := by gcongr

end Half

open PositivityTheory.Rg.BcB.SpectralAccumulation in
open scoped Classical in

theorem conc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
  (R ε δ : ℝ) (α : GA E N → ℂ) (F : Set (GA E N)), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → 0 < ε →
  Continuous α → HasCompactSupport α → 0 < δ → IsFundamentalDomain (latticeGL E N) F μ →
  ∃ Ω : Set (GA E N), IsCompact Ω ∧ ∀ (V : Submodule ℂ (Sm E N)) (ψ : Sm E N), IsDiscrete V → ψ ∈ V → TypeB K W ψ →
    InfBdd R V → (∀ r, 0 < r → r < N → ∀ c ∈ ExpV r V, pE E N r c ≤ -ε * (r * ((N : ℝ) - r))) →
    (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ.1 (x * y) ∂μ = s * ψ.1 x) →
    (∫⁻ x in F, ‖ψ.1 x‖ₑ ^ 2 ∂μ) = 1 → 1 ≤ 2 * ∫⁻ x in Ω, ‖ψ.1 x‖ₑ ^ 2 ∂μ := by
  intro E _ _ _ N _ _ μ _ K W R ε δ α F hK hW hε hα hαc hδ hF
  letI : MeasurableSpace (archGroup E N) := borel _
  haveI : BorelSpace (archGroup E N) := ⟨rfl⟩
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  let ν : Measure (archGroup E N) := Measure.haar
  let P : Sm E N → Prop := fun ψ => ∃ V : Submodule ℂ (Sm E N), IsDiscrete V ∧ ψ ∈ V ∧ TypeB K W ψ ∧ InfBdd R V ∧
    (∀ r, 0 < r → r < N → ∀ c ∈ ExpV r V, pE E N r c ≤ -ε * (r * ((N : ℝ) - r))) ∧
    (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ.1 (x * y) ∂μ = s * ψ.1 x) ∧ (∫⁻ x in F, ‖ψ.1 x‖ₑ ^ 2 ∂μ) = 1
  let ι : Type := {ψ : Sm E N // P ψ}
  let f : ι → GA E N → ℂ := fun i => i.1.1
  have hAut : ∀ i : ι, IsAutForm i.1 := by
    rintro ⟨ψ, V, hV, hψ, -⟩
    exact hV.aut ψ hψ
  have hcen : ∀ (i : ι) t g, f i (splitCentre E N t * g) = f i g := by
    rintro ⟨ψ, V, hV, hψ, -⟩
    exact (hV.sqInt ψ hψ).1
  have hcont : ∀ i, Continuous (f i) := fun i => ContAut.continuous_of_isOpen_stab E N _ (hAut i).level
  have hLI : ∀ i, IsLeftInvariant (f i) := fun i => GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E N _ (hAut i)
  have hleft : ∀ (i : ι), ∀ γ ∈ latticeGL E N, ∀ g, f i (γ * g) = f i g := by
    intro i
    let S : Subgroup (GA E N) :=
      { carrier := {γ | ∀ g, f i (γ * g) = f i g}
        one_mem' := fun g => by rw [one_mul]
        mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
        inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }
    have : latticeGL E N ≤ S :=
      sup_le (by rintro _ ⟨γ, rfl⟩; exact (hAut i).left γ) (Subgroup.zpowers_le.2 (hcen i 1))
    exact this
  obtain ⟨U, hU, hUk⟩ := GlobalTheory.T.exists_open_integral_subgroup E N K hK
  have hfam : UFam f := by
    refine ⟨hcont, hLI, U, hU, fun i g u => ?_⟩
    obtain ⟨k, hk, e⟩ := hUk u
    rw [e]
    obtain ⟨ψ, V, hV, hψ, hT, -⟩ := i
    exact hT.1 k hk g
  have hrep : ∀ i : ι, ∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * f i (x * y) ∂μ = s * f i x := by
    rintro ⟨ψ, V, hV, hψ, hT, hI, hE, hs, hn⟩
    exact hs
  have hnorm : ∀ i : ι, (∫⁻ x in F, ‖f i x‖ₑ ^ 2 ∂μ) = 1 := by
    rintro ⟨ψ, V, hV, hψ, hT, hI, hE, hs, hn⟩
    exact hn
  obtain ⟨M, hM⟩ := initU E N μ α δ F hα hαc hδ hF
  have hM' := hM ι f hcont hleft hrep hnorm

  have hD : ∀ r, ∃ D : ℕ, 0 < r → r < N → ∀ V : Submodule ℂ (Sm E N), IsDiscrete V →
      (∀ τ : E →+* ℂ, ∃ m, HasInfCharGL V τ m) → ∀ φ ∈ V, ∃ p : ℂ[X], p.Monic ∧ p.natDegree ≤ D ∧ An.Kill r φ.1 p ∧
        ∀ z, p.IsRoot z → ∃ c ∈ Exp r φ.1, z = Complex.exp c := by
    intro r
    by_cases hr : 0 < r ∧ r < N
    · obtain ⟨D, h⟩ := GlobalTheory.T.exists_exponent_polynomial_discrete E N r hr.1 hr.2
      exact ⟨D, fun _ _ => h⟩
    · exact ⟨0, fun h0 h1 => (hr ⟨h0, h1⟩).elim⟩
  choose Dr hDr using hD
  set D : ℕ := (Finset.range N).sup Dr with hDdef
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have hrho : ∀ r, 0 < r → r < N → 0 < An.rho E N r := by
    intro r h0 h1
    unfold An.rho
    have a1 : (0 : ℝ) < r := by exact_mod_cast h0
    have a2 : (0 : ℝ) < (N : ℝ) - r := sub_pos.2 (by exact_mod_cast h1)
    positivity
  set κ' : ℕ → ℝ := fun r => An.rho E N r * (1 - 2 * ε) with hκ'
  set κ : ℕ → ℝ := fun r => An.rho E N r * (1 - ε) with hκ
  have hp : ∀ r (i : ι), ∃ p : ℂ[X], 0 < r → r < N → p.Monic ∧ p.natDegree ≤ D ∧ An.Kill r (f i) p ∧
      ∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp (κ' r) := by
    rintro r ⟨ψ, V, hV, hψ, hT, hI, hE, hs, hn⟩
    by_cases hr : 0 < r ∧ r < N
    swap
    · exact ⟨1, fun h0 h1 => (hr ⟨h0, h1⟩).elim⟩
    obtain ⟨h0, h1⟩ := hr
    obtain ⟨p, hpm, hpd, hpk, hpz⟩ := hDr r h0 h1 V hV (fun τ => (hI τ).imp fun m h => h.1) ψ hψ
    refine ⟨p, fun _ _ => ⟨hpm, hpd.trans (Finset.le_sup (Finset.mem_range.2 (by omega))), hpk, fun z hz => ?_⟩⟩
    obtain ⟨c, hc, rfl⟩ := hpz z hz
    have h2 := hE r h0 h1 c ⟨ψ, hψ, hc⟩
    unfold pE at h2
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    have h3 : c.re / (Module.finrank ℚ E : ℝ) ≤ (r : ℝ) * ((N : ℝ) - r) / 2 - ε * (r * ((N : ℝ) - r)) := by linarith
    have h4 := (div_le_iff₀ hd).1 h3
    simp only [hκ', An.rho]
    calc c.re ≤ _ := h4
      _ = _ := by ring
  choose p hpp using hp
  obtain ⟨k, hk⟩ := iterU ν (κ' := κ') (κ := κ) (D := D) (p := p) hfam hM' (fun r h0 h1 =>
    ⟨by
      have := hrho r h0 h1
      simp only [hκ', hκ]
      nlinarith, fun i => hpp r i h0 h1⟩)
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := GroundTheory.Automorphic.Reduction.exists_siegelSet (K := E) N
  obtain ⟨-, hS, hL, -⟩ := dict_holds E N
  have h8 : (0 : ℝ≥0∞) < 1 / 8 := by simp
  obtain ⟨β, hβ, hβψ⟩ := approxU ν μ α δ F hα hαc hδ hF (1 / 8) h8 k
  obtain ⟨Ω, hΩ, hΩf⟩ := GlobalTheory.T.uniform_bound_siegel_set E N μ ι (fun i => (sm ν β)^[k] (f i)) κ (iter_fam ν hβ hfam k).cont (hk β hβ)
    (fun r h0 h1 => by
      have := hrho r h0 h1
      simp only [hκ]
      nlinarith) ω hω hωB (max 0 (-Real.log t)) (1 / 8) h8
  refine ⟨Ω, hΩ, fun V ψ hV hψ hT hI hE hs hn => ?_⟩
  let i : ι := ⟨ψ, V, hV, hψ, hT, hI, hE, hs, hn⟩
  exact half_of_cover (latticeGL E N) μ hF hΩ (fun g => JSqIntGlue.exists_mem_slab hS hL ht hsieg g)
    (hcont i) ((iter_fam ν hβ hfam k).cont i) (hleft i) (iter_left ν (hleft i) k) hn
    (hβψ _ (hcont i) (hleft i) (hrep i) hn) (hΩf i)

end GlobalTheory.CompanionTheory.Conc

end
end
