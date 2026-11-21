import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.ContinuousOnOrbit
import CompanionTheory.AutomorphicTheory.RankOneEstimates.DecSender
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.ThmMOfXi
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.FrameBlockWMem
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.DiscreteSeriesUnitarySmoothBasicImports
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesLinear
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesAdjoint
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DerivedSeriesDerivation
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordLengthBoundOfLinear
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsFactor
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ReductionOfDerivedSeries
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ChartExistence
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuotientBoundOfFactorReduceChart
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TruncatedDerivation
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TruncatedDerivationLimit
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AdaptExists
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwasawaDecomposition
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviDecomposition
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecomposition
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfIwasawaLeviCartanStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorBound
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SpanGenerators
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExponentialMembership
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.RootVectors
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugacy

section
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate

noncomputable section

namespace CompanionTheory.Bmu

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spanFam {n : ℕ} (S : Submodule ℝ (Mat n)) : ∃ (d : ℕ) (X : Fin d → Mat n), (∀ j, X j ∈ S) ∧
    ∀ Y ∈ S, ∃ a : Fin d → ℝ, Y = ∑ j, (a j : ℂ) • X j := by
  let b := Module.finBasis ℝ S
  refine ⟨_, fun j => (b j : Mat n), fun j => (b j).2, fun Y hY => ⟨fun j => b.repr ⟨Y, hY⟩ j, ?_⟩⟩
  have h := congrArg (Subtype.val) (b.sum_repr ⟨Y, hY⟩)
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
  simp only [Complex.coe_smul]
  exact h.symm

theorem lie_add {n : ℕ} {Hm X Y : Mat n} (hX : Lie Hm X) (hY : Lie Hm Y) : Lie Hm (X + Y) := by
  unfold Lie at *
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
  calc Xᴴ * Hm + Yᴴ * Hm + (Hm * X + Hm * Y) = (Xᴴ * Hm + Hm * X) + (Yᴴ * Hm + Hm * Y) := by abel
    _ = 0 := by rw [hX, hY, add_zero]

theorem lie_smul {n : ℕ} {Hm X : Mat n} (c : ℝ) (hX : Lie Hm X) : Lie Hm (c • X) := by
  unfold Lie at *
  rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem lie_zero {n : ℕ} (Hm : Mat n) : Lie Hm 0 := by simp [Lie]

variable {k r : ℕ}

def sUw (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Submodule ℝ (Mat (2 * r + k + 1)) where
  carrier := {X | InUw k r z X}
  zero_mem' := ⟨lie_zero _, fun _ => ⟨zero_mulVec _, zero_mulVec _⟩, zero_mulVec _⟩
  add_mem' := fun {X Y} hX hY => ⟨lie_add hX.1 hY.1, fun a =>
    ⟨by rw [add_mulVec, (hX.2.1 a).1, (hY.2.1 a).1, add_zero], by rw [add_mulVec, (hX.2.1 a).2, (hY.2.1 a).2, add_zero]⟩,
    by rw [add_mulVec, hX.2.2, hY.2.2, add_zero]⟩
  smul_mem' := fun c X hX => ⟨lie_smul c hX.1, fun a =>
    ⟨by rw [smul_mulVec, (hX.2.1 a).1, smul_zero], by rw [smul_mulVec, (hX.2.1 a).2, smul_zero]⟩,
    by rw [smul_mulVec, hX.2.2, smul_zero]⟩

def sN (k r : ℕ) : Submodule ℝ (Mat (2 * r + k + 1)) where
  carrier := {X | InN k r X}
  zero_mem' := ⟨lie_zero _, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  add_mem' := fun {X Y} hX hY => ⟨lie_add hX.1 hY.1, fun a i h => by
    rw [Matrix.add_apply, hX.2.1 a i h, hY.2.1 a i h, add_zero], fun i j h1 h2 h3 => by
    rw [Matrix.add_apply, hX.2.2 i j h1 h2 h3, hY.2.2 i j h1 h2 h3, add_zero]⟩
  smul_mem' := fun c X hX => ⟨lie_smul c hX.1, fun a i h => by
    rw [Matrix.smul_apply, hX.2.1 a i h, smul_zero], fun i j h1 h2 h3 => by
    rw [Matrix.smul_apply, hX.2.2 i j h1 h2 h3, smul_zero]⟩

def sQ (k r : ℕ) (Γ : Mat (2 * r + k + 1)) : Submodule ℝ (Mat (2 * r + k + 1)) where
  carrier := {X | InQ k r Γ X}
  zero_mem' := ⟨lie_zero _, fun _ _ _ => by simp⟩
  add_mem' := fun {X Y} hX hY => ⟨lie_add hX.1 hY.1, fun i j h => by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, hX.2 i j h, hY.2 i j h, add_zero]⟩
  smul_mem' := fun c X hX => ⟨lie_smul c hX.1, fun i j h => by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, hX.2 i j h, smul_zero]⟩

theorem psiGen_one {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin r → ℂ) :
    PI.BesselMapUniq.psiGen k r z c 1 = 1 := by
  have h : ∀ a, PI.BesselMapUniq.ellA k r z 1 a = 0 := by
    intro a
    unfold PI.BesselMapUniq.ellA
    split_ifs with h
    · refine Matrix.one_apply_ne fun e => ?_
      have := congrArg Fin.val e
      simp [eI] at this
    · rw [one_mulVec]
      exact hz _ (Or.inl a.2)
  simp [PI.BesselMapUniq.psiGen, h]

theorem psiGen_cont (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (PI.BesselMapUniq.psiGen k r z c) := by
  have h : ∀ a, Continuous fun g => PI.BesselMapUniq.ellA k r z g a := by
    intro a
    unfold PI.BesselMapUniq.ellA
    split_ifs with h
    · exact continuous_id.matrix_elem _ _
    · exact (continuous_apply (eI k r a)).comp
        ((continuous_id (X := Mat (2 * r + k + 1))).matrix_mulVec (continuous_const (y := z)))
  unfold PI.BesselMapUniq.psiGen
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finset_sum _ fun a _ => continuous_const.mul (h a)))))

theorem norm_psiGen (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (g : Mat (2 * r + k + 1)) :
    ‖PI.BesselMapUniq.psiGen k r z c g‖ = 1 := by
  unfold PI.BesselMapUniq.psiGen
  exact Complex.norm_exp_I_mul_ofReal _

theorem one_uw (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mat (2 * r + k + 1)) ∈ UWset k r z :=
  ⟨by simp [UH], fun _ => ⟨one_mulVec _, one_mulVec _⟩, one_mulVec _⟩

theorem bounded_of (hQB : QBound) (hAB : AbsBound) (hAd : AdaptExists) (hDec : Decomp) (hTB : TorBound)
    (hSp : SpanG) (hEx : ExpMem) (hRV : RootVec) : Bounded := by
  intro k r H _ _ _ σ hU hk z c hz hT hc V _ _ _ π hπ1 hπi hπc B hB heq w hw
  obtain ⟨Γ, hΓ⟩ := (hAd k r hk).2 z hz hT
  obtain ⟨d₁, X₁, hX₁, sp₁⟩ := spanFam (sUw k r z)
  obtain ⟨d₂, X₂, hX₂, sp₂⟩ := spanFam (sN k r)
  obtain ⟨e, Q, hQ, sp₃⟩ := spanFam (sQ k r Γ)
  have hX : ∀ j, InUw k r z (Fin.append X₁ X₂ j) ∨ InN k r (Fin.append X₁ X₂ j) := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]; exact Or.inl (hX₁ i)
    · rw [Fin.append_right]; exact Or.inr (hX₂ i)
  have hspan : Spans (Hpk k r) (Fin.append X₁ X₂) Q := by
    intro Y hY
    obtain ⟨Y₁, Y₂, Y₃, h1, h2, h3, rfl⟩ := hSp k r z Γ hk hΓ Y hY
    obtain ⟨a₁, e₁⟩ := sp₁ Y₁ h1
    obtain ⟨a₂, e₂⟩ := sp₂ Y₂ h2
    obtain ⟨b, e₃⟩ := sp₃ Y₃ h3
    refine ⟨Fin.append a₁ a₂, b, ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [← e₁, ← e₂, ← e₃]
  have hχ : ∀ j, ∃ χ : ℝ → (V →L[ℂ] V), Continuous χ ∧ χ 0 = 1 ∧
      ∀ t v, IsSm (UH (Hpk k r)) σ v → B (σ (ex (Fin.append X₁ X₂ j) t) v) = χ t (B v) := by
    intro j
    rcases hX j with h | h
    · have hm := fun t => (hEx k r z _ t).1 h
      refine ⟨fun t => π (ex (Fin.append X₁ X₂ j) t), hπc.comp_continuous (continuous_ex _) hm, ?_, fun t v hv => ?_⟩
      · simp only [ex_zero, hπ1]
      · have := heq _ (hm t) 1 WeylGroupFacts.mem_n_one v hv
        rwa [Matrix.mul_one, psiGen_one hz, one_smul] at this
    · have hm := fun t => (hEx k r z _ t).2 h
      refine ⟨fun t => PI.BesselMapUniq.psiGen k r z c (ex (Fin.append X₁ X₂ j) t) • (1 : V →L[ℂ] V),
        ((psiGen_cont z c).comp (continuous_ex _)).smul continuous_const, ?_, fun t v hv => ?_⟩
      · simp only [ex_zero, psiGen_one hz, one_smul]
      · have := heq 1 (one_uw z) _ (hm t) v hv
        rw [Matrix.one_mul, hπ1] at this
        exact this
  choose χ hχc hχ0 hχe using hχ
  have hXL : ∀ j, Lie (Hpk k r) (Fin.append X₁ X₂ j) := fun j => (hX j).elim (fun h => h.1) fun h => h.1
  have hQL : ∀ i, Lie (Hpk k r) (Q i) := fun i => (hQ i).1
  obtain ⟨C, m, hC, hQ'⟩ := hQB _ _ H σ hU V B hB _ e _ Q hXL hQL hspan χ hχc hχ0 hχe
  obtain ⟨C₁, hC₁⟩ := hRV k r z Γ c hk hΓ hc
  set C₂ : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * ∑ i, ‖Γ⁻¹ * Q i * Γ‖ with hC₂
  obtain ⟨K, hK⟩ := hAB _ _ H σ hU V B hB e Q hQL C m hC hQ' (max C₁ C₂) (2 * r + k + 1) w hw
  refine ⟨K, fun g hg => ?_⟩
  obtain ⟨h, hh, m', hm', d, R, hd, hR, hg', rfl⟩ := hDec k r z Γ hk hz hΓ g hg
  set g' := Γ * dg d * R with hg'def
  have hsm : IsSm (UH (Hpk k r)) σ (σ g' w) := hw.apply hU.rep hg'
  rw [hU.rep.apply_mul (hU.rep.mul_mem _ hh.1 _ hm'.1) hg', heq h hh m' hm' _ hsm, norm_smul, norm_psiGen, one_mul,
    hπi h hh]
  have hconj : ∀ M : ℝ, 1 ≤ M → (∀ a : Fin r, d (eI k r a) ≤ M * d (nxt k r a)) →
      ∀ i, ‖g'⁻¹ * Q i * g'‖ ≤ max C₁ C₂ * M ^ (2 * r + k + 1) := by
    intro M hM hr i
    have e1 : g'⁻¹ * Q i * g' = (dg d * R)⁻¹ * (Γ⁻¹ * Q i * Γ) * (dg d * R) := by
      rw [hg'def, Matrix.mul_assoc Γ, Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
    rw [e1]
    refine (hTB k r d R _ M hk hd hR hM hr (hQ i).2).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    refine le_trans ?_ (le_max_right _ _)
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun i => ‖Γ⁻¹ * Q i * Γ‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
      (by positivity)
  by_cases hall : ∀ a : Fin r, d (eI k r a) / d (nxt k r a) ≤ 1
  · refine hK g' hg' 1 le_rfl (hconj 1 le_rfl fun a => ?_) (Or.inl rfl)
    exact (div_le_iff₀ (hd.1 _)).1 (hall a)
  · push Not at hall
    obtain ⟨a₁, ha₁⟩ := hall
    obtain ⟨a₀, -, ha₀⟩ := Finset.exists_max_image Finset.univ (fun a : Fin r => d (eI k r a) / d (nxt k r a))
      ⟨a₁, Finset.mem_univ _⟩
    have hM : 1 ≤ d (eI k r a₀) / d (nxt k r a₀) := ha₁.le.trans (ha₀ a₁ (Finset.mem_univ _))
    obtain ⟨Y, hY, hYn, hYe⟩ := hC₁ a₀ d R hd hR hg'
    refine hK g' hg' _ hM (hconj _ hM fun a => (div_le_iff₀ (hd.1 _)).1 (ha₀ a (Finset.mem_univ _)))
      (Or.inr ⟨Y, d (eI k r a₀) / d (nxt k r a₀), hY, hYn.trans (le_max_left _ _), le_abs_self _, fun τ u hu => ?_⟩)
    obtain ⟨hN, hψ⟩ := hYe τ
    have hinv : g'⁻¹ * g' = 1 := mul_eq_one_comm.1 (hU.grp.2.2.2 g' hg').2
    have e2 : g' * ex Y τ = 1 * (g' * ex Y τ * g'⁻¹) * g' := by
      rw [Matrix.one_mul, Matrix.mul_assoc (g' * ex Y τ), hinv, Matrix.mul_one]
    rw [e2, hU.rep.apply_mul (hU.rep.mul_mem _ hU.rep.one_mem _ hN.1) hg',
      heq 1 (one_uw z) _ hN _ (hu.apply hU.rep hg'), hπ1, hψ]
    rfl

end CompanionTheory.Bmu
end
end

section
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.QuantumDeterminants ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1 CompanionTheory.D.Upq.Sm
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace CompanionTheory.Bmu

theorem orbit_mult (hCL : CutLim) (hAd : DsAd) (hF : Factor) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (D : B.RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D)
    (hS : SqIntG D X) (ha : aM k r ≤ X.a) (hU : URep (Hpk k r) X.σ) (hw : IsSm (UH (Hpk k r)) X.σ X.w)
    (hdec : ∀ v, IsSm (UH (Hpk k r)) X.σ v → ∃ C : ℝ, ∀ x ∈ B.GV k r, ‖⟪v, X.σ x X.w⟫_ℂ‖ ≤ C * B.gN x ^ (-X.a))
    {l : X.Hs → Wp} (hl : IsMultOneMap D X l) {Bm : X.Hs → Wp} (hB : CWLin (Hpk k r) X.σ Bm)
    (heq : ∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r, ∀ v, IsSm (UH (Hpk k r)) X.σ v →
      Bm (X.σ (h * m) v) = psi k r D.z cStd m • D.π h (Bm v))
    (hbd : ∃ K : ℝ, ∀ g ∈ UH (Hpk k r), ‖Bm (X.σ g X.w)‖ ≤ K) :
    ∃ c : ℂ, ∀ x ∈ UH (Hpk k r), Bm (X.σ x X.w) = c • l (X.σ x X.w) := by
  obtain ⟨d, hd⟩ := stSchurG k r Wp D X hD hS
  obtain ⟨K, hK⟩ := hbd
  have hae := BeEquiv.ae_mem_of_haarOn D.haarG
  have hAB : B.AB k r ≤ X.a := by
    refine (le_trans ?_ ha)
    have h1 : (1 : ℝ) ≤ r + 1 := by have := Nat.cast_nonneg (α := ℝ) r; linarith
    have h2 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h3 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hn : (1 : ℝ) ≤ nR k r := by unfold nR; exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
    have h4 : B.AB k r ≤ nR k r ^ 2 + 1 := by
      unfold B.AB nR
      push_cast
      nlinarith [sq_nonneg ((k : ℝ) + r - (r + 1))]
    have h5 : nR k r ^ 2 ≤ nR k r ^ 3 := pow_le_pow_right₀ hn (by norm_num)
    have h6 := one_le_pow₀ (n := 3) hn
    unfold aM
    linarith
  have hGN := TopH.gN_integrable D (SquareIntegrabilityOnOrbit.gnInt_of multiplicity_one_hypotheses_hold) hAB
  have hcont := hB.continuousOn_orbit hF hU hw
  have hWm := SquareIntegrabilityOnOrbit.aesm_of_contOn multiplicity_one_hypotheses_hold D (f := fun g => Bm (X.σ g X.w)) hcont
  obtain ⟨c, hc⟩ := stMFix multiplicity_one_hypotheses_hold k r Wp D X hD hS ha l hl d hd (fun g => Bm (X.σ g X.w)) hWm
    (fun h hh m hm x hx => by
      have hi := WeylGroupFacts.uw_inv hh
      obtain ⟨hn, he⟩ := unitary_weyl_normal_holds k r D.z D.z_mem h⁻¹ hi m hm
      have hu := WeylGroupFacts.isUnit_of_uh hh.1
      rw [Matrix.nonsing_inv_nonsing_inv _ hu] at hn he
      have e : m * h * x = h * (h⁻¹ * m * h) * x := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
      show Bm (X.σ (m * h * x) X.w) = psi k r D.z cStd m • D.π h (Bm (X.σ x X.w))
      rw [e, hU.rep.apply_mul (hU.rep.mul_mem _ hh.1 _ hn.1) hx, heq h hh _ hn _ (hw.apply hU.rep hx)]
      unfold psi
      rw [he])
    (fun x hx => by
      have hxi : x⁻¹ ∈ B.GV k r := (hU.grp.2.2.2 x hx).1
      have hmp : MeasurePreserving (lmulM x⁻¹) D.μG D.μG :=
        ⟨BeEquiv.measurable_lmul_mt x⁻¹, D.haarG.left x⁻¹ hxi⟩
      have h1 : Integrable (fun y : Mt k r => B.gN (x⁻¹ * Matrix.of y) ^ (-X.a)) D.μG :=
        hmp.integrable_comp_of_integrable hGN
      refine (h1.mul_const K).mono' (h1.aestronglyMeasurable.mul hWm.norm) ?_
      filter_upwards [hae] with y hy
      have h0 : 0 ≤ B.gN (x⁻¹ * Matrix.of y) ^ (-X.a) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [Real.norm_of_nonneg (mul_nonneg h0 (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hK _ hy) h0)
  have hμ : PI.IsHaarOnM (UH (Hpk k r)) D.μG :=
    ⟨BeEquiv.sigmaFinite_of_haarOn D.haarG, D.haarG.ne_zero, D.haarG.conc, D.haarG.left⟩
  have hσc : ContinuousOn (fun g => X.σ g X.w) (B.GV k r) := X.rep.2.2 X.w
  have hint : ∀ v, IsSm (UH (Hpk k r)) X.σ v →
      Integrable (fun y : Mt k r => ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ) D.μG := by
    intro v hv
    obtain ⟨C, hC⟩ := hdec v hv
    refine (hGN.const_mul C).mono' (SquareIntegrabilityOnOrbit.aesm_of_contOn multiplicity_one_hypotheses_hold D (f := fun g => ⟪v, X.σ g X.w⟫_ℂ)
      ((innerSL ℂ v).continuous.comp_continuousOn hσc)) ?_
    filter_upwards [hae] with y hy
    exact hC _ hy
  have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.1.ne'
  have hrep : ∀ v, IsSm (UH (Hpk k r)) X.σ v →
      ∫ y : Mt k r, conj ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • X.σ (Matrix.of y) X.w ∂D.μG = (d : ℂ)⁻¹ • v := by
    intro v hv
    have hi : Integrable (fun y : Mt k r => conj ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • X.σ (Matrix.of y) X.w) D.μG := by
      refine (hint v hv).norm.mono' (SquareIntegrabilityOnOrbit.aesm_of_contOn multiplicity_one_hypotheses_hold D
        (f := fun g => conj ⟪v, X.σ g X.w⟫_ℂ • X.σ g X.w)
        ((Complex.continuous_conj.comp_continuousOn ((innerSL ℂ v).continuous.comp_continuousOn hσc)).smul hσc)) ?_
      filter_upwards [hae] with y hy
      rw [norm_smul, hU.iso _ hy, X.w_norm, mul_one, Complex.norm_conj]
    refine ext_inner_left ℂ fun ξ => ?_
    rw [← integral_inner hi, inner_smul_right]
    have h := (hd.2 X.w ξ X.w v).2
    rw [inner_self_eq_norm_sq_to_K, X.w_norm] at h
    simp only [inner_smul_right]
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)) (h.trans ?_)
    · simp only [mc, Complex.star_def]
      ring
    · simp [div_eq_inv_mul]
  refine ⟨c, fun x hx => ?_⟩
  have hBx := hB.comp_sigma hAd hU hx
  have hlim := hCL _ _ X.Hs X.σ hU Wp _ hBx D.μG hμ X.w hw hint _ hrep
    ⟨K, fun g hg => by rw [← hU.rep.apply_mul hx hg]; exact hK _ (hU.rep.mul_mem _ hx _ hg)⟩ X.w hw
  rw [← hc x hx]
  have e1 : Bm (X.σ x X.w) = (d : ℂ) • ((d : ℂ)⁻¹ • Bm (X.σ x X.w)) := by
    rw [smul_smul, mul_inv_cancel₀ hd0, one_smul]
  rw [e1, hlim, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [hae] with y hy
  rw [hU.rep.apply_mul hx hy, smul_smul]
  rfl

theorem cwLin_of {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat (2 * r + k + 1) → (H →L[ℂ] H)} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mat (2 * r + k + 1) → ℂ} {π : Mat (2 * r + k + 1) → (Wp →L[ℂ] Wp)}
    {Bm : H → Wp} (h : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π Bm) : CWLin (Hpk k r) σ Bm := by
  obtain ⟨h1, h2, -, C, Ws, hW, hb⟩ := h
  refine ⟨fun x hx y hy => h1 x hx y hy, fun a x hx => h2 a x hx, C, Ws, hW, fun v hv => ?_⟩
  have := hb v hv
  simpa only [dsigW_eq'] using this

theorem uniq_of (hBd : Bounded) (hCL : CutLim) (hTC : TorConj) (hAd : DsAd) (hF : Factor) : BesselMapUniqGap := by
  intro k r ε lam h H _ _ σ z c u Wp _ _ π hk hg hh hl hσ hz hT hc hπ B₁ B₂ hB₁ hB₂
  haveI : CompleteSpace H := by obtain ⟨P, -, h1, -⟩ := hσ; exact h1
  haveI : FiniteDimensional ℂ Wp := by obtain ⟨g, -, -, h1, -⟩ := hπ; exact h1
  obtain ⟨hrep, hiso, hcont, hirr⟩ := TopTA.pi_facts (u := u) (π := π) hz hT hπ
  obtain ⟨D, hDz, hDπ, hD⟩ := stDiagExists multiplicity_one_hypotheses_hold k r Wp z π hk hz hT hrep hiso hcont hirr
  subst hDz hDπ
  obtain ⟨hUR, hsq⟩ := TopTA.sqInt_of_DSHpk (σ := σ) hσ D.haarG
  have hG : PI.IsMatGroup (UH (Hpk k r)) := PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r
  have hU : URep (Hpk k r) σ :=
    ⟨(hermitian_pos_facts_hold k r).2.1, hG, ⟨hG.2.1, hG.2.2.1, hUR.1.1, hUR.1.2⟩, hUR.2.1⟩
  have hm : thrStar ε + ((4 * (2 * r + k + 1) ^ 3 : ℕ) : ℝ) < h := by
    have := CompanionTheory.FamilyDerivativeExpansion.DecS.thr_le (n := 2 * r + k + 1) (by omega) ε
    have h1 : (0 : ℝ) < ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by positivity
    rw [Nat.cast_mul, Nat.cast_pow]
    push_cast at *
    linarith
  have dec : ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      ∃ C : ℝ, ∀ x ∈ B.GV k r, ‖⟪v, σ x w⟫_ℂ‖ ≤ C * B.gN x ^ (-aM k r) := by
    intro w hw v hv
    obtain ⟨C, Ws, -, h2⟩ := CompanionTheory.FamilyDerivativeExpansion.DecS.decayM hl hσ hg _ hm v hv
    exact ⟨_, fun x hx => h2 (aM k r) (by unfold aM nR; push_cast; rfl) w hw x hx⟩
  obtain ⟨-, -, -, -, hsm, -, hKT, ⟨w0, hw0, hw0K, -⟩, -⟩ :=
    GlobalTheory.T.discreteSeries_unitary_smooth_basic CompanionTheory.D.gk.admitted.k_finite_smooth k r ε lam ⟨H, σ⟩ ⟨hl, hσ⟩
  have hw0s := hsm w0 (hKT w0 hw0K)
  obtain ⟨C0, hC0⟩ := dec w0 hw0s w0 hw0s
  let X : SigData k r := ⟨H, σ, hUR, TopTA.irr_of_DSHpk (σ := σ) hσ, w0, hw0, aM k r, C0, hC0⟩
  have hS : SqIntG D X := hsq
  obtain ⟨l, hl1⟩ := thmM k r Wp D X hD hS le_rfl
  obtain ⟨τ, hτ, hτW, hτN⟩ := hTC k r D.z c hz hc
  have hw : IsSm (UH (Hpk k r)) σ w0 := hw0s
  have hτi : τ⁻¹ * τ = 1 := mul_eq_one_comm.1 (hG.2.2.2 τ hτ).2
  have key : ∀ Bm : H → Wp,
      PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) D.z (PI.BesselMapUniq.psiGen k r D.z c) σ D.π Bm →
      ∃ c₀ : ℂ, ∀ x ∈ UH (Hpk k r), Bm (σ τ (σ x w0)) = c₀ • l (σ x w0) := by
    intro Bm hBm
    have hCW := cwLin_of hBm
    obtain ⟨K, hK⟩ := hBd k r H σ hU hk D.z c hz hT hc Wp D.π hrep.1 hiso hcont Bm hCW
      (fun h hh m hm v hv => hBm.2.2.1 h hh m hm v hv) w0 hw
    refine orbit_mult hCL hAd hF D X hD hS le_rfl hU hw (fun v hv => dec w0 hw0s v hv) hl1
      (Bm := fun v => Bm (σ τ v)) (hCW.comp_sigma hAd hU hτ) (fun h hh m hm v hv => ?_) ⟨K, fun g hg => ?_⟩
    · obtain ⟨hn, hψ⟩ := hτN m hm
      have e : τ * (h * m) = h * (τ * m * τ⁻¹) * τ := by
        rw [← Matrix.mul_assoc, hτW h hh]
        simp only [Matrix.mul_assoc, hτi, Matrix.mul_one]
      show Bm (σ τ (σ (h * m) v)) = psi k r D.z cStd m • D.π h (Bm (σ τ v))
      rw [← hU.rep.apply_mul hτ (hU.rep.mul_mem _ hh.1 _ hm.1), e,
        hU.rep.apply_mul (hU.rep.mul_mem _ hh.1 _ hn.1) hτ, hBm.2.2.1 h hh _ hn _ (hv.apply hU.rep hτ), hψ]
    · show ‖Bm (σ τ (σ g w0))‖ ≤ K
      rw [← hU.rep.apply_mul hτ hg]
      exact hK _ (hU.rep.mul_mem _ hτ _ hg)
  obtain ⟨c₁, e₁⟩ := key B₁ hB₁
  obtain ⟨c₂, e₂⟩ := key B₂ hB₂
  have fin : ∀ a b : ℂ, a * c₁ + b * c₂ = 0 →
      ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, a • B₁ v + b • B₂ v = 0 := by
    intro a b hab v hv
    have hE := (((cwLin_of hB₁).comb (cwLin_of hB₂) a b).comp_sigma hAd hU hτ)
    have hτ' := (hG.2.2.2 τ hτ).1
    have hv' : IsSm (UH (Hpk k r)) σ (σ τ⁻¹ v) := IsSm.apply hU.rep hv hτ'
    have h0 := hE.eq_zero hU hw (fun g hg => by
        show a • B₁ (σ τ (σ g w0)) + b • B₂ (σ τ (σ g w0)) = 0
        rw [e₁ g hg, e₂ g hg, smul_smul, smul_smul, ← add_smul, hab, zero_smul]) hv'
      (fun Ws hWs δ hδ => by
        have := cyc_of_smooth k r ε lam H σ w0 hσ (by intro e; rw [e, norm_zero] at hw0; exact zero_ne_one hw0)
          hw0s _ hv' Ws hWs δ hδ
        simp only [dsigW_eq'] at this
        exact this)
    have e : σ τ (σ τ⁻¹ v) = v := by
      rw [← hU.rep.apply_mul hτ hτ', (hG.2.2.2 τ hτ).2, hU.rep.map_one]; rfl
    simpa only [e] using h0
  by_cases h1 : c₁ = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, fin 1 0 (by rw [h1]; simp)⟩
  · exact ⟨c₂, -c₁, Or.inr (neg_ne_zero.2 h1), fin c₂ (-c₁) (by ring)⟩

end CompanionTheory.Bmu
end
end

section
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate

noncomputable section

namespace CompanionTheory.Bmu

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem prod_norm_le {n : ℕ} (W : List (Mat n)) {a : ℝ} (h : ∀ X ∈ W, ‖X‖ ≤ a) :
    (W.map fun X => ‖X‖).prod ≤ a ^ W.length := by
  induction W with
  | nil => simp
  | cons X W ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    have h0 : 0 ≤ (W.map fun X => ‖X‖).prod := List.prod_nonneg fun x hx => by
      obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
    exact mul_le_mul (h X List.mem_cons_self) (ih fun Y hY => h Y (List.mem_cons_of_mem _ hY)) h0
      ((norm_nonneg X).trans (h X List.mem_cons_self))

theorem absBound_of (hF : Factor) (hAd : DsAd) (hDer : DsDer) (hWB : WordBd) : AbsBound := by
  intro n Hm H _ _ _ σ hU V _ _ _ B hB e Q hQ C m hC hQB C₀ c w hw
  obtain ⟨N, Wd, β, hWd, hβ⟩ := hF n Hm H σ hU V B hB
  obtain ⟨Cw, hCw, hW⟩ := hWB n Hm H σ hU w hw (m + c * m)
  set A : ℝ := max 1 C₀ with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  refine ⟨C * (Cw * A ^ (m + c * m)), fun g hg M hM hconj hcase => ?_⟩
  have hMc : 1 ≤ M ^ c := one_le_pow₀ hM

  have main : ∀ R : List (Mat n), LieWd Hm R → R.length ≤ c * m → (∀ X ∈ R, ‖X‖ ≤ A) →
      ‖B (σ g (dsW σ R w))‖ ≤ C * (Cw * A ^ (m + c * m) * M ^ (c * m)) := by
    intro R hR hRl hRn
    have hu : IsSm (UH Hm) σ (dsW σ R w) := hw.dsW hU.rep hR.lieW
    refine hQB _ (hu.apply hU.rep hg) _ fun P hP => ?_
    have hPL : LieWd Hm (P.map Q) := fun X hX => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hX; exact hQ i
    obtain ⟨h1, h2⟩ := hAd n Hm H σ hU g hg _ hPL
    rw [h2 _ hu, hU.iso g hg]
    set P' := (P.map Q).map fun X => g⁻¹ * X * g with hP'
    have hl : P'.length = P.length := by simp [hP']
    have e1 : dsW σ P' (dsW σ R w) = dsW σ (P' ++ R) w := by unfold dsW; rw [List.foldr_append]
    rw [e1]
    refine (hW (P' ++ R) (fun X hX => (List.mem_append.1 hX).elim (h1 X) (hR X))
      (by rw [List.length_append, hl]; omega)).trans ?_
    rw [List.map_append, List.prod_append, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hCw
    have b1 : (P'.map fun X => ‖X‖).prod ≤ (A * M ^ c) ^ m := by
      refine (prod_norm_le P' (a := A * M ^ c) fun X hX => ?_).trans ?_
      · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hY
        exact (hconj i).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      · exact pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hA1 hMc) (hl ▸ hP)
    have b2 : (R.map fun X => ‖X‖).prod ≤ A ^ (c * m) := (prod_norm_le R hRn).trans (pow_le_pow_right₀ hA1 hRl)
    have h0 : 0 ≤ (R.map fun X => ‖X‖).prod := List.prod_nonneg fun x hx => by
      obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
    calc _ ≤ (A * M ^ c) ^ m * A ^ (c * m) := mul_le_mul b1 b2 h0 (by positivity)
      _ = A ^ (m + c * m) * M ^ (c * m) := by rw [mul_pow, ← pow_mul, pow_add]; ring
  rcases hcase with h1 | ⟨Y, lam, hY, hYn, hlam, hχ⟩
  · have := main [] (fun _ h => absurd h List.not_mem_nil) (Nat.zero_le _) (fun _ h => absurd h List.not_mem_nil)
    rw [h1, one_pow, mul_one] at this
    exact this
  · have step : ∀ u, IsSm (UH Hm) σ u → B (σ g (ds σ Y u)) = (Complex.I * lam) • B (σ g u) := by
      intro u hu
      have hds : IsSm (UH Hm) σ (ds σ Y u) :=
        hu.dsW hU.rep (W := [Y]) (LieWd.lieW fun X hX => by rw [List.mem_singleton.1 hX]; exact hY)
      have d1 : HasDerivAt (fun τ : ℝ => ∑ i, β i (dsW σ (Wd i) (σ (g * ex Y τ) u)))
          (∑ i, β i (dsW σ (Wd i) (σ g (ds σ Y u)))) 0 :=
        HasDerivAt.fun_sum fun i _ => ((β i).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
          (hDer n Hm H σ hU _ (hWd i) g hg Y hY u hu)
      have e1 : (fun τ : ℝ => ∑ i, β i (dsW σ (Wd i) (σ (g * ex Y τ) u))) =
          fun τ : ℝ => Complex.exp (Complex.I * (lam * τ : ℝ)) • B (σ g u) := by
        funext τ
        rw [← hβ _ (hu.apply hU.rep (hU.rep.mul_mem _ hg _ (ex_mem_of_lie hY τ))), hχ τ u hu]
      have d2 : HasDerivAt (fun τ : ℝ => Complex.exp (Complex.I * (lam * τ : ℝ))) (Complex.I * lam) 0 := by
        have h1 : HasDerivAt (fun τ : ℝ => Complex.I * ((lam * τ : ℝ) : ℂ)) (Complex.I * lam) 0 := by
          have := (((hasDerivAt_id (0 : ℝ)).const_mul lam).ofReal_comp).const_mul Complex.I
          simpa using this
        simpa using h1.cexp
      rw [e1, ← hβ _ (hds.apply hU.rep hg)] at d1
      exact d1.unique (d2.smul_const _)
    have iter : ∀ j : ℕ, B (σ g (dsW σ (List.replicate j Y) w)) = (Complex.I * lam) ^ j • B (σ g w) := by
      intro j
      induction j with
      | zero => simp [dsW]
      | succ j ih =>
        have hu : IsSm (UH Hm) σ (dsW σ (List.replicate j Y) w) :=
          hw.dsW hU.rep (LieWd.lieW fun X hX => by rw [List.eq_of_mem_replicate hX]; exact hY)
        rw [List.replicate_succ, dsW_cons, step _ hu, ih, smul_smul, pow_succ']
    have h := main (List.replicate (c * m) Y) (fun X hX => by rw [List.eq_of_mem_replicate hX]; exact hY)
      (by simp) (fun X hX => by rw [List.eq_of_mem_replicate hX]; exact hYn.trans (le_max_right _ _))
    rw [iter, norm_smul, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at h
    have hMp : 0 < M ^ (c * m) := by positivity
    have h2 : M ^ (c * m) * ‖B (σ g w)‖ ≤ |lam| ^ (c * m) * ‖B (σ g w)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hlam _) (norm_nonneg _)
    refine le_of_mul_le_mul_left (h2.trans (h.trans_eq ?_)) hMp
    ring

end CompanionTheory.Bmu
end
end

section
namespace CompanionTheory.Bmu

theorem bounded : Bounded :=
  bounded_of (GlobalTheory.T.quotient_bound_of_factor_reduce_chart GlobalTheory.T.factorization' (GlobalTheory.T.reduction_of_derived_series GlobalTheory.T.DerivedSeriesLinear GlobalTheory.T.DerivedSeriesAdjoint GlobalTheory.T.DerivedSeriesDerivation) GlobalTheory.T.ChartExistence)
    (absBound_of GlobalTheory.T.factorization' GlobalTheory.T.DerivedSeriesAdjoint GlobalTheory.T.DerivedSeriesDerivation (GlobalTheory.T.word_length_bound_of_linear GlobalTheory.T.DerivedSeriesLinear)) GlobalTheory.T.AdaptedBasisExistsAlt
    (GlobalTheory.T.decomposition_of_iwasawa_levi_cartan GlobalTheory.T.AdaptedBasisExistsAlt GlobalTheory.T.IwasawaDecomposition GlobalTheory.T.LeviDecomposition GlobalTheory.T.CartanDecomposition) GlobalTheory.T.torBound' GlobalTheory.T.SpanGenerators
    GlobalTheory.T.ExponentialMembership GlobalTheory.T.RootVectors

theorem besselMapUniqGap : BesselMapUniqGap :=
  uniq_of bounded (GlobalTheory.T.truncated_derivation_limit GlobalTheory.T.factorization' GlobalTheory.T.TruncatedDerivation) GlobalTheory.T.TorusConjugacy GlobalTheory.T.DerivedSeriesAdjoint GlobalTheory.T.factorization'

end CompanionTheory.Bmu
end
