import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DBoundB
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilAH

variable {D : D7} {n : ℕ}

theorem cLoc_pos {l : D.what₂.Tau → ℝ} {τ : D.what₂.Tau} (h : l τ ≠ 0) : 0 < cLoc l τ := by
  unfold cLoc; have := abs_pos.2 h; positivity

theorem abs_tLoc (l : D.what₂.Tau → ℝ) (τ : D.what₂.Tau) : |tLoc l τ| = cLoc l τ := by
  unfold tLoc cLoc; rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

theorem trace_gramB_real {m : ℕ} (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    (gramB ε b u).trace = ((∑ a ∈ Finset.univ.filter (fun a => ε a = b), ∑ j, ‖u a j‖ ^ 2 : ℝ) : ℂ) := by
  simp only [gramB, evX, Qb, map_sum, map_mul, MvPolynomial.eval_X, if_true, Bool.false_eq_true, if_false,
    Matrix.trace, Matrix.diag]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.conj_mul', Complex.star_def]

theorem sum_filter_bool {m : ℕ} (ε : Fin m → Bool) (f : Fin m → ℝ) :
    ∑ a ∈ Finset.univ.filter (fun a => ε a = true), f a + ∑ a ∈ Finset.univ.filter (fun a => ε a = false), f a =
      ∑ a, f a := by
  rw [← Finset.sum_union]
  · congr 1; ext a; cases ε a <;> simp
  · rw [Finset.disjoint_filter]; intro a _ h; simp [h]

theorem gC_gauss {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (hc : 0 < c) (δ : ℝ) (u : Fin m → Fin n → ℂ) :
    gC ε t c ((Complex.I * (δ / c : ℝ)) • 1) ((-(Complex.I * (δ / c : ℝ))) • 1) u =
      Complex.exp (-((δ * ∑ a, ∑ j, ‖u a j‖ ^ 2 : ℝ) : ℂ)) := by
  unfold gC
  congr 1
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul, trace_gramB_real]
  have h := sum_filter_bool (epsT t ε) (fun a => ∑ j, ‖u a j‖ ^ 2)
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [← h]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem fP_one {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (hc : 0 < c) :
    fP c (1 : PX m n) = gZf ε t c (Complex.I • 1) := by
  funext u
  have e1 : gZf ε t c (Complex.I • 1) u = gC ε t c ((Complex.I * (c / c : ℝ)) • 1) ((-(Complex.I * (c / c : ℝ))) • 1) u := by
    unfold gZf gC
    rw [div_self hc.ne', Complex.ofReal_one, mul_one, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.star_def, Complex.conj_I]
  rw [e1, gC_gauss ε t c hc c u]
  simp [fP, evX, gs]

end PositivityTheory.Rg.Sw.Glob.DilAH
end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilBH

variable {D : D7} {n : ℕ}

theorem compAt_add {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (x y : Mx D m n) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.add_apply, map_add]

theorem pointAt {m : ℕ} (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (hfr : IsUnit fr.det) (x₀ : Mx D m n) (u : Fin m → Fin n → ℂ) :
    ∃ x : Mx D m n, fr⁻¹ * compAt θ τ x = Matrix.of u ∧ (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x₀) ∧
      x.map (finPart D) = x₀.map (finPart D) := by
  obtain ⟨L, _, hLf, hLz⟩ :=
    Formalism.IndefR.Eqv.lineAtExists_holds D θ hθ m n τ (fr * Matrix.of u - compAt θ τ x₀)
  refine ⟨x₀ + L 1, ?_, ?_, ?_⟩
  · rw [compAt_add, hLz 1 τ, if_pos rfl, Complex.ofReal_one, one_smul]
    have hs : compAt θ τ x₀ + (fr * Matrix.of u - compAt θ τ x₀) = fr * Matrix.of u := by abel
    rw [hs]
    exact Matrix.nonsing_inv_mul_cancel_left _ _ hfr
  · intro τ' h
    rw [compAt_add, hLz 1 τ', if_neg h, add_zero]
  · ext i j
    have h1 := congrFun (congrFun (hLf 1) i) j
    simp only [Matrix.map_apply, Matrix.add_apply, map_add, Matrix.zero_apply] at h1 ⊢
    rw [h1, add_zero]

end PositivityTheory.Rg.Sw.Glob.DilBH
end
end

section
noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.Glob

namespace SchwartzDifferenceQuotient

variable {m n : ℕ}

instance haarInner (n : ℕ) : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

instance haarOuter (m n : ℕ) : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

theorem isSch_sub {f g : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) (hg : IsSch g) : IsSch (f - g) := by
  obtain ⟨S, rfl⟩ := hf
  obtain ⟨S', rfl⟩ := hg
  exact ⟨S - S', by ext u; simp⟩

theorem isSch_smul (a : ℂ) {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) : IsSch (fun u => a * f u) := by
  obtain ⟨S, rfl⟩ := hf
  exact ⟨a • S, by ext u; simp [smul_eq_mul]⟩

theorem isSch_continuous {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) : Continuous f := by
  obtain ⟨S, rfl⟩ := hf
  exact S.continuous

theorem isSch_sq_integrable {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) :
    Integrable (fun u => ‖f u‖ ^ 2) := by
  obtain ⟨S, rfl⟩ := hf
  exact (S.memLp ((2 : ℕ) : ENNReal) volume).integrable_norm_pow two_ne_zero

end SchwartzDifferenceQuotient

open SchwartzDifferenceQuotient in
theorem dL2 : DifferenceQuotientIsometryExchange := by
  intro m n T κ hκ hTS hTsub hTsmul hTiso G G' E' s hG hG' hE' hL2 hpt
  have hD : ∀ h : ℝ, IsSch (fun u => (G (s + h) u - G s u) / (h : ℂ) - G' u) := by
    intro h
    have h3 := isSch_sub (isSch_smul ((h : ℂ)⁻¹) (isSch_sub (hG (s + h)) (hG s))) hG'
    convert h3 using 1
    funext u
    simp only [Pi.sub_apply]
    try ring
  have hTD : ∀ h : ℝ, T (fun u => (G (s + h) u - G s u) / (h : ℂ) - G' u) =
      fun u => (T (G (s + h)) u - T (G s) u) / (h : ℂ) - T G' u := by
    intro h
    have e1 : (fun u => (G (s + h) u - G s u) / (h : ℂ) - G' u) =
        (fun u => (h : ℂ)⁻¹ * (G (s + h) - G s) u) - G' := by
      funext u
      simp only [Pi.sub_apply]
      try ring
    rw [e1, hTsub _ _ (isSch_smul _ (isSch_sub (hG _) (hG _))) hG',
      hTsmul _ _ (isSch_sub (hG _) (hG _)), hTsub _ _ (hG _) (hG _)]
    funext u
    simp only [Pi.sub_apply]
    try ring
  obtain ⟨F, hF⟩ : ∃ F : ℝ → (Fin m → Fin n → ℂ) → ENNReal,
      F = fun h u => ENNReal.ofReal (‖(T (G (s + h)) u - T (G s) u) / (h : ℂ) - T G' u‖ ^ 2) := ⟨_, rfl⟩
  have hmeas : ∀ h, Measurable (F h) := by
    intro h
    have hc := isSch_continuous (hTS _ (hD h))
    rw [hTD] at hc
    rw [hF]
    exact ENNReal.measurable_ofReal.comp (hc.norm.pow 2).measurable
  have hlim_pt : ∀ u, Tendsto (fun h => F h u) (𝓝[≠] 0) (𝓝 (ENNReal.ofReal (‖E' u - T G' u‖ ^ 2))) := by
    intro u
    rw [hF]
    have h1 := ((hpt u).sub_const (T G' u)).norm.pow 2
    exact (ENNReal.continuous_ofReal.tendsto _).comp h1
  have hint : ∀ h, ∫⁻ u, F h u = ENNReal.ofReal (κ * ∫ u, ‖(G (s + h) u - G s u) / (h : ℂ) - G' u‖ ^ 2) := by
    intro h
    rw [← hTiso _ (hD h), hTD, ofReal_integral_eq_lintegral_ofReal, hF]
    · have hi := isSch_sq_integrable (hTS _ (hD h))
      rw [hTD] at hi
      exact hi
    · exact Filter.Eventually.of_forall fun u => sq_nonneg _
  have hlim_int : Tendsto (fun h => ∫⁻ u, F h u) (𝓝[≠] 0) (𝓝 0) := by
    simp_rw [hint]
    have h1 := hL2.const_mul κ
    rw [mul_zero] at h1
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    rw [ENNReal.ofReal_zero] at h2
    exact h2
  have hfatou := lintegral_liminf_le (μ := (volume : Measure (Fin m → Fin n → ℂ))) (u := 𝓝[≠] (0 : ℝ)) hmeas
  rw [hlim_int.liminf_eq] at hfatou
  have hz : ∫⁻ u, ENNReal.ofReal (‖E' u - T G' u‖ ^ 2) = 0 := by
    refine le_antisymm ?_ (by simp)
    calc _ = ∫⁻ u, liminf (fun h => F h u) (𝓝[≠] (0 : ℝ)) := by
          congr 1
          funext u
          exact ((hlim_pt u).liminf_eq).symm
      _ ≤ 0 := hfatou
  have hcT := isSch_continuous (hTS _ hG')
  have hcE : Continuous fun u => E' u - T G' u := hE'.sub hcT
  have hm : Measurable fun u => ENNReal.ofReal (‖E' u - T G' u‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (hcE.norm.pow 2).measurable
  rw [lintegral_eq_zero_iff hm] at hz
  have hae : E' =ᵐ[volume] T G' := by
    filter_upwards [hz] with u hu
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hu
    exact sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm hu (sq_nonneg _))))
  exact ((Continuous.ae_eq_iff_eq volume hE' hcT).mp hae).symm

end PositivityTheory.Rg.Sw.Glob
end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilCH

variable {D : D7} {n : ℕ} {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem tens_cancel (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ} (hΨ : AwayCls θ τ fr Ψ)
    {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) {F G : (Fin V.rank → Fin n → ℂ) → ℂ}
    (h : tens θ τ fr F Ψ = tens θ τ fr G Ψ) : F = G := by
  funext u
  obtain ⟨x, hxu, hxo, hxf⟩ := DilBH.pointAt θ hθ τ fr hfr x₀ u
  have hΨx : Ψ x = Ψ x₀ := hΨ.1 x x₀ hxo hxf
  have := congrFun h x
  simp only [tens, hxu, hΨx] at this
  exact mul_right_cancel₀ hx₀ this

variable {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {ι : GR n →* G D n}
  {L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)}

theorem L_sub (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) (y : GR n) {f g : (Fin V.rank → Fin n → ℂ) → ℂ}
    (hf : IsSch f) (hg : IsSch g) : L y (f - g) = L y f - L y g := by
  have h := hL.2 y Ψ hΨ (f - g) (SchwartzDifferenceQuotient.isSch_sub hf hg)
  have e : (⟨tens θ τ fr (f - g) Ψ, hΨ.2 _ (SchwartzDifferenceQuotient.isSch_sub hf hg)⟩ : schwartzA θ V.rank n) =
      ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ - ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ :=
    Subtype.ext (by funext x; simp only [tens, Submodule.coe_sub]; show (f _ - g _) * _ = f _ * _ - g _ * _; ring)
  rw [e, map_sub, Submodule.coe_sub, hL.2 y Ψ hΨ f hf, hL.2 y Ψ hΨ g hg] at h
  refine tens_cancel hθ hfr hΨ hx₀ ?_
  rw [← h]; funext x
  show tens θ τ fr (L y f) Ψ x - tens θ τ fr (L y g) Ψ x = _
  simp only [tens]
  show _ = (L y f _ - L y g _) * _
  ring

theorem L_smul (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) (y : GR n) (a : ℂ) {f : (Fin V.rank → Fin n → ℂ) → ℂ}
    (hf : IsSch f) : L y (fun u => a * f u) = fun u => a * L y f u := by
  have h := hL.2 y Ψ hΨ _ (SchwartzDifferenceQuotient.isSch_smul a hf)
  have e : (⟨tens θ τ fr (fun u => a * f u) Ψ, hΨ.2 _ (SchwartzDifferenceQuotient.isSch_smul a hf)⟩ : schwartzA θ V.rank n) =
      a • ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ :=
    Subtype.ext (by funext x; simp [tens, mul_assoc])
  rw [e, map_smul, Submodule.coe_smul, hL.2 y Ψ hΨ f hf] at h
  refine tens_cancel hθ hfr hΨ hx₀ ?_
  rw [← h]; funext x; simp [tens, mul_assoc]

theorem L_mul (hL : IsLocFact ω τ fr ι L) (hθ : IsInfFam θ) (hfr : IsUnit fr.det) {Ψ : Mx D V.rank n → ℂ}
    (hΨ : AwayCls θ τ fr Ψ) {x₀ : Mx D V.rank n} (hx₀ : Ψ x₀ ≠ 0) (y y' : GR n) {f : (Fin V.rank → Fin n → ℂ) → ℂ}
    (hf : IsSch f) : L (y * y') f = L y (L y' f) := by
  have h := hL.2 (y * y') Ψ hΨ f hf
  have h' : ω (ι y') ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ = ⟨tens θ τ fr (L y' f) Ψ, hΨ.2 _ (hL.1 y' f hf)⟩ :=
    Subtype.ext (hL.2 y' Ψ hΨ f hf)
  rw [map_mul, map_mul, Module.End.mul_apply, h', hL.2 y Ψ hΨ _ (hL.1 y' f hf)] at h
  exact tens_cancel hθ hfr hΨ hx₀ h.symm

theorem diffOn_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (r : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv r f) U := by
  induction r with
  | zero => simpa using hf
  | succ r ih => rw [iteratedDeriv_succ]; exact ih.deriv hU

theorem iteratedDeriv_ofReal {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hR : ∀ s : ℝ, (s : ℂ) ∈ U) (r : ℕ) : iteratedDeriv r (fun t : ℝ => f t) = fun t : ℝ => iteratedDeriv r f t := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hd : DifferentiableAt ℂ (iteratedDeriv r f) t :=
      (diffOn_iteratedDeriv hU hf r).differentiableAt (hU.mem_nhds (hR t))
    rw [iteratedDeriv_succ]
    exact (hd.hasDerivAt.comp_ofReal).deriv

end PositivityTheory.Rg.Sw.Glob.DilCH
end
end

section
noncomputable section

open Topology

namespace PositivityTheory.Rg.Sw.Glob

def ContDeriv : Prop :=
  ∀ (m n : ℕ) (U : Set ℂ), IsOpen U → ∀ f : ℂ → (Fin m → Fin n → ℂ) → ℂ,
    ContinuousOn (fun p : ℂ × (Fin m → Fin n → ℂ) => f p.1 p.2) (U ×ˢ Set.univ) →
    (∀ u, DifferentiableOn ℂ (fun z => f z u) U) →
    ∀ r : ℕ, ContinuousOn (fun p : ℂ × (Fin m → Fin n → ℂ) => iteratedDeriv r (fun z => f z p.2) p.1) (U ×ˢ Set.univ)

def SchScale : Prop :=
  ∀ (m n : ℕ) (f : (Fin m → Fin n → ℂ) → ℂ) (s : ℝ) (X : Fin n → ℝ) (a : ℂ), IsSch f →
    IsSch (fun u => a * f (fun i j => u i j * Real.exp (s * X j)))

end PositivityTheory.Rg.Sw.Glob
end
end
