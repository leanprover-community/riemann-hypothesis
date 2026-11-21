import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeRaiseWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormPowerIntegralHermLineBundlePow
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimultaneousDiagonalisationPosDefHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosDefOfL2Definite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosDefL2LeSupOfLinIndep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramIsHermitianL2EqDoubleSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVolumeDensityFiniteIsOpenPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMorseSectionsMLAddAUniform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChernTopPowerVolumeDensityRatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaiseFirstWeightSectionsLociValuesNorms

section
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.MetFam

open MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V cHess wd wdb)
open scoped ContDiff ENNReal

theorem contDiffAt_fderiv_snd {D : ℕ} {Θ : ℝ × V D → ℂ} {x₀ : ℝ × V D} {m n : WithTop ℕ∞} (h : ContDiffAt ℝ n Θ x₀)
    (hmn : m + 1 ≤ n) (e : V D) :
    ContDiffAt ℝ m (fun x : ℝ × V D => fderiv ℝ (fun v => Θ (x.1, v)) x.2 e) x₀ := by
  have h₁ : ContDiffAt ℝ n (Function.uncurry fun (x : ℝ × V D) (v : V D) => Θ (x.1, v)) (x₀, x₀.2) :=
    ContDiffAt.comp (g := Θ) (f := fun w : (ℝ × V D) × V D => (w.1.1, w.2)) (x₀, x₀.2) h
      ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd).contDiffAt
  exact (h₁.fderiv contDiffAt_snd hmn).clm_apply contDiffAt_const

theorem continuousAt_cHess_snd {D : ℕ} {Θ : ℝ × V D → ℂ} {x₀ : ℝ × V D} (h : ContDiffAt ℝ 2 Θ x₀) :
    ContinuousAt (fun x : ℝ × V D => cHess D (fun v => Θ (x.1, v)) x.2) x₀ := by
  refine continuousAt_pi.2 fun j => continuousAt_pi.2 fun l => ?_
  have h₁ : ContDiffAt ℝ 1 (fun x : ℝ × V D => wdb D l (fun v => Θ (x.1, v)) x.2) x₀ :=
    ((contDiffAt_fderiv_snd h (by norm_num) _).add
      (contDiffAt_const.mul (contDiffAt_fderiv_snd h (by norm_num) _))).div_const 2
  have h₂ : ContDiffAt ℝ 0 (fun x : ℝ × V D =>
      wd D j (fun v => wdb D l (fun w => Θ (x.1, w)) v) x.2) x₀ :=
    ((contDiffAt_fderiv_snd h₁ (by norm_num) _).sub
      (contDiffAt_const.mul (contDiffAt_fderiv_snd h₁ (by norm_num) _))).div_const 2
  exact h₂.continuousAt

theorem FamAt.exists_bound_chernDens {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {t : ℝ → ℝ} (ht : Tendsto t atTop (𝓝 0)) {B : LB X} {φ : Weight p σ B} (hφ : φ.IsCInf)
    {u : ℝ → CxPts p σ → ℝ} (hu : ∀ R y, CInfAt (u R) y) {u₀ : CxPts p σ → ℝ} {y : CxPts p σ} (h : FamAt t u u₀ y)
    (c : AlgChart p σ D) (hy : y ∈ c.e.source) :
    ∃ K : ℝ, ∀ᶠ x : ℝ × CxPts p σ in atTop ×ˢ 𝓝 y, |c.chernDens (φ.addFn (u x.1)) x.2| ≤ K := by
  obtain ⟨ι, _, f, Φ, O, h₁, h₂, h₃, h₄, -, h₆⟩ := h
  have hi := mem_pick φ.isLB y
  set i := pick φ.isLB y
  set Θ : ℝ × V D → ℂ := fun x => ((φ.φ i (c.e.symm x.2) + Φ (x.1, f (c.e.symm x.2)) : ℝ) : ℂ) with hΘ
  have hΘd : ContDiffAt ℝ 2 Θ (0, c.e y) := by
    have a₁ : ContDiffAt ℝ 2 (fun x : ℝ × V D => φ.φ i (c.e.symm x.2)) (0, c.e y) :=
      ContDiffAt.comp (g := fun v => φ.φ i (c.e.symm v)) (0, c.e y) (hφ.contDiffAt c hy hi) contDiffAt_snd
    have a₂ : ContDiffAt ℝ 2 (fun x : ℝ × V D => f (c.e.symm x.2)) (0, c.e y) :=
      ContDiffAt.comp (g := fun v => f (c.e.symm v)) (0, c.e y)
        ((h₁.contDiffAt_chart c hy).of_le (by norm_cast)) contDiffAt_snd
    have a₃ : ContDiffAt ℝ 2 Φ (0, f (c.e.symm (c.e y))) := by
      rw [c.e.left_inv hy]
      exact (h₄.contDiffAt (h₂.mem_nhds h₃)).of_le (by norm_cast)
    have a₄ : ContDiffAt ℝ 2 (fun x : ℝ × V D => Φ (x.1, f (c.e.symm x.2))) (0, c.e y) :=
      ContDiffAt.comp (g := Φ) (f := fun x : ℝ × V D => (x.1, f (c.e.symm x.2))) (0, c.e y) a₃
        (contDiffAt_fst.prodMk a₂)
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ (a₁.add a₄)
  set G : ℝ × V D → ℝ := fun x => D.factorial / Real.pi ^ D * (cHess D (fun v => Θ (x.1, v)) x.2).det.re with hG
  have hGc : ContinuousAt G (0, c.e y) :=
    continuousAt_const.mul (Complex.continuous_re.continuousAt.comp
      ((continuous_id.matrix_det).continuousAt.comp (continuousAt_cHess_snd hΘd)))
  have hT : Tendsto (fun x : ℝ × CxPts p σ => G (t x.1, c.e x.2)) (atTop ×ˢ 𝓝 y) (𝓝 (G (0, c.e y))) :=
    hGc.tendsto.comp ((ht.comp tendsto_fst).prodMk_nhds ((c.e.continuousAt hy).tendsto.comp tendsto_snd))
  refine ⟨|G (0, c.e y)| + 1, ?_⟩
  obtain ⟨pa, ha, pb, hb, hab⟩ := eventually_prod_iff.1 h₆
  filter_upwards [hT.abs.eventually (ge_mem_nhds (lt_add_one _)), tendsto_fst.eventually ha,
    tendsto_snd.eventually hb.eventually_nhds, tendsto_snd.eventually (c.e.open_source.mem_nhds hy),
    tendsto_snd.eventually ((isOpen_ptsIn (B.U i)).mem_nhds hi)] with x hx hxa hxb hxs hxi
  have e : (fun v => ((φ.addFn (u x.1)).φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e x.2)] fun v => Θ (t x.1, v) := by
    have hc := c.e.continuousAt_symm (c.e.map_source hxs)
    rw [ContinuousAt, c.e.left_inv hxs] at hc
    filter_upwards [hc.eventually hxb] with v hv
    simp only [hΘ, Weight.addFn, hab hxa hv]
  rw [c.chernDens_eq (hφ.addFn (hu x.1)) hxs hxi, AlgChart.hess, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e]
  exact hx

theorem exists_bound_chernPart_univ : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ t : ℝ → ℝ, Tendsto t atTop (𝓝 0) → ∀ (σ : k →+* ℂ) (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ u : ℝ → CxPts p σ → ℝ, (∀ R y, CInfAt (u R) y) → (∀ y, FamAt t u (fun _ => 0) y) → ∃ C : NNReal, ∀ᶠ R in atTop, ∀ ε : ℤˣ, (φ.addFn (u R)).chernPart D ε Set.univ ≤ (C : ENNReal) := by
  intro k _ X _ p D hX hS t ht σ B φ hφ u hu hF
  have := hX.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  obtain ⟨A⟩ := hS σ
  have hloc : ∀ y : CxPts p σ, ∃ U : Set (CxPts p σ), IsOpen U ∧ y ∈ U ∧ ∃ C : NNReal,
      ∀ᶠ R in atTop, ∀ ε : ℤˣ, (φ.addFn (u R)).chernPart D ε U ≤ (C : ENNReal) := by
    intro y
    obtain ⟨a, hy⟩ := A.cover y
    set c := A.chart a
    obtain ⟨K, hK⟩ := (hF y).exists_bound_chernDens ht hφ hu c hy
    obtain ⟨pa, ha, pb, hb, hab⟩ := eventually_prod_iff.1 hK
    have hball : ∀ᶠ z in 𝓝 y, c.e z ∈ Metric.closedBall (c.e y) 1 :=
      (c.e.continuousAt hy).eventually (Metric.closedBall_mem_nhds _ one_pos)
    obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.1 (hb.and (hball.and (c.e.open_source.mem_nhds hy)))
    have hUs : U ⊆ c.e.source := fun z hz => (hU z hz).2.2
    have hfin : ENNReal.ofReal K * volume (Metric.closedBall (c.e y) 1) ≠ ⊤ :=
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top).ne
    refine ⟨U, hUo, hyU, (ENNReal.ofReal K * volume (Metric.closedBall (c.e y) 1)).toNNReal, ?_⟩
    filter_upwards [ha] with R hR ε
    rw [ENNReal.coe_toNNReal hfin, Weight.chernPart_apply (hφ.addFn (hu R)) ε c hUo.measurableSet hUs]
    have hm := GlobalTheory.ChartGlue.measurableSet_image c.e hUo.measurableSet hUs
    calc _ ≤ ∫⁻ _ in c.e '' U, ENNReal.ofReal K := by
          refine setLIntegral_mono' hm ?_
          rintro _ ⟨z, hz, rfl⟩
          refine ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ?_)
          rw [c.e.left_inv (hUs hz), abs_mul]
          have := hab hR (hU z hz).1
          rcases Int.units_eq_one_or ε with rfl | rfl <;> simpa using this
      _ = ENNReal.ofReal K * volume (c.e '' U) := setLIntegral_const _ _
      _ ≤ _ := by
          gcongr
          rintro _ ⟨z, hz, rfl⟩
          exact (hU z hz).2.1
  choose U hUo hyU C hC using hloc
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUo (fun y _ => Set.mem_iUnion.2 ⟨y, hyU y⟩)
  refine ⟨∑ y ∈ s, C y, ?_⟩
  filter_upwards [(eventually_all_finset s).2 fun y _ => hC y] with R hR ε
  refine (measure_mono hs).trans ((measure_biUnion_finset_le s U).trans ?_)
  rw [ENNReal.coe_finset_sum]
  exact Finset.sum_le_sum fun y hy => hR y hy ε

end GlobalTheory.MetFam
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_part_uniform_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ t : ℝ → ℝ, Tendsto t atTop (𝓝 0) → ∀ (σ : k →+* ℂ) (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ u : ℝ → CxPts p σ → ℝ, (∀ R y, CInfAt (u R) y) → (∀ y, FamAt t u (fun _ => 0) y) → ∃ C : NNReal, ∀ᶠ R in atTop, ∀ ε : ℤˣ, (φ.addFn (u R)).chernPart D ε Set.univ ≤ (C : ENNReal) := by
  atlas_forward_decl GlobalTheory.MetFam.exists_bound_chernPart_univ
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.HermLB GlobalTheory.CxPts GlobalTheory.MetFam GlobalTheory.Published

namespace GlobalTheory.SelfCont

theorem tendsto_zero_of_pow {ι α : Type} [Fintype ι] {l : Filter α} (d : ℕ) (Φ : α → MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (h : ∀ n : ι → ℤ, Tendsto (fun R => Φ R (lin (fun i => (n i : ℝ)) ^ d)) l (𝓝 0))
    (h' : ∀ (P : MvPolynomial ι ℝ) (e : ℕ), e ≠ d → P.IsHomogeneous e → ∀ R, Φ R P = 0) (P : MvPolynomial ι ℝ) :
    Tendsto (fun R => Φ R P) l (𝓝 0) := by
  let S : Submodule ℝ (MvPolynomial ι ℝ) :=
    { carrier := {P | Tendsto (fun R => Φ R P) l (𝓝 0)}
      add_mem' := fun {a b} ha hb => by simpa using Tendsto.add ha hb
      zero_mem' := by simpa using tendsto_const_nhds
      smul_mem' := fun c a ha => by simpa using Tendsto.const_mul c ha }
  by_contra hP
  obtain ⟨f, hf, hS⟩ := S.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 fun e => hP (show P ∈ S from e ▸ trivial))
  exact hf (Model.eq_zero_of_pow d f (fun n => hS (h n)) fun Q e he hQ =>
    hS (show Tendsto _ _ _ by simpa only [h' Q e he hQ] using tendsto_const_nhds))

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem icls_fnB_add {u v w : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu hc hv hd hw he) (e : ∀ σ y, w σ y = u σ y + v σ y) :
    (fnB w hw he).icls = (fnB u hu hc).icls + (fnB v hv hd).icls := by
  rw [← icls_tens, icls_eq_iff.2 (isometric_tens_fnB _ v hv hd)]
  exact icls_eq_iff.2 (isometric_of_eqOn fun σ _ y _ => (e σ y).symm)

theorem isConj_mul {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ}
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (c : ℝ) (σ σ' : k →+* ℂ) :
    (Weight.ofFun fun y => c * u σ y).IsConj (Weight.ofFun fun y => c * u σ' y) :=
  fun i y y' h hy => congrArg (c * ·) (hc σ σ' i y y' h hy)

theorem icls_fnB_mul {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu : ∀ σ y, CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (n : ℤ) :
    (fnB (fun σ y => (n : ℝ) * u σ y) (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _)).icls =
      n • (fnB u hu hc).icls := by
  have key (m : ℤ) := icls_fnB_add (p := p) (w := fun σ y => ((m + 1 : ℤ) : ℝ) * u σ y) (u := fun σ y => (m : ℝ) * u σ y)
    (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _) hu hc (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _)
    fun σ y => by push_cast; ring
  induction n using Int.induction_on with
  | zero =>
    have := icls_fnB_add (p := p) (w := u) (u := fun σ y => ((0 : ℤ) : ℝ) * u σ y)
      (fun σ y => (hu σ y).const_mul _) (isConj_mul hc _) hu hc hu hc fun σ y => by push_cast; ring
    rw [zero_smul]
    exact right_eq_add.1 this
  | succ n ih => rw [key, ih, add_smul, one_smul]
  | pred n ih =>
    have := key (-(n : ℤ) - 1)
    simp only [sub_add_cancel] at this
    rw [sub_smul, one_smul, ← ih, this, add_sub_cancel_right]

theorem tendsto_integral_zero {α β : Type} [MeasurableSpace β] {l : Filter α} {u : α → β → ℝ} {μ : α → Measure β}
    (hu : TendstoUniformly u (fun _ => 0) l) {C : NNReal} (hC : ∀ᶠ R in l, μ R Set.univ ≤ (C : ENNReal)) :
    Tendsto (fun R => ∫ y, u R y ∂μ R) l (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have h1 : (0 : ℝ) < C + 1 := by positivity
  filter_upwards [hC, Metric.tendstoUniformly_iff.1 hu _ (div_pos hε h1)] with R h₁ h₂
  have : IsFiniteMeasure (μ R) := ⟨h₁.trans_lt ENNReal.coe_lt_top⟩
  have h₃ : (μ R).real Set.univ ≤ C := ENNReal.toReal_le_coe_of_le_coe h₁
  rw [dist_zero_right]
  refine (norm_integral_le_of_norm_le_const (C := ε / (C + 1)) (.of_forall fun y => ?_)).trans_lt ?_
  · simpa only [dist_zero_left] using (h₂ y).le
  · calc ε / (C + 1) * (μ R).real Set.univ < ε / (C + 1) * (C + 1) :=
          mul_lt_mul_of_pos_left (by linarith) (div_pos hε h1)
      _ = ε := div_mul_cancel₀ _ h1.ne'

variable [IsIntegral X] {D : ℕ} {t : ℝ → ℝ} {u : ℝ → ∀ σ : k →+* ℂ, CxPts p σ → ℝ}

theorem tendsto_chInt (hX : IsArithVar p D) (hs : GenSmooth p D) (ht : Tendsto t atTop (𝓝 0))
    (hu : ∀ R σ y, CInfAt (u R σ) y) (hc : ∀ R σ σ', (Weight.ofFun (u R σ)).IsConj (Weight.ofFun (u R σ')))
    (hf : ∀ σ y, FamAt t (fun R => u R σ) (fun _ => 0) y) (N : HermLB p) (c : ℝ) :
    Tendsto (fun R => chInt (N.raise (fun σ y => c * u R σ y) (fun σ y => (hu R σ y).const_mul _) (isConj_mul (hc R) _))
      D (u R)) atTop (𝓝 0) := by
  have := hX.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  simp only [chInt, finsum_eq_sum_of_fintype, Weight.chernInt, Measure.restrict_univ]
  rw [← Finset.sum_const_zero (s := (Finset.univ : Finset (k →+* ℂ))), ← sub_zero (0 : ℝ)]
  refine tendsto_finsetSum _ fun σ _ => ?_
  have := hX.compactSpace σ
  have hU := tendstoUniformly_of_famAt ht (hf σ)
  obtain ⟨C, hC⟩ := T.chern_part_uniform_bound k X p D hX hs t ht σ N.B (N.φ σ) (N.cInf σ) (fun R y => c * u R σ y)
    (fun R y => (hu R σ y).const_mul _) fun y => by
      simpa only [mul_zero] using (hf σ y).comp_contDiff (Ψ := fun x : ℝ => c * x) (contDiff_const.mul contDiff_id)
  exact (tendsto_integral_zero hU (hC.mono fun R h => h 1)).sub (tendsto_integral_zero hU (hC.mono fun R h => h (-1)))

omit [IsIntegral X] in

theorem isometric_comb_raise {v : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hv : ∀ σ y, CInfAt (v σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (v σ)).IsConj (Weight.ofFun (v σ'))) (N : HermLB p) (n : Fin 2 → ℤ) :
    (comb ![fnB v hv hc, N] n).Isometric ((zp N (n 1)).raise (fun σ y => (n 0 : ℝ) * v σ y)
      (fun σ y => (hv σ y).const_mul _) (isConj_mul hc _)) :=
  icls_eq_iff.1 (by
    rw [← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_fnB_mul hv hc, icls_zp, icls_comb,
      Fin.sum_univ_two, add_comm]
    rfl)

theorem mixed_eq (H : ArCalc) (hX : IsArithVar p D) {v : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hv : ∀ σ y, CInfAt (v σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (v σ)).IsConj (Weight.ofFun (v σ'))) (N : HermLB p)
    {Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ} (hΘ : IsArFun ![fnB v hv hc, N] D Θ) (n : Fin 2 → ℤ) :
    Θ (MvPolynomial.X 0 * lin (fun i => (n i : ℝ)) ^ D) = 1 / 2 * chInt (comb ![fnB v hv hc, N] n) D v := by
  let A : Option (Fin 2) → Fin 2 → ℤ := fun j => Pi.single (j.elim 0 id) 1
  have h := ((H.arIso k X p D hX).2 _ _ Θ hΘ).2.2 (Option (Fin 2))
    (fun o => o.elim (fnB v hv hc) ![fnB v hv hc, N]) A (by
      rintro (_ | i)
      · exact isometric_comb_single _ 0
      · exact isometric_comb_single _ i)
  have e (j : Option (Fin 2)) : (lin fun i => (A j i : ℝ)) = MvPolynomial.X (j.elim 0 id) := lin_single _
  rw [← H.arChange k X p D hX _ _ v hv hc _ h n, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  congr 1
  rw [map_mul, map_pow, aeval_X, aeval_rename]
  simp only [Function.comp_def, e, Option.elim_none, Option.elim_some, id, aeval_X_left_apply]

theorem tendsto_selfInter : ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → GenSmooth p D → ∀ t : ℝ → ℝ, Tendsto t atTop (𝓝 0) → ∀ (L : ℝ → HermLB p) (L₀ : HermLB p),
    LFam t L L₀ → ∀ (a : ℝ → ℝ) (a₀ : ℝ), (∀ R, (L R).IsSelfInter (a R)) → L₀.IsSelfInter a₀ →
    Tendsto a atTop (𝓝 a₀) := by
  intro H k _ X _ p D hX hs t ht L L₀ ⟨u, hu, hc, hL, hf⟩ a a₀ ha ha₀
  choose Θ hΘ using fun R => ((H.arExists k X p D hX).2 _ ![fnB (u R) (hu R) (hc R), L₀]).1
  obtain ⟨Q, hQ⟩ := sub_dvd_pow_sub_pow (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ)
    (MvPolynomial.X 1) (D + 1)
  rw [add_sub_cancel_right] at hQ
  have key := tendsto_zero_of_pow (l := atTop) D (fun R => Θ R ∘ₗ LinearMap.mulLeft ℝ (MvPolynomial.X 0)) (fun n => by
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, fun R => mixed_eq H hX (hu R) (hc R) L₀ (hΘ R) n,
      fun R => (isometric_comb_raise (hu R) (hc R) L₀ n).chInt_eq]
    simpa only [mul_zero] using (tendsto_chInt hX hs ht hu hc hf (zp L₀ (n 1)) (n 0)).const_mul (1 / 2))
    (fun P e he hP R => (hΘ R).2 _ (1 + e) (by omega) ((isHomogeneous_X ℝ 0).mul hP)) Q
  have e₀ (R) : a₀ = Θ R (MvPolynomial.X 1 ^ (D + 1)) := ha₀.unique hX (((H.arIso k X p D hX).2 _ _ _ (hΘ R)).1 1)
  have e₁ (R) : a R = Θ R ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ (D + 1)) := by
    have i : (comb ![fnB (u R) (hu R) (hc R), L₀] fun _ => 1).Isometric (L R) := icls_eq_iff.1 (by
      rw [← icls_eq_iff.2 (hL R), ← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_comb, Fin.sum_univ_two,
        one_smul, one_smul, add_comm]
      rfl)
    have := (ha R).unique hX (i.isSelfInter hX ((hΘ R).1 _))
    simpa [lin] using this
  rw [← tendsto_sub_nhds_zero_iff]
  refine key.congr fun R => ?_
  rw [e₁ R, e₀ R, ← map_sub, hQ]
  rfl

end GlobalTheory.SelfCont

end
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.SelfPoly

open MvPolynomial

theorem eval_pow_expand (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    Θ ((C t * X 0 + X 1) ^ (D + 1)) = ∑ i ∈ Finset.range (D + 2),
      t ^ i * ((D + 1).choose i * Θ (X 0 ^ i * X 1 ^ (D + 1 - i))) := by
  rw [add_pow, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (C t * X 0) ^ i * X 1 ^ (D + 1 - i) * ((D + 1).choose i : MvPolynomial (Fin 2) ℝ)
      = C (t ^ i * (D + 1).choose i) * (X 0 ^ i * X 1 ^ (D + 1 - i)) := by
    rw [C_mul, C_pow, map_natCast]; ring
  rw [this, C_mul', LinearMap.map_smul, smul_eq_mul]; ring

theorem eval_mul_pow_expand (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    Θ (X 0 * (C t * X 0 + X 1) ^ D) = ∑ j ∈ Finset.range (D + 1),
      t ^ j * (D.choose j * Θ (X 0 ^ (j + 1) * X 1 ^ (D - j))) := by
  rw [add_pow, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : X 0 * ((C t * X 0) ^ j * X 1 ^ (D - j) * (D.choose j : MvPolynomial (Fin 2) ℝ))
      = C (t ^ j * D.choose j) * (X 0 ^ (j + 1) * X 1 ^ (D - j)) := by
    rw [C_mul, C_pow, map_natCast]; ring
  rw [this, C_mul', LinearMap.map_smul, smul_eq_mul]; ring

def poly (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (D + 2),
    Polynomial.C ((D + 1).choose i * Θ (X 0 ^ i * X 1 ^ (D + 1 - i))) * Polynomial.X ^ i

theorem poly_eval (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    (poly Θ D).eval t = Θ ((C t * X 0 + X 1) ^ (D + 1)) := by
  rw [eval_pow_expand, poly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

theorem poly_derivative_eval (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    (poly Θ D).derivative.eval t = ((D : ℝ) + 1) * Θ (X 0 * (C t * X 0 + X 1) ^ D) := by
  rw [eval_mul_pow_expand, poly, map_sum, Polynomial.eval_finsetSum, Finset.sum_range_succ', Finset.mul_sum]
  simp only [Polynomial.derivative_C_mul_X_pow, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Nat.cast_zero, mul_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e₁ : D + 1 - (j + 1) = D - j := Nat.add_sub_add_right D 1 j
  have e₂ : (((D + 1).choose (j + 1) : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) = ((D : ℝ) + 1) * (D.choose j : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq D j).symm
  rw [e₁, Nat.add_sub_cancel]
  calc ((D + 1).choose (j + 1) : ℝ) * Θ (X 0 ^ (j + 1) * X 1 ^ (D - j)) * ((j + 1 : ℕ) : ℝ) * t ^ j
      = (((D + 1).choose (j + 1) : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) * (t ^ j * Θ (X 0 ^ (j + 1) * X 1 ^ (D - j))) := by ring
    _ = _ := by rw [e₂]; ring

end GlobalTheory.HSAmp.SelfPoly

namespace GlobalTheory.HSAmp.SelfPoly

open MvPolynomial HermLB

theorem selfInter_poly : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (u : SmFn p) (a a' : ℝ), L.IsSelfInter a → (up L u).IsSelfInter a' →
    ∃ s : Polynomial ℝ, s.eval 0 = a ∧ s.eval 1 = a' ∧
      ∀ t : ℚ, ((D : ℝ) + 1) / 2 * chInt (up L (u.smul t)) D u.u = s.derivative.eval (t : ℝ) := by
  intro H k _ X _ p D hX L u a a' ha ha'
  obtain ⟨Θ, hΘ⟩ := ((H.arExists k X p D hX).2 _ ![fnB u.u u.cInf u.conj, L]).1
  refine ⟨poly Θ D, ?_, ?_, fun t => ?_⟩
  · rw [poly_eval, map_zero, zero_mul, zero_add]
    exact (ha.unique hX (((H.arIso k X p D hX).2 _ _ _ hΘ).1 1)).symm
  · rw [poly_eval, map_one, one_mul]
    have i : (comb ![fnB u.u u.cInf u.conj, L] fun _ => 1).Isometric (up L u) := icls_eq_iff.1 (by
      show _ = (L.raise u.u u.cInf u.conj).icls
      rw [← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_comb, Fin.sum_univ_two,
        one_smul, one_smul, add_comm]
      rfl)
    rw [ha'.unique hX (i.isSelfInter hX (hΘ.1 _))]
    simp [lin, Fin.sum_univ_two]
  · rw [poly_derivative_eval]
    have hd : (t.den : ℝ) ≠ 0 := Nat.cast_ne_zero.2 t.den_nz
    have hq : (t.den : ℝ) * (t : ℝ) = t.num := by
      rw [Rat.cast_def]; field_simp
    let n : Fin 2 → ℤ := ![t.num, t.den]
    have h₁ := GlobalTheory.SelfCont.mixed_eq H hX u.cInf u.conj L hΘ n
    have h₂ := (GlobalTheory.SelfCont.isometric_comb_raise u.cInf u.conj L n).chInt_eq D u.u
    have h₃ : ((zp L (n 1)).raise (fun σ y => (n 0 : ℝ) * u.u σ y) (fun σ y => (u.cInf σ y).const_mul _)
        (GlobalTheory.SelfCont.isConj_mul u.conj _)).Isometric ((up L (u.smul t)).pow t.den) := icls_eq_iff.1 (by
      rw [← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_pow]
      show _ = t.den • ((L.raise (u.smul t).u (u.smul t).cInf (u.smul t).conj).icls)
      rw [← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_zp, smul_add, ← natCast_zsmul,
        ← natCast_zsmul, ← GlobalTheory.SelfCont.icls_fnB_mul (u.smul t).cInf (u.smul t).conj]
      congr 1
      refine icls_eq_iff.2 (isometric_of_eqOn fun σ _ y _ => ?_)
      show (t.den : ℤ) * ((t : ℝ) * u.u σ y) = (t.num : ℝ) * u.u σ y
      rw [← hq]; push_cast; ring)
    have h₄ := GlobalTheory.T.chernFormPowerIntegral_hermLineBundle_pow k X p D hX (up L (u.smul t)) t.den u.u
    have h₅ : (lin fun i => (n i : ℝ)) = C (t.den : ℝ) * (C (t : ℝ) * MvPolynomial.X 0 + MvPolynomial.X 1) := by
      simp only [lin, Fin.sum_univ_two, n, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [mul_add, ← mul_assoc, ← C_mul, hq]; push_cast; ring
    have h₆ : Θ (MvPolynomial.X 0 * (lin fun i => (n i : ℝ)) ^ D) = (t.den : ℝ) ^ D * Θ (MvPolynomial.X 0 * (C (t : ℝ) * MvPolynomial.X 0 + MvPolynomial.X 1) ^ D) := by
      rw [h₅, mul_pow, ← C_pow, mul_left_comm, C_mul', LinearMap.map_smul, smul_eq_mul]
    have key : (t.den : ℝ) ^ D * chInt (up L (u.smul t)) D u.u =
        (t.den : ℝ) ^ D * (2 * Θ (MvPolynomial.X 0 * (C (t : ℝ) * MvPolynomial.X 0 + MvPolynomial.X 1) ^ D)) := by
      rw [← h₄, ← h₃.chInt_eq, ← h₂]
      linarith
    have := mul_left_cancel₀ (pow_ne_zero D hd) key
    rw [this]; ring

end GlobalTheory.HSAmp.SelfPoly
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_intersection_metric_segment_polynomial : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (u : SmFn p) (a a' : ℝ), L.IsSelfInter a → (up L u).IsSelfInter a' → ∃ s : Polynomial ℝ, s.eval 0 = a ∧ s.eval 1 = a' ∧ ∀ t : ℚ, ((D : ℝ) + 1) / 2 * chInt (up L (u.smul t)) D u.u = s.derivative.eval (t : ℝ) := by
  atlas_forward_decl GlobalTheory.HSAmp.SelfPoly.selfInter_poly
end

section
section
open Filter Topology

namespace GlobalTheory

theorem polynomial_increment_near_derivative (s : Polynomial ℝ) {η δ : ℝ}
    (hδ : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, dist x y < δ →
      dist (s.derivative.eval x) (s.derivative.eval y) < η)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hba : b - a < δ) :
    (b - a) * s.derivative.eval a ≤ s.eval b - s.eval a + η * (b - a) ∧
    s.eval b - s.eval a ≤ (b - a) * s.derivative.eval b + η * (b - a) := by
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope (fun x => s.eval x) hab
    s.continuous.continuousOn (fun x _ => s.differentiableAt.differentiableWithinAt)
  rw [Polynomial.deriv] at hcd
  have hpos : 0 < b - a := sub_pos.mpr hab
  have hsc : s.eval b - s.eval a = (b - a) * s.derivative.eval c := by
    rw [hcd]; field_simp
  have h1 := hδ c ⟨by linarith [hc.1], by linarith [hc.2]⟩ a ⟨ha, by linarith⟩
    (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hc.1, hc.2])
  have h2 := hδ c ⟨by linarith [hc.1], by linarith [hc.2]⟩ b ⟨by linarith, hb⟩
    (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hc.1, hc.2])
  rw [Real.dist_eq, abs_lt] at h1 h2
  constructor
  · rw [hsc]; nlinarith [mul_lt_mul_of_pos_left h1.1 hpos]
  · rw [hsc]; nlinarith [mul_lt_mul_of_pos_left h2.2 hpos]

theorem riemann_sum_of_one_sided_increments : ∀ (s : Polynomial ℝ) (ℓ : ℚ → ℕ → ℝ),
    (∀ t t' : ℚ, 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m : ℕ in atTop, ℓ t m - ℓ t' m ≤ ((t' : ℝ) - t) * s.derivative.eval (t : ℝ) + ε) →
    Tendsto (fun m => ℓ 0 m - ℓ 1 m) atTop (𝓝 (s.eval 1 - s.eval 0)) := by
  intro s ℓ h
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε / 4 := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; positivity
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous s.derivative.continuous.continuousOn) η hηpos
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  have hnpos : (0:ℝ) < n := lt_trans (by positivity) hn
  have hn0 : n ≠ 0 := by exact_mod_cast hnpos.ne'
  have hstep : (1:ℝ) / n < δ := by
    rw [div_lt_iff₀ hnpos]; rw [div_lt_iff₀ hδpos] at hn; linarith
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℚ, t = fun j : ℕ => (j : ℚ) / n := ⟨_, rfl⟩
  have ht0 : ∀ j, 0 ≤ t j := fun j => by rw [ht]; positivity
  have ht1 : ∀ j ≤ n, t j ≤ 1 := fun j hj => by
    rw [ht]; show (j:ℚ) / n ≤ 1
    rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn0)]; exact_mod_cast hj
  have htR : ∀ j, ((t j : ℚ) : ℝ) = (j : ℝ) / n := fun j => by rw [ht]; push_cast; ring
  have hdiff : ∀ j, ((t (j+1) : ℚ) : ℝ) - t j = 1 / n := fun j => by
    rw [htR, htR]; push_cast; ring
  have hηn : η * (1 / (n:ℝ)) = η / n := by ring
  have hup : ∀ᶠ m in atTop, ∀ j ∈ Finset.range n, ℓ (t j) m - ℓ (t (j+1)) m ≤
      (((t (j+1)) : ℝ) - t j) * s.derivative.eval (t j : ℝ) + η / n := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact h _ _ (ht0 j) (ht1 j hj'.le) (ht0 (j+1)) (ht1 (j+1) hj') _ (by positivity)
  have hlo : ∀ᶠ m in atTop, ∀ j ∈ Finset.range n, ℓ (t (j+1)) m - ℓ (t j) m ≤
      (((t j) : ℝ) - t (j+1)) * s.derivative.eval (t (j+1) : ℝ) + η / n := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact h _ _ (ht0 (j+1)) (ht1 (j+1) hj') (ht0 j) (ht1 j hj'.le) _ (by positivity)
  filter_upwards [hup, hlo] with m hu hl
  have t0 : t 0 = 0 := by rw [ht]; simp
  have tn : t n = 1 := by
    rw [ht]; show (n:ℚ) / n = 1; exact div_self (by exact_mod_cast hn0)
  have hsumℓ : ℓ 0 m - ℓ 1 m = ∑ j ∈ Finset.range n, (ℓ (t j) m - ℓ (t (j+1)) m) := by
    have := Finset.sum_range_sub' (fun j => ℓ (t j) m) n
    rw [this, t0, tn]
  have hsums : s.eval 1 - s.eval 0 =
      ∑ j ∈ Finset.range n, (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ)) := by
    have := Finset.sum_range_sub (fun j => s.eval (t j : ℝ)) n
    rw [this, t0, tn]; simp
  have hstepb : ∀ j ∈ Finset.range n,
      |(ℓ (t j) m - ℓ (t (j+1)) m) - (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ))| ≤ 2 * (η / n) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hd := hdiff j
    have h1n : (0:ℝ) < 1 / n := by positivity
    obtain ⟨k1, k2⟩ := polynomial_increment_near_derivative s hδ (a := t j) (b := t (j+1))
      (by exact_mod_cast ht0 j) (by linarith) (by exact_mod_cast ht1 _ hj') (by rw [hd]; exact hstep)
    have u := hu j hj
    have l := hl j hj
    have hd' : ((t j : ℚ) : ℝ) - t (j+1) = -(1 / n) := by linarith
    rw [hd] at k1 k2 u
    rw [hd'] at l
    rw [hηn] at k1 k2
    rw [abs_le]; constructor
    · nlinarith
    · nlinarith
  rw [Real.dist_eq, hsumℓ, hsums, ← Finset.sum_sub_distrib]
  calc |∑ j ∈ Finset.range n, ((ℓ (t j) m - ℓ (t (j+1)) m) - (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ)))|
      ≤ ∑ j ∈ Finset.range n, |(ℓ (t j) m - ℓ (t (j+1)) m) - (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, 2 * (η / n) := Finset.sum_le_sum hstepb
    _ = 2 * η := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    _ < ε := by rw [hη]; linarith

end GlobalTheory
end

open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_sub_of_one_sided_increment_bound_derivative : ∀ (s : Polynomial ℝ) (ℓ : ℚ → ℕ → ℝ), (∀ t t' : ℚ, 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ℓ t m - ℓ t' m ≤ ((t' : ℝ) - t) * s.derivative.eval (t : ℝ) + ε) → Tendsto (fun m => ℓ 0 m - ℓ 1 m) atTop (𝓝 (s.eval 1 - s.eval 0)) := by
  atlas_forward_decl GlobalTheory.riemann_sum_of_one_sided_increments
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem semiPos_up_smul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ) (L : HermLB p) (u : SmFn p)
    (t : ℝ), 0 ≤ t → t ≤ 1 → L.SemiPos D → (up L u).SemiPos D → (up L (u.smul t)).SemiPos D := by
  intro k _ X p D L u t h0 h1 hL hLu σ i c y hy ξ
  set f : ReciprocityTheory.L2DbarEstimates.V D → ℝ := fun v => (L.φ σ).φ i (c.e.symm v) with hfdef
  set g : ReciprocityTheory.L2DbarEstimates.V D → ℝ := fun v => u.u σ (c.e.symm v) with hgdef
  have hf : ContDiffAt ℝ 2 f (c.e y) := (L.cInf σ).contDiffAt c hy.1 hy.2
  have hfg : ContDiffAt ℝ 2 (fun v => f v + g v) (c.e y) := ((up L u).cInf σ).contDiffAt c hy.1 hy.2
  have a : 0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => (f v : ℂ)) (c.e y) ξ).re := hL σ i c y hy ξ
  have b : 0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => ((f v + g v : ℝ) : ℂ)) (c.e y) ξ).re := hLu σ i c y hy ξ
  have e : (fun v => (((up L (u.smul t)).φ σ).φ i (c.e.symm v) : ℂ)) =
      fun v => ((((1 - t) * f v + 0) + (t * (f v + g v) + 0) : ℝ) : ℂ) := by
    funext v
    show ((((L.φ σ).φ i (c.e.symm v) + t * u.u σ (c.e.symm v)) : ℝ) : ℂ) = _
    congr 1
    simp only [hfdef, hgdef]
    ring
  rw [e, ReciprocityTheory.L2DbarEstimates.Y.flA_leviV_add, ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul hf,
    ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul (f := fun v => f v + g v) hfg]
  · rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have : 0 ≤ 1 - t := by linarith
    positivity
  · exact (hf.const_smul (1 - t)).add contDiffAt_const
  · exact (hfg.const_smul t).add contDiffAt_const

end GlobalTheory.HSAmp
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiPos_raiseWeight_segment_smul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ) (L : HermLB p) (u : SmFn p) (t : ℝ), 0 ≤ t → t ≤ 1 → L.SemiPos D → (up L u).SemiPos D → (up L (u.smul t)).SemiPos D := by
  atlas_forward_decl GlobalTheory.HSAmp.semiPos_up_smul
end

section
section
set_option autoImplicit false

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.GramJensen

variable {S : Type} {Y : S → Type} [∀ σ, MeasurableSpace (Y σ)] {ι : Type} [Fintype ι] [DecidableEq ι]

def twist (v : ∀ σ, Y σ → ι → ℂ) (w : ∀ σ, Y σ → ℝ) : ∀ σ, Y σ → ι → ℂ :=
  fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)

def col (T : Matrix ι ι ℂ) (a : ι) : ι → ℂ := fun i => star (T i a)

theorem exp_half_sq (t : ℝ) : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
  rw [sq, ← Real.exp_add]; ring_nf

theorem cmb_twist (v : ∀ σ, Y σ → ι → ℂ) (w : ∀ σ, Y σ → ℝ) (c : ι → ℂ) (σ : S) (y : Y σ) :
    cmb (twist v w) c σ y = cmb v c σ y * Real.exp (-(w σ y)) := by
  have h : ∑ i, c i * twist v w σ y i = (∑ i, c i * v σ y i) * (Real.exp (-(w σ y) / 2) : ℝ) := by
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_; simp only [twist]; ring
  rw [cmb, cmb, h, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, exp_half_sq]

theorem cmb_nonneg (v : ∀ σ, Y σ → ι → ℂ) (c : ι → ℂ) (σ : S) (y : Y σ) : 0 ≤ cmb v c σ y := by
  unfold cmb; positivity

theorem exp_neg_le {C t : ℝ} (h : |t| ≤ C) : Real.exp (-t) ≤ Real.exp C :=
  Real.exp_le_exp.2 (by linarith [neg_le_abs t])

theorem exp_neg_ge {C t : ℝ} (h : |t| ≤ C) : Real.exp (-C) ≤ Real.exp (-t) :=
  Real.exp_le_exp.2 (by linarith [le_abs_self t])

variable {μ : ∀ σ, Measure (Y σ)} {v : ∀ σ, Y σ → ι → ℂ} {w : ∀ σ, Y σ → ℝ} {C : ℝ}

theorem isFam_twist (h : IsFam μ v) (hw : ∀ σ, Measurable (w σ)) (hC : ∀ σ y, |w σ y| ≤ C) :
    IsFam μ (twist v w) := by
  refine ⟨h.finite, fun σ i j => ?_⟩
  have e : (fun y => twist v w σ y i * (starRingEnd ℂ) (twist v w σ y j)) =
      fun y => ((Real.exp (-(w σ y)) : ℝ) : ℂ) * (v σ y i * (starRingEnd ℂ) (v σ y j)) := by
    funext y
    simp only [twist, map_mul, Complex.conj_ofReal]
    rw [← exp_half_sq]; push_cast; ring
  rw [e]
  refine (h.integrable σ i j).bdd_mul (c := Real.exp C) ?_ ?_
  · exact (Complex.measurable_ofReal.comp (Real.measurable_exp.comp (hw σ).neg)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact exp_neg_le (hC σ y)

theorem l2_twist_eq_finsum_integral_mul_exp_neg (c : ι → ℂ) :
    l2 μ (twist v w) c = ∑ᶠ σ, ∫ y, cmb v c σ y * Real.exp (-(w σ y)) ∂μ σ := by
  simp only [l2, cmb_twist]

theorem quad (M T : Matrix ι ι ℂ) (a : ι) :
    ∑ i, ∑ j, col T a i * (starRingEnd ℂ) (col T a j) * M i j = (Tᴴ * M * T) a a := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, col]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.star_def, Complex.conj_conj]; ring

theorem quad_vec (M : Matrix ι ι ℂ) (x : ι → ℂ) :
    star x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, star x i * (starRingEnd ℂ) (star x j) * M i j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def, Complex.conj_conj]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring

theorem exp_neg_bound_mul_l2_le_l2_twist (h : IsFam μ v) (hw : ∀ σ, Measurable (w σ)) (hC : ∀ σ y, |w σ y| ≤ C) (c : ι → ℂ) :
    Real.exp (-C) * l2 μ v c ≤ l2 μ (twist v w) c := by
  have hS := h.finite
  haveI := Fintype.ofFinite S
  obtain ⟨-, hc⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ v h
  rw [l2_twist_eq_finsum_integral_mul_exp_neg]
  simp only [l2, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_le_sum fun σ _ => ?_
  rw [← integral_const_mul]
  refine integral_mono (((hc c).1 σ).const_mul _) ?_ fun y => ?_
  · exact ((hc c).1 σ).mul_bdd (c := Real.exp C) (Real.measurable_exp.comp (hw σ).neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact exp_neg_le (hC σ y))
  · have h0 := cmb_nonneg v c σ y
    have h1 := exp_neg_ge (hC σ y)
    simp only
    nlinarith

theorem posDef_twist (h : IsFam μ v) (hG : (gram μ v).PosDef) (hw : ∀ σ, Measurable (w σ))
    (hC : ∀ σ y, |w σ y| ≤ C) : (gram μ (twist v w)).PosDef := by
  refine GlobalTheory.T.gram_posDef_of_l2_definite S Y ι μ _ (isFam_twist h hw hC) fun c hc0 => ?_
  by_contra hne
  have hx : star c ≠ 0 := fun h' => hne (by simpa using congrArg star h')
  have hpos := hG.dotProduct_mulVec_pos hx
  obtain ⟨-, hl⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ v h
  rw [quad_vec, star_star, ← (hl c).2.2] at hpos
  have hp : 0 < l2 μ v c := by exact_mod_cast hpos
  have := exp_neg_bound_mul_l2_le_l2_twist h hw hC c
  rw [hc0] at this
  nlinarith [Real.exp_pos (-C)]

theorem jensen (hS : Finite S) (f : ∀ σ, Y σ → ℝ) (hf0 : ∀ σ y, 0 ≤ f σ y)
    (hfi : ∀ σ, Integrable (f σ) (μ σ)) (hf1 : ∑ᶠ σ, ∫ y, f σ y ∂μ σ = 1) (hw : ∀ σ, Measurable (w σ))
    (hC : ∀ σ y, |w σ y| ≤ C) :
    Real.exp (-(∑ᶠ σ, ∫ y, w σ y * f σ y ∂μ σ)) ≤ ∑ᶠ σ, ∫ y, f σ y * Real.exp (-(w σ y)) ∂μ σ := by
  haveI := Fintype.ofFinite S
  simp only [finsum_eq_sum_of_fintype] at hf1 ⊢
  obtain ⟨m, hm⟩ : ∃ m, m = ∑ σ, ∫ y, w σ y * f σ y ∂μ σ := ⟨_, rfl⟩
  rw [← hm]
  have hwi : ∀ σ, Integrable (fun y => w σ y * f σ y) (μ σ) := fun σ =>
    (hfi σ).bdd_mul (c := C) (hw σ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC σ y)
  have hei : ∀ σ, Integrable (fun y => f σ y * Real.exp (-(w σ y))) (μ σ) := fun σ =>
    (hfi σ).mul_bdd (c := Real.exp C) (Real.measurable_exp.comp (hw σ).neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact exp_neg_le (hC σ y))
  have pt : ∀ σ y, Real.exp (-m) * (f σ y * (1 + m) - w σ y * f σ y) ≤ f σ y * Real.exp (-(w σ y)) := by
    intro σ y
    have h1 := Real.add_one_le_exp (m - w σ y)
    have h2 : Real.exp (-m) * Real.exp (m - w σ y) = Real.exp (-(w σ y)) := by rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-m) * (m - w σ y + 1) ≤ Real.exp (-(w σ y)) := by
      rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    have h4 := mul_le_mul_of_nonneg_left h3 (hf0 σ y)
    nlinarith
  have e : ∀ σ, ∫ y, Real.exp (-m) * (f σ y * (1 + m) - w σ y * f σ y) ∂μ σ =
      Real.exp (-m) * ((1 + m) * ∫ y, f σ y ∂μ σ - ∫ y, w σ y * f σ y ∂μ σ) := by
    intro σ
    rw [integral_const_mul, integral_sub ((hfi σ).mul_const _) (hwi σ), integral_mul_const]; ring
  calc Real.exp (-m) = Real.exp (-m) * ((1 + m) * ∑ σ, ∫ y, f σ y ∂μ σ - ∑ σ, ∫ y, w σ y * f σ y ∂μ σ) := by
        rw [hf1, ← hm]; ring
    _ = ∑ σ, ∫ y, Real.exp (-m) * (f σ y * (1 + m) - w σ y * f σ y) ∂μ σ := by
        rw [Finset.sum_congr rfl fun σ _ => e σ, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ ≤ ∑ σ, ∫ y, f σ y * Real.exp (-(w σ y)) ∂μ σ :=
        Finset.sum_le_sum fun σ _ => integral_mono ((((hfi σ).mul_const _).sub (hwi σ)).const_mul _) (hei σ) (pt σ)

theorem berg_sum (T : Matrix ι ι ℂ) (hT : Tᴴ * gram μ v * T = 1) (σ : S) (y : Y σ) :
    ∑ a, cmb v (col T a) σ y = bergmanDensity μ v σ y := by
  have hinv : (gram μ v)⁻¹ = T * Tᴴ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.mul_assoc]
    exact mul_eq_one_comm.1 hT
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have key : ((∑ a, cmb v (col T a) σ y : ℝ) : ℂ) =
      ∑ i, ∑ j, (gram μ v)⁻¹ j i * (v σ y i * (starRingEnd ℂ) (v σ y j)) := by
    have ha : ∀ a, ((cmb v (col T a) σ y : ℝ) : ℂ) =
        ∑ i, ∑ j, T j a * star (T i a) * (v σ y i * (starRingEnd ℂ) (v σ y j)) := by
      intro a
      rw [cmb, hn, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [col, map_mul, Complex.star_def, Complex.conj_conj]; ring
    rw [hinv, Complex.ofReal_sum]
    simp only [ha, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  rw [bergmanDensity, ← key, Complex.ofReal_re]

theorem jensen_gram (h : IsFam μ v) (hG : (gram μ v).PosDef) (hw : ∀ σ, Measurable (w σ))
    (hC : ∀ σ y, |w σ y| ≤ C) :
    IsFam μ (twist v w) ∧ (gram μ (twist v w)).PosDef ∧
      Real.log (gram μ v).det.re - ∑ᶠ σ, ∫ y, w σ y * bergmanDensity μ v σ y ∂μ σ ≤
        Real.log (gram μ (twist v w)).det.re := by
  have hF := isFam_twist h hw hC
  have hG' := posDef_twist h hG hw hC
  refine ⟨hF, hG', ?_⟩
  have hS := h.finite
  haveI := Fintype.ofFinite S
  obtain ⟨T, d, -, hT, hT'⟩ := GlobalTheory.T.exists_simultaneous_diagonalisation_posDef_hermitian ι _ _ hG hG'.1
  obtain ⟨-, hl⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ v h
  obtain ⟨-, hl'⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ _ hF
  have hl1 : ∀ a, l2 μ v (col T a) = 1 := fun a => by
    have := (hl (col T a)).2.2
    rw [quad, hT, Matrix.one_apply_eq] at this; exact_mod_cast this
  have hld : ∀ a, l2 μ (twist v w) (col T a) = d a := fun a => by
    have := (hl' (col T a)).2.2
    rw [quad, hT', Matrix.diagonal_apply_eq] at this; exact_mod_cast this
  have hj : ∀ a, Real.exp (-(∑ᶠ σ, ∫ y, w σ y * cmb v (col T a) σ y ∂μ σ)) ≤ d a := fun a => by
    rw [← hld a, l2_twist_eq_finsum_integral_mul_exp_neg]
    exact jensen hS (cmb v (col T a)) (cmb_nonneg v _) (hl (col T a)).1 (hl1 a) hw hC
  have hd : ∀ a, 0 < d a := fun a => (Real.exp_pos _).trans_le (hj a)
  have hdet : (gram μ (twist v w)).det = (gram μ v).det * ∏ a, (d a : ℂ) := by
    have e1 := congrArg Matrix.det hT
    have e2 := congrArg Matrix.det hT'
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at e1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at e2
    linear_combination (gram μ v).det * e2 - (gram μ (twist v w)).det * e1
  have hpos := Complex.pos_iff.1 (Matrix.PosDef.det_pos hG)
  have hre : (gram μ (twist v w)).det.re = (gram μ v).det.re * ∏ a, d a := by
    rw [hdet, ← Complex.ofReal_prod, Complex.re_mul_ofReal]
  rw [hre, Real.log_mul hpos.1.ne' (Finset.prod_pos fun a _ => hd a).ne', Real.log_prod fun a _ => (hd a).ne']
  have hsum : ∑ᶠ σ, ∫ y, w σ y * bergmanDensity μ v σ y ∂μ σ = ∑ a, ∑ᶠ σ, ∫ y, w σ y * cmb v (col T a) σ y ∂μ σ := by
    simp only [finsum_eq_sum_of_fintype]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← integral_finsetSum Finset.univ fun a _ => ((hl (col T a)).1 σ).bdd_mul (c := C)
      (hw σ).aestronglyMeasurable (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC σ y)]
    congr 1; funext y; rw [← Finset.mul_sum, berg_sum T hT]
  have hlog : ∀ a, -(∑ᶠ σ, ∫ y, w σ y * cmb v (col T a) σ y ∂μ σ) ≤ Real.log (d a) := fun a => by
    have := Real.log_le_log (Real.exp_pos _) (hj a); rwa [Real.log_exp] at this
  rw [hsum]
  have := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hlog a
  rw [Finset.sum_neg_distrib] at this
  linarith

theorem gram_det_jensen : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).PosDef → ∀ (w : ∀ σ, Y σ → ℝ) (C : ℝ), (∀ σ, Measurable (w σ)) → (∀ σ y, |w σ y| ≤ C) → IsFam μ (fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)) ∧ (gram μ fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)).PosDef ∧ Real.log (gram μ v).det.re - ∑ᶠ σ, ∫ y, w σ y * bergmanDensity μ v σ y ∂μ σ ≤ Real.log (gram μ fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)).det.re := by
  intro S Y _ ι _ _ μ v h hG w C hw hC
  exact jensen_gram h hG hw hC

end GlobalTheory.GramJensen
end
end

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramDeterminant_jensen_change_of_weight : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).PosDef → ∀ (w : ∀ σ, Y σ → ℝ) (C : ℝ), (∀ σ, Measurable (w σ)) → (∀ σ y, |w σ y| ≤ C) → IsFam μ (fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)) ∧ (gram μ fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)).PosDef ∧ Real.log (gram μ v).det.re - ∑ᶠ σ, ∫ y, w σ y * bergmanDensity μ v σ y ∂μ σ ≤ Real.log (gram μ fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)).det.re := by
  atlas_forward_decl GlobalTheory.GramJensen.gram_det_jensen
end

section
section
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp.BergProof

lemma sum_eq_dot {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) (w : ι → ℂ) :
    ∑ i, ∑ j, H j i * (w i * (starRingEnd ℂ) (w j)) = star w ⬝ᵥ (H *ᵥ w) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring)

lemma berg_eq {S : Type} {Y : S → Type} [∀ σ, MeasurableSpace (Y σ)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ) (σ : S) (y : Y σ) :
    bergmanDensity μ v σ y = (star (v σ y) ⬝ᵥ ((gram μ v)⁻¹ *ᵥ v σ y)).re := by
  rw [bergmanDensity, sum_eq_dot]

lemma ofReal_re_of_nonneg {z : ℂ} (h : 0 ≤ z) : ((z.re : ℝ) : ℂ) = z := by
  have h' := Complex.le_def.mp h
  apply Complex.ext <;> simp [h'.2.symm]

end GlobalTheory.HSAmp.BergProof

open GlobalTheory.HSAmp.BergProof in

theorem GlobalTheory.HSAmp.berg_mass_extremal : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).PosDef → (∀ σ, Integrable (bergmanDensity μ v σ) (μ σ)) ∧ ∑ᶠ σ, ∫ y, bergmanDensity μ v σ y ∂μ σ = Fintype.card ι ∧ (∀ σ y, 0 ≤ bergmanDensity μ v σ y) ∧ ∀ σ y (M : ℝ), 0 ≤ M → (∀ c : ι → ℂ, cmb v c σ y ≤ M * l2 μ v c) → bergmanDensity μ v σ y ≤ M := by
  intro S Y _ ι _ _ μ v hF hG
  obtain ⟨hHerm, hl2⟩ := GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form S Y ι μ v hF
  have hH : ((gram μ v)⁻¹).PosDef := hG.inv
  have hu : IsUnit (gram μ v).det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  have hGH : gram μ v * (gram μ v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hHG : (gram μ v)⁻¹ * gram μ v = 1 := Matrix.nonsing_inv_mul _ hu
  have hHh : ((gram μ v)⁻¹).IsHermitian := hH.isHermitian
  have hnn : ∀ σ y, 0 ≤ star (v σ y) ⬝ᵥ ((gram μ v)⁻¹ *ᵥ v σ y) := fun σ y =>
    hH.posSemidef.dotProduct_mulVec_nonneg _
  have key : ∀ σ y, (bergmanDensity μ v σ y : ℂ) = star (v σ y) ⬝ᵥ ((gram μ v)⁻¹ *ᵥ v σ y) := fun σ y => by
    rw [berg_eq]; exact ofReal_re_of_nonneg (hnn σ y)
  have hpos : ∀ σ y, 0 ≤ bergmanDensity μ v σ y := fun σ y => by
    rw [berg_eq]; exact (Complex.le_def.mp (hnn σ y)).1
  have hint : ∀ σ, Integrable (fun y => ∑ i, ∑ j, (gram μ v)⁻¹ j i * (v σ y i * (starRingEnd ℂ) (v σ y j))) (μ σ) :=
    fun σ => integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hF.integrable σ i j).const_mul _
  refine ⟨fun σ => (hint σ).re, ?_, hpos, ?_⟩
  · haveI : Finite S := hF.finite
    haveI := Fintype.ofFinite S
    have hσ : ∀ σ, ∫ y, bergmanDensity μ v σ y ∂μ σ =
        (∑ i, ∑ j, (gram μ v)⁻¹ j i * ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ).re := fun σ => by
      have e1 : ∫ y, bergmanDensity μ v σ y ∂μ σ =
          RCLike.re (∫ y, ∑ i, ∑ j, (gram μ v)⁻¹ j i * (v σ y i * (starRingEnd ℂ) (v σ y j)) ∂μ σ) :=
        integral_re (hint σ)
      rw [e1, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hF.integrable σ i j).const_mul _]
      change Complex.re _ = Complex.re _
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => (hF.integrable σ i j).const_mul _]
      exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
    have hsum : ∑ i, ∑ j, (gram μ v)⁻¹ j i * gram μ v i j = (Fintype.card ι : ℂ) := by
      rw [Finset.sum_comm]
      have : ∀ j, ∑ i, (gram μ v)⁻¹ j i * gram μ v i j = ((gram μ v)⁻¹ * gram μ v) j j :=
        fun j => (Matrix.mul_apply).symm
      simp only [this, hHG, Matrix.one_apply_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [finsum_eq_sum_of_fintype]
    simp only [hσ]
    rw [← Complex.re_sum]
    have hg : ∀ i j, gram μ v i j = ∑ σ, ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ := fun i j => by
      rw [gram, Matrix.of_apply, finsum_eq_sum_of_fintype]
    have hswap : ∑ σ, ∑ i, ∑ j, (gram μ v)⁻¹ j i * ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ =
        ∑ i, ∑ j, (gram μ v)⁻¹ j i * gram μ v i j := by
      simp only [hg, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [hswap, hsum, Complex.natCast_re]
  · intro σ y M hM h
    set w := v σ y with hw
    set u := (gram μ v)⁻¹ *ᵥ w with hu'
    have hB := key σ y
    rw [← hw] at hB
    have hdot : star u ⬝ᵥ w = star w ⬝ᵥ ((gram μ v)⁻¹ *ᵥ w) := by
      rw [hu', Matrix.star_mulVec, hHh.eq, ← Matrix.dotProduct_mulVec]
    have hc : cmb v (star u) σ y = bergmanDensity μ v σ y ^ 2 := by
      have : ∑ i, star u i * v σ y i = (bergmanDensity μ v σ y : ℂ) := by
        rw [hB, ← hdot]; rfl
      rw [cmb, this, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hl : l2 μ v (star u) = bergmanDensity μ v σ y := by
      apply Complex.ofReal_injective
      rw [(hl2 (star u)).2.2, hB, ← hdot]
      have hGu : gram μ v *ᵥ u = w := by
        rw [hu', Matrix.mulVec_mulVec, hGH, Matrix.one_mulVec]
      conv_rhs => rw [← hGu]
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def, Complex.conj_conj]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have h2 := h (star u)
    rw [hc, hl] at h2
    have h0 := hpos σ y
    nlinarith
end

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bergman_function_total_mass_extremal : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).PosDef → (∀ σ, Integrable (bergmanDensity μ v σ) (μ σ)) ∧ ∑ᶠ σ, ∫ y, bergmanDensity μ v σ y ∂μ σ = Fintype.card ι ∧ (∀ σ y, 0 ≤ bergmanDensity μ v σ y) ∧ ∀ σ y (M : ℝ), 0 ≤ M → (∀ c : ι → ℂ, cmb v c σ y ≤ M * l2 μ v c) → bergmanDensity μ v σ y ≤ M := by
  atlas_forward_decl GlobalTheory.HSAmp.berg_mass_extremal
end

section
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

theorem abs_integral_weight_sub_le_one {Y : Type} [MeasurableSpace Y] (μ : Measure Y)
    (B β w : Y → ℝ) (C : ℝ) (hB : Integrable B μ) (hβ : Integrable β μ) (hle : ∀ y, B y ≤ β y)
    (hw : Measurable w) (hC : ∀ y, |w y| ≤ C) :
    |∫ y, w y * B y ∂μ - ∫ y, w y * β y ∂μ| ≤ C * (∫ y, β y ∂μ - ∫ y, B y ∂μ) := by
  have hwm : AEStronglyMeasurable w μ := hw.aestronglyMeasurable
  have hb : ∀ᵐ y ∂μ, ‖w y‖ ≤ C := Eventually.of_forall fun y => by simpa using hC y
  have h1 : Integrable (fun y => w y * B y) μ := hB.bdd_mul hwm hb
  have h2 : Integrable (fun y => w y * β y) μ := hβ.bdd_mul hwm hb
  rw [← integral_sub h1 h2, ← integral_sub hβ hB, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans ?_
  refine integral_mono (h1.sub h2).abs ((hβ.sub hB).const_mul C) fun y => ?_
  have h3 : 0 ≤ β y - B y := sub_nonneg.2 (hle y)
  show |w y * B y - w y * β y| ≤ C * (β y - B y)
  rw [← mul_sub, abs_mul, abs_sub_comm, abs_of_nonneg h3]
  exact mul_le_mul_of_nonneg_right (hC y) h3

theorem abs_finsum_integral_weight_sub_le :
    ∀ (S : Type) [Finite S] (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (μ : ∀ σ, Measure (Y σ)) (B β w : ∀ σ, Y σ → ℝ) (C : ℝ), (∀ σ, Integrable (B σ) (μ σ)) → (∀ σ, Integrable (β σ) (μ σ)) → (∀ σ y, B σ y ≤ β σ y) → (∀ σ, Measurable (w σ)) → 0 ≤ C → (∀ σ y, |w σ y| ≤ C) → |∑ᶠ σ, ∫ y, w σ y * B σ y ∂μ σ - ∑ᶠ σ, ∫ y, w σ y * β σ y ∂μ σ| ≤ C * (∑ᶠ σ, ∫ y, β σ y ∂μ σ - ∑ᶠ σ, ∫ y, B σ y ∂μ σ) := by
  intro S _ Y _ μ B β w C hB hβ hle hw _ hC
  haveI := Fintype.ofFinite S
  simp only [finsum_eq_sum_of_fintype]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
  exact abs_integral_weight_sub_le_one (μ σ) (B σ) (β σ) (w σ) C (hB σ) (hβ σ) (hle σ) (hw σ) (hC σ)

end GlobalTheory.HSAmp
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem tendsto_of_abs_sub_le_eventually (a q : ℕ → ℝ) (I G W V C : ℝ) (hC : 0 ≤ C) (hq : Tendsto q atTop (𝓝 G))
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, |a m - I - ε * W| ≤ C * (G + ε * V - q m)) : Tendsto a atTop (𝓝 I) := by
  rw [Metric.tendsto_nhds]
  intro e he
  have hK : 0 < |W| + C * |V| + 1 := by positivity
  set ε := e / (2 * (|W| + C * |V| + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hq' := Metric.tendsto_nhds.1 hq (e / (2 * (C + 1))) (by positivity)
  filter_upwards [h ε hε0, hq'] with m hm hqm
  rw [Real.dist_eq] at hqm ⊢
  have h1 : |a m - I| ≤ |a m - I - ε * W| + ε * |W| := by
    have := abs_add_le (a m - I - ε * W) (ε * W)
    rw [abs_mul, abs_of_pos hε0] at this
    simpa using this
  have h2 : C * (G + ε * V - q m) ≤ C * |q m - G| + C * (ε * |V|) := by
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hC
    have := neg_abs_le (q m - G)
    have := le_abs_self V
    nlinarith
  have h3 : C * |q m - G| ≤ (C + 1) * |q m - G| := by nlinarith [abs_nonneg (q m - G)]
  have h4 : (C + 1) * |q m - G| < e / 2 := by
    have := mul_lt_mul_of_pos_left hqm (by linarith : (0:ℝ) < C + 1)
    rwa [mul_div_assoc', mul_comm 2 (C + 1), ← div_div, mul_div_cancel_left₀ _ (by linarith : (C + 1) ≠ 0)] at this
  have h5 : ε * (|W| + C * |V|) < e / 2 := by
    rw [hε, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg W, abs_nonneg V]
  nlinarith

end GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem tendsto_finsum_integral_berg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ w : ∀ σ, CxPts p σ → ℝ, (∀ σ, Continuous (w σ)) → Tendsto (fun m : ℕ => (∑ᶠ σ, ∫ y, w σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas) / (m : ℝ) ^ D) atTop (𝓝 (chInt P.L D w / D.factorial)) := by
  intro k _ X _ p D hX hG P hpos ω r f hf hli hr w hw
  classical
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  letI := Fintype.ofFinite (k →+* ℂ)
  have hcpt : ∀ σ, CompactSpace (CxPts p σ) := hX.compactSpace
  have hfm : ∀ σ, IsFiniteMeasure (ω σ).meas := fun σ => (GlobalTheory.T.smoothVolumeDensity_finite_isOpenPos k X p D hX hG σ (ω σ)).1
  choose ρ hρR hρ0 hρint using fun σ => GlobalTheory.T.exists_chernTopPower_volumeDensity_ratio k X p D hX hG P.L hpos σ (ω σ)
  have hbd : ∀ σ (g : CxPts p σ → ℝ), Continuous g → ∃ C, ∀ y, |g y| ≤ C := fun σ g hg => by
    haveI := hcpt σ
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
    exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩
  have hint : ∀ σ (g : CxPts p σ → ℝ), Continuous g → Integrable g (ω σ).meas := fun σ g hg => by
    haveI := hfm σ
    obtain ⟨C, hC⟩ := hbd σ g hg
    exact Integrable.of_bound hg.aestronglyMeasurable C
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y)
  choose Cw hCw using fun σ => hbd σ (w σ) (hw σ)
  set C : ℝ := ∑ σ, |Cw σ| with hCdef
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hwC : ∀ σ y, |w σ y| ≤ C := fun σ y => (hCw σ y).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun σ => |Cw σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)))
  set Iw : ℝ := ∑ σ, ∫ y, w σ y * ρ σ y ∂(ω σ).meas with hIw
  set G' : ℝ := ∑ σ, ∫ y, ρ σ y ∂(ω σ).meas with hG'
  set W : ℝ := ∑ σ, ∫ y, w σ y ∂(ω σ).meas with hW
  set V : ℝ := ∑ σ, ∫ _y, (1 : ℝ) ∂(ω σ).meas with hV
  have hch : chInt P.L D w = Iw := by
    simp only [chInt, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun σ _ => hρint σ (w σ) (hw σ)
  have hgd : gdeg P.L D = G' := by
    simp only [gdeg, chInt, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hρint σ _ continuous_const]
    simp
  rw [hch]
  rw [hgd] at hr
  refine tendsto_of_abs_sub_le_eventually _ (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) (Iw / D.factorial)
    (G' / D.factorial) W V C hC0 hr fun ε hε => ?_
  filter_upwards [GlobalTheory.T.holomorphicMorse_sections_mL_add_A_uniform k X p D hX hG P hpos ω ρ hρR ε hε, eventually_ge_atTop 1] with m hmo hm1
  obtain ⟨hfam, hpd, -⟩ := GlobalTheory.T.gram_posDef_l2_le_sup_of_lin_indep k X p D hX hG P ω m 1 (Fin (r m)) (f m) (hf m) (hli m)
  obtain ⟨hBi, hBs, hB0, hBx⟩ := GlobalTheory.T.bergman_function_total_mass_extremal (k →+* ℂ) (fun σ => CxPts p σ) (Fin (r m))
    (fun σ => (ω σ).meas) (vals P m 1 (f m)) hfam hpd
  set M : ℝ := (m : ℝ) ^ D with hMdef
  have hM : 0 < M := pow_pos (by exact_mod_cast hm1) D
  have hDf : (0 : ℝ) < D.factorial := by exact_mod_cast D.factorial_pos
  have hle : ∀ σ y, bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ≤ (ρ σ y / D.factorial + ε) * M :=
    fun σ y => hBx σ y _ (mul_nonneg (add_nonneg (div_nonneg (hρ0 σ y) hDf.le) hε.le) hM.le)
      fun c => hmo (Fin (r m)) (f m) (hf m) c σ y
  have hβi : ∀ σ, Integrable (fun y => (ρ σ y / D.factorial + ε) * M) (ω σ).meas := fun σ => by
    haveI := hfm σ
    exact (((hint σ _ (hρR σ).1).div_const _).add (integrable_const ε)).mul_const M
  have hl1 := abs_finsum_integral_weight_sub_le (k →+* ℂ) (fun σ => CxPts p σ) (fun σ => (ω σ).meas)
    (bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m))) (fun σ y => (ρ σ y / D.factorial + ε) * M) w C hBi hβi hle
    (fun σ => (hw σ).measurable) hC0 hwC
  have e1 : ∀ σ, ∫ y, w σ y * ((ρ σ y / D.factorial + ε) * M) ∂(ω σ).meas =
      M / D.factorial * ∫ y, w σ y * ρ σ y ∂(ω σ).meas + M * ε * ∫ y, w σ y ∂(ω σ).meas := fun σ => by
    have h1 : Integrable (fun y => w σ y * ρ σ y) (ω σ).meas := hint σ _ ((hw σ).mul (hρR σ).1)
    have h2 := hint σ _ (hw σ)
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h1.const_mul _) (h2.const_mul _)]
    congr 1; funext y; ring
  have e2 : ∀ σ, ∫ y, (ρ σ y / D.factorial + ε) * M ∂(ω σ).meas =
      M / D.factorial * ∫ y, ρ σ y ∂(ω σ).meas + M * ε * ∫ _y, (1 : ℝ) ∂(ω σ).meas := fun σ => by
    haveI := hfm σ
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hint σ _ (hρR σ).1).const_mul _) ((integrable_const (1 : ℝ)).const_mul _)]
    congr 1; funext y; ring
  simp only [finsum_eq_sum_of_fintype] at hl1 hBs ⊢
  simp only [Fintype.card_fin] at hBs
  rw [Finset.sum_congr rfl fun σ _ => e1 σ, Finset.sum_congr rfl fun σ _ => e2 σ, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hBs] at hl1
  rw [← hIw, ← hW, ← hG', ← hV] at hl1
  set A : ℝ := ∑ σ, ∫ y, w σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas with hA
  have eq1 : A / M - Iw / D.factorial - ε * W = (A - (M / D.factorial * Iw + M * ε * W)) / M := by
    field_simp
    ring
  rw [eq1, abs_div, abs_of_pos hM, div_le_iff₀ hM]
  have eq2 : C * (G' / D.factorial + ε * V - (r m : ℝ) / M) * M =
      C * (M / D.factorial * G' + M * ε * V - (r m : ℝ)) := by
    field_simp
  rw [eq2]
  exact hl1

end GlobalTheory.HSAmp
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_bergmanMeasure_chernForm_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ w : ∀ σ, CxPts p σ → ℝ, (∀ σ, Continuous (w σ)) → Tendsto (fun m : ℕ => (∑ᶠ σ, ∫ y, w σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas) / (m : ℝ) ^ D) atTop (𝓝 (chInt P.L D w / D.factorial)) := by
  atlas_forward_decl GlobalTheory.HSAmp.tendsto_finsum_integral_berg
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

theorem gram_det_up_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ (u : SmFn p) (ε : ℝ), 0 < ε → ∀ᶠ m : ℕ in atTop, Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re ≤ (chInt P.L D u.u / D.factorial + ε) * (m : ℝ) ^ (D + 1) := by
  intro k _ X _ p D hX hG P hL ω r f hf hli hr u ε hε
  have hcomp : ∀ σ, CompactSpace (CxPts p σ) := hX.compactSpace
  have hcont : ∀ σ, Continuous (u.u σ) := fun σ =>
    continuous_iff_continuousAt.2 fun y => (u.cInf σ y).continuousAt
  have hT := GlobalTheory.T.tendsto_bergmanMeasure_chernForm_pow k X p D hX hG P hL ω r f hf hli hr u.u hcont
  have hev : ∀ᶠ m : ℕ in atTop, (∑ᶠ σ, ∫ y, u.u σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas)
      / (m : ℝ) ^ D < chInt P.L D u.u / D.factorial + ε :=
    hT (Iio_mem_nhds (by linarith))
  filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
  obtain ⟨hF, hPD, -⟩ := GlobalTheory.T.gram_posDef_l2_le_sup_of_lin_indep k X p D hX hG P ω m 1 (Fin (r m)) (f m) (hf m) (hli m)
  haveI : Finite (k →+* ℂ) := hF.finite
  haveI : Fintype (k →+* ℂ) := Fintype.ofFinite _
  have hB : ∀ σ, ∃ C : ℝ, ∀ y, |u.u σ y| ≤ C := fun σ => by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hcont σ).continuousOn
    exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩
  choose C hC using hB
  set w : ∀ σ, CxPts p σ → ℝ := fun σ y => (((m : ℤ) : ℝ)) * u.u σ y with hw
  have hwm : ∀ σ, Measurable (w σ) := fun σ => (continuous_const.mul (hcont σ)).measurable
  have hwb : ∀ σ y, |w σ y| ≤ (m : ℝ) * ∑ τ, |C τ| := fun σ y => by
    simp only [hw, Int.cast_natCast, abs_mul, Nat.abs_cast]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg m)
    exact (hC σ y).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun τ => |C τ|) (fun τ _ => abs_nonneg _) (Finset.mem_univ σ)))
  obtain ⟨-, -, hJ⟩ := GlobalTheory.T.gramDeterminant_jensen_change_of_weight (k →+* ℂ) (fun σ => CxPts p σ) (Fin (r m)) (fun σ => (ω σ).meas)
    (vals P m 1 (f m)) hF hPD w _ hwm hwb
  have hnew : (fun σ y i => vals P m 1 (f m) σ y i * ((Real.exp (-(w σ y) / 2) : ℝ) : ℂ))
      = vals (upperParabolic P u) m 1 (f m) := by
    funext σ y i
    simp only [vals, hw]
    rw [((GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u m 1).2.2 σ y (f m i)).1]
  rw [hnew] at hJ
  have hsum : (∑ᶠ σ, ∫ y, w σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas)
      = (m : ℝ) * ∑ᶠ σ, ∫ y, u.u σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas := by
    rw [mul_finsum]
    refine finsum_congr fun σ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hw, Int.cast_natCast]
    ring
  rw [hsum] at hJ
  have hmpos : (0 : ℝ) < (m : ℝ) ^ D := pow_pos (by exact_mod_cast hm1) D
  rw [div_lt_iff₀ hmpos] at hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h2 := mul_le_mul_of_nonneg_left hm.le hm0
  calc _ ≤ (m : ℝ) * ∑ᶠ σ, ∫ y, u.u σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas := by linarith
    _ ≤ _ := h2
    _ = _ := by ring

end GlobalTheory.HSAmp
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramDeterminant_weightShift_asymptotic_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ (u : SmFn p) (ε : ℝ), 0 < ε → ∀ᶠ m : ℕ in atTop, Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re ≤ (chInt P.L D u.u / D.factorial + ε) * (m : ℝ) ^ (D + 1) := by
  atlas_forward_decl GlobalTheory.HSAmp.gram_det_up_le
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSAmpDet

theorem chInt_smul {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (D : ℕ) (c : ℝ) (u : SmFn p) :
    chInt L D (u.smul c).u = c * chInt L D u.u := by
  simp only [chInt, SmFn.smul, Weight.chernInt_const_mul, mul_finsum]

section
variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem vals_smul (P : Pair p) (u : SmFn p) (t : ℝ) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic P (u.smul t)) a b g = fun σ y i => vals P a b g σ y i * (Real.exp (-(a * (t * u.u σ y)) / 2) : ℝ) := by
  funext σ y i
  exact ((GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P (u.smul t) a b).2.2 σ y (g i)).1

theorem vals_zero (P : Pair p) (u : SmFn p) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic P (u.smul 0)) a b g = vals P a b g := by
  rw [vals_smul]
  funext σ y i
  simp

theorem vals_one (P : Pair p) (u : SmFn p) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic P (u.smul 1)) a b g = vals (upperParabolic P u) a b g := by
  rw [vals_smul]
  funext σ y i
  rw [one_mul]
  exact ((GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u a b).2.2 σ y (g i)).1.symm

theorem vals_two (P : Pair p) (u : SmFn p) (t t' : ℝ) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic (upperParabolic P (u.smul t)) (u.smul (t' - t))) a b g = vals (upperParabolic P (u.smul t')) a b g := by
  rw [vals_smul, vals_smul, vals_smul]
  funext σ y i
  rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  ring

end

theorem tendsto_logDet_gram_sub : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ (u : SmFn p) (a a' : ℝ), (up P.L u).SemiPos D → P.L.IsSelfInter a → (up P.L u).IsSelfInter a' → Tendsto (fun m : ℕ => (Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (2 * (a' - a) / (D + 1).factorial)) := by
  intro hA k _ X _ p D hX hG P hP ω r f hf hli hr u a a' hsp ha ha'
  obtain ⟨s, hs0, hs1, hsd⟩ := GlobalTheory.T.self_intersection_metric_segment_polynomial hA k X p D hX P.L u a a' ha ha'
  set c : ℝ := 2 / ((D + 1).factorial : ℝ) with hc
  let ℓ : ℚ → ℕ → ℝ := fun t m =>
    Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P (u.smul (t : ℝ))) m 1 (f m))).det.re / (m : ℝ) ^ (D + 1)
  have hR := GlobalTheory.T.tendsto_sub_of_one_sided_increment_bound_derivative (Polynomial.C c * s) ℓ ?_
  · have hfun : (fun m => ℓ 0 m - ℓ 1 m) = fun m : ℕ => (Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re) / (m : ℝ) ^ (D + 1) := by
      funext m
      simp only [ℓ, Rat.cast_zero, Rat.cast_one, vals_zero, vals_one, sub_div]
    have hval : (Polynomial.C c * s).eval 1 - (Polynomial.C c * s).eval 0 = 2 * (a' - a) / (D + 1).factorial := by
      simp only [Polynomial.eval_mul, Polynomial.eval_C, hs0, hs1, hc]
      ring
    rw [hfun, hval] at hR
    exact hR
  · intro t t' ht0 ht1 ht0' ht1' ε hε
    have hsemi : (upperParabolic P (u.smul (t : ℝ))).L.SemiPos D :=
      GlobalTheory.T.semiPos_raiseWeight_segment_smul k X p D P.L u t (by exact_mod_cast ht0) (by exact_mod_cast ht1) hP hsp
    have hH : ∀ (m : ℕ) i, f m i ∈ (upperParabolic P (u.smul (t : ℝ))).H m 1 := fun m i => by
      rw [(GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P (u.smul (t : ℝ)) m 1).1]
      exact hf m i
    have hrk : Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop
        (𝓝 (gdeg (upperParabolic P (u.smul (t : ℝ))).L D / D.factorial)) := by
      rw [show (upperParabolic P (u.smul (t : ℝ))).L = up P.L (u.smul (t : ℝ)) from rfl,
        GlobalTheory.T.hermLineBundleGeometricDegree_raiseWeight hA k X p D hX P.L (u.smul (t : ℝ))]
      exact hr
    have hstep := GlobalTheory.T.gramDeterminant_weightShift_asymptotic_le k X p D hX hG (upperParabolic P (u.smul (t : ℝ))) hsemi ω r f hH hli hrk
      (u.smul ((t' : ℝ) - t)) ε hε
    have hch : chInt (upperParabolic P (u.smul (t : ℝ))).L D (u.smul ((t' : ℝ) - t)).u / D.factorial =
        ((t' : ℝ) - t) * (Polynomial.C c * s).derivative.eval (t : ℝ) := by
      rw [chInt_smul, Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C, ← hsd t, hc,
        Nat.factorial_succ]
      have hf0 : (D.factorial : ℝ) ≠ 0 := by positivity
      show ((t' : ℝ) - t) * chInt (up P.L (u.smul (t : ℝ))) D u.u / D.factorial = _
      push_cast
      field_simp
    filter_upwards [hstep, eventually_ge_atTop 1] with m hm hm1
    have hpos : (0 : ℝ) < (m : ℝ) ^ (D + 1) := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      positivity
    rw [vals_two, hch] at hm
    simp only [ℓ]
    rw [← sub_div, div_le_iff₀ hpos]
    linarith

end GlobalTheory.HSAmpDet
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_logDet_gram_change_semiPositive_metric : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ (u : SmFn p) (a a' : ℝ), (up P.L u).SemiPos D → P.L.IsSelfInter a → (up P.L u).IsSelfInter a' → Tendsto (fun m : ℕ => (Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (2 * (a' - a) / (D + 1).factorial)) := by
  atlas_forward_decl GlobalTheory.HSAmpDet.tendsto_logDet_gram_sub
end
