import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsOffOpenFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMeasureDensityExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinePairExtensionCosSqBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousCosSqAngleFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricRestrictionVanishingLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoOfEqualSublinesShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricIsometricOfIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsoIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortExactOfComposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactCompositionCompatibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactCompositionMetricCompatStatement

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.ArInt GlobalTheory.Cartier

namespace GlobalTheory.HermLB

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} [IsIntegral X] [IsLocallyNoetherian X]

omit [IsIntegral X] [IsLocallyNoetherian X] in

theorem isometric_comb_unit_one (M : HermLB p) :
    (comb (fun _ : Unit => M) fun _ => 1).Isometric M := by
  have e : (fun _ : Unit => (1 : ℤ)) = Pi.single () 1 := by
    funext u
    simp
  rw [e]
  exact isometric_comb_single (fun _ : Unit => M) ()

theorem arMix_pair (HM : Published.ArMix) (hX : IsArithVar p 1) {L M : HermLB p}
    {Φ : MvPolynomial (Option Unit) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option Unit => o.elim L fun _ => M) 1 Φ) {h : X → ℝ} (H : M.IsArithHeight h)
    (r : L.B.ι → X.functionFieldˣ) (hr : IsRatSec L.B r) :
    M.ArchIntegrable L 1 hr ∧
      Φ (MvPolynomial.X none * MvPolynomial.X (some ())) =
        ∑ᶠ z, ((L.div hr).mult z : ℝ) * h z - M.archInt L 1 hr := by
  have e := isometric_comb_unit_one M
  obtain ⟨h₁, h₂⟩ := HM k X p 1 hX Unit L (fun _ => M) Φ hΦ (fun _ => 1) h
    (e.symm.isArithHeight hX H) r hr
  have hl : MvPolynomial.rename some (lin fun _ : Unit => (((1 : ℤ) : ℤ) : ℝ)) ^ 1 =
      (MvPolynomial.X (some ()) : MvPolynomial (Option Unit) ℝ) := by
    simp [lin]
  rw [hl] at h₂
  refine ⟨fun σ => ?_, ?_⟩
  · rw [← e.chernIntegrableOn_eq σ 1]
    exact h₁ σ
  · have a : (comb (fun _ : Unit => M) fun _ => 1).archInt L 1 hr = M.archInt L 1 hr :=
      finsum_congr fun σ => congrFun (congrFun (e.chernInt_eq σ 1) _) _
    rw [h₂, a]

theorem isInter_iff (HE : Published.ArExists) (HM : Published.ArMix) (hX : IsArithVar p 1) {L M : HermLB p}
    {Φ : MvPolynomial (Option Unit) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option Unit => o.elim L fun _ => M) 1 Φ) (a : ℝ) :
    L.IsInter M a ↔ a = Φ (MvPolynomial.X none * MvPolynomial.X (some ())) := by
  constructor
  · rintro ⟨h, H, ha⟩
    obtain ⟨r, hr⟩ := exists_isRatSec L.isLB
    rw [(ha r hr).2, (arMix_pair HM hX hΦ H r hr).2]
  · rintro rfl
    obtain ⟨h, H⟩ := (HE k X p 1 hX).1 M
    exact ⟨h, H, fun r hr => arMix_pair HM hX hΦ H r hr⟩

theorem isInter_of_comb (HE : Published.ArExists) (HM : Published.ArMix) (HI : Published.ArIso) (hX : IsArithVar p 1)
    {ι : Type} [Fintype ι] {T : ι → HermLB p} {Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (hΨ : IsArFun T 1 Ψ)
    {u v : ι → ℤ} {L M : HermLB p} (hu : (comb T u).Isometric L) (hv : (comb T v).Isometric M) :
    L.IsInter M (Ψ (lin (fun i => (u i : ℝ)) * lin fun i => (v i : ℝ))) := by
  have hΦ := ((HI k X p 1 hX).2 ι T Ψ hΨ).2.2 (Option Unit) (fun o => o.elim L fun _ => M)
    (fun o => o.elim u fun _ => v) (by rintro (_ | _); exacts [hu, hv])
  refine (isInter_iff HE HM hX hΦ _).2 ?_
  simp

theorem lin_add_int {ι : Type} [Fintype ι] (u v : ι → ℤ) :
    (lin fun i => (((u + v) i : ℤ) : ℝ)) = (lin fun i => (u i : ℝ)) + lin fun i => (v i : ℝ) := by
  simp [lin, add_mul, Finset.sum_add_distrib]

end GlobalTheory.HermLB

namespace GlobalTheory

theorem isInter_calculus : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X]
    [IsLocallyNoetherian X], IsArithVar p 1 → ∀ (L L' M : HermLB p), (∃ a, L.IsInter M a) ∧
      (∀ a, L.IsInter M a → M.IsInter L a) ∧
      (∀ a a', L.IsInter M a → L'.IsInter M a' → (L.tens L').IsInter M (a + a')) ∧
      ∀ a x y z, L.IsInter M a → L.IsSelfInter x → M.IsSelfInter y → (L.tens M).IsSelfInter z →
        z = x + 2 * a + y := by
  intro hC k _ X p _ _ hX L L' M
  have HE := hC.arExists
  have HM := hC.arMix
  have HI := hC.arIso
  let T : Fin 3 → HermLB p := ![L, L', M]
  obtain ⟨Ψ, hΨ⟩ := ((HE k X p 1 hX).2 (Fin 3) T).1
  let e : Fin 3 → Fin 3 → ℤ := fun i => Pi.single i 1
  have c₀ : (comb T (e 0)).Isometric L := isometric_comb_single T 0
  have c₁ : (comb T (e 1)).Isometric L' := isometric_comb_single T 1
  have c₂ : (comb T (e 2)).Isometric M := isometric_comb_single T 2
  have l (i : Fin 3) : (lin fun j => ((e i j : ℤ) : ℝ)) = MvPolynomial.X i := lin_single i
  have s₀₁ : (comb T (e 0 + e 1)).Isometric (L.tens L') :=
    (isometric_comb_add T _ _).trans (c₀.tens c₁)
  have s₀₂ : (comb T (e 0 + e 2)).Isometric (L.tens M) :=
    (isometric_comb_add T _ _).trans (c₀.tens c₂)
  have I₀ := HermLB.isInter_of_comb HE HM HI hX hΨ c₀ c₂
  have I₀' := HermLB.isInter_of_comb HE HM HI hX hΨ c₂ c₀
  have I₁ := HermLB.isInter_of_comb HE HM HI hX hΨ c₁ c₂
  have I₀₁ := HermLB.isInter_of_comb HE HM HI hX hΨ s₀₁ c₂
  rw [l, l] at I₀ I₀' I₁
  rw [HermLB.lin_add_int, l, l, l] at I₀₁
  refine ⟨⟨_, I₀⟩, fun a ha => ?_, fun a a' ha ha' => ?_, fun a x y z ha hx hy hz => ?_⟩
  · rw [ha.unique hX I₀, mul_comm]
    exact I₀'
  · rw [ha.unique hX I₀, ha'.unique hX I₁, ← map_add, ← add_mul]
    exact I₀₁
  · have S₀ := c₀.isSelfInter hX (hΨ.1 (e 0))
    have S₂ := c₂.isSelfInter hX (hΨ.1 (e 2))
    have S := s₀₂.isSelfInter hX (hΨ.1 (e 0 + e 2))
    rw [l] at S₀ S₂
    rw [HermLB.lin_add_int, l, l] at S
    rw [hx.unique hX S₀, hy.unique hX S₂, hz.unique hX S, ha.unique hX I₀]
    have E : (MvPolynomial.X 0 + MvPolynomial.X 2 : MvPolynomial (Fin 3) ℝ) ^ (1 + 1) =
        MvPolynomial.X 0 ^ (1 + 1) + (MvPolynomial.X 0 * MvPolynomial.X 2 + MvPolynomial.X 0 * MvPolynomial.X 2) +
          MvPolynomial.X 2 ^ (1 + 1) := by ring
    rw [E, map_add, map_add, map_add]
    ring

end GlobalTheory
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernDens_detWeight_eq_neg_levi_log : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), (∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → IsDens fun (c : AlgChart p σ 1) y => c.chernDens φ y) ∧ ∀ (L : X.Modules) (g : Met p σ L 1), g.IsCInf → ∀ (U : X.Opens) (t : Γ(L, U)), IsFrame (fun _ : Fin 1 => t) → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∈ ptsIn p σ U → c.chernDens g.detWeight y = -(leviForm (fun v => Real.log (g.form t t (c.e.symm v)).re) (c.e y) (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)).re / Real.pi := by
  first | exact @GlobalTheory.CurveDens.chernDens_curve | exact GlobalTheory.CurveDens.chernDens_curve | (intros; apply GlobalTheory.CurveDens.chernDens_curve <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.CurveDens

section Abstract

variable {Y : Type} [MeasurableSpace Y] {ν : Measure Y}

theorem integrableOn_and_sub_withDensity {g F : Y → ℝ} {S : Set Y} (hg : Measurable g)
    (hS : MeasurableSet S)
    (h₁ : IntegrableOn F S (ν.withDensity fun y => ENNReal.ofReal (g y)))
    (h₂ : IntegrableOn F S (ν.withDensity fun y => ENNReal.ofReal (-g y))) :
    IntegrableOn (fun y => g y * F y) S ν ∧
      (∫ y in S, F y ∂(ν.withDensity fun y => ENNReal.ofReal (g y))) -
        (∫ y in S, F y ∂(ν.withDensity fun y => ENNReal.ofReal (-g y))) =
      ∫ y in S, g y * F y ∂ν := by
  have m₁ : Measurable fun y => ENNReal.ofReal (g y) := hg.ennreal_ofReal
  have m₂ : Measurable fun y => ENNReal.ofReal (-g y) := hg.neg.ennreal_ofReal
  have t₁ : ∀ᵐ y ∂(ν.restrict S), ENNReal.ofReal (g y) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have t₂ : ∀ᵐ y ∂(ν.restrict S), ENNReal.ofReal (-g y) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  unfold IntegrableOn at h₁ h₂ ⊢
  rw [restrict_withDensity hS] at h₁ h₂
  rw [restrict_withDensity hS, restrict_withDensity hS]
  have i₁ := (integrable_withDensity_iff_integrable_smul' m₁ t₁).1 h₁
  have i₂ := (integrable_withDensity_iff_integrable_smul' m₂ t₂).1 h₂
  have e : ∀ y, g y * F y =
      (ENNReal.ofReal (g y)).toReal • F y - (ENNReal.ofReal (-g y)).toReal • F y := fun y => by
    rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal', smul_eq_mul, smul_eq_mul, ← sub_mul]
    congr 1
    rcases le_total 0 (g y) with h | h
    · simp [h]
    · simp [h]
  refine ⟨(i₁.sub i₂).congr (Eventually.of_forall fun y => (e y).symm), ?_⟩
  rw [integral_withDensity_eq_integral_toReal_smul₀ m₁.aemeasurable t₁,
    integral_withDensity_eq_integral_toReal_smul₀ m₂.aemeasurable t₂, ← integral_sub i₁ i₂]
  exact integral_congr_ae (Eventually.of_forall fun y => (e y).symm)

theorem tendsto_partial_log {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, x ^ (n + 1) / ((n : ℝ) + 1)) atTop
      (𝓝 (-Real.log (1 - x))) := by
  have := (Real.hasSum_pow_div_log_of_abs_lt_one (x := x) (by rwa [abs_of_nonneg h0])).tendsto_sum_nat
  exact this

theorem partial_log_bound {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (N : ℕ) :
    0 ≤ ∑ n ∈ Finset.range N, x ^ (n + 1) / ((n : ℝ) + 1) ∧
      ∑ n ∈ Finset.range N, x ^ (n + 1) / ((n : ℝ) + 1) ≤ -Real.log (1 - x) := by
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := x) (by rwa [abs_of_nonneg h0])
  have hn : ∀ n : ℕ, 0 ≤ x ^ (n + 1) / ((n : ℝ) + 1) := fun n => by positivity
  refine ⟨Finset.sum_nonneg fun n _ => hn n, ?_⟩
  rw [← hs.tsum_eq]
  exact hs.summable.sum_le_tsum _ fun n _ => hn n

theorem integral_log_eq_of_forall_pow [IsFiniteMeasure ν] {v D d : Y → ℝ}
    (hv : Measurable v) (hD : Measurable D) (hd : Measurable d)
    (bD : ∃ C, ∀ y, |D y| ≤ C) (bd : ∃ C, ∀ y, |d y| ≤ C)
    (h0 : ∀ y, 0 ≤ v y) (h1 : ∀ᵐ y ∂ν, v y < 1)
    (hi : Integrable (fun y => D y * Real.log (1 - v y)) ν)
    (H : ∀ n : ℕ, ∫ y, (v y ^ (n + 1) * D y + (n + 1) * v y ^ n * (1 - v y) * d y) ∂ν = 0) :
    ∫ y, D y * Real.log (1 - v y) ∂ν = ∫ y, d y ∂ν := by
  obtain ⟨CD, hCD⟩ := bD
  obtain ⟨Cd, hCd⟩ := bd
  have hdi : Integrable d ν := Integrable.of_bound hd.aestronglyMeasurable Cd
    (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hCd y)
  have hhm : ∀ n : ℕ, Measurable fun y =>
      v y ^ (n + 1) * D y + ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y := fun n =>
    ((hv.pow_const _).mul hD).add
      (((measurable_const.mul (hv.pow_const _)).mul (measurable_const.sub hv)).mul hd)
  have hhi : ∀ n : ℕ, Integrable (fun y =>
      v y ^ (n + 1) * D y + ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y) ν := fun n => by
    refine Integrable.of_bound (hhm n).aestronglyMeasurable (CD + ((n : ℝ) + 1) * Cd) ?_
    filter_upwards [h1] with y hy
    have a0 : 0 ≤ v y ^ (n + 1) := pow_nonneg (h0 y) _
    have a1 : v y ^ (n + 1) ≤ 1 := pow_le_one₀ (h0 y) hy.le
    have b0 : 0 ≤ v y ^ n * (1 - v y) := mul_nonneg (pow_nonneg (h0 y) _) (by linarith)
    have b1 : v y ^ n * (1 - v y) ≤ 1 :=
      mul_le_one₀ (pow_le_one₀ (h0 y) hy.le) (by linarith) (by linarith [h0 y])
    have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg a0]
      calc v y ^ (n + 1) * |D y| ≤ 1 * |D y| := by gcongr
        _ ≤ CD := by simpa using hCD y
    · have e : ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y =
          ((n : ℝ) + 1) * ((v y ^ n * (1 - v y)) * d y) := by ring
      rw [e, abs_mul, abs_mul, abs_of_nonneg hn, abs_of_nonneg b0]
      gcongr
      calc v y ^ n * (1 - v y) * |d y| ≤ 1 * |d y| := by gcongr
        _ ≤ Cd := by simpa using hCd y

  have hQ : ∀ N : ℕ, ∫ y, (∑ n ∈ Finset.range N, (((n : ℝ) + 1)⁻¹ *
      (v y ^ (n + 1) * D y + ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y))) ∂ν = 0 := fun N => by
    rw [integral_finset_sum _ fun n _ => (hhi n).const_mul _]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [integral_const_mul]
    have := H n
    push_cast at this
    rw [this, mul_zero]
  have hform : ∀ (N : ℕ) (y : Y), (∑ n ∈ Finset.range N, (((n : ℝ) + 1)⁻¹ *
      (v y ^ (n + 1) * D y + ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y))) =
      (∑ n ∈ Finset.range N, v y ^ (n + 1) / ((n : ℝ) + 1)) * D y + (1 - v y ^ N) * d y := by
    intro N y
    rw [← geom_sum_mul_neg, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hlim : Tendsto (fun N : ℕ => ∫ y, (∑ n ∈ Finset.range N, (((n : ℝ) + 1)⁻¹ *
      (v y ^ (n + 1) * D y + ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y))) ∂ν) atTop
      (𝓝 (∫ y, (-(D y * Real.log (1 - v y)) + d y) ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => |D y * Real.log (1 - v y)| + |d y|)
      (fun N => (Finset.measurable_sum _ fun n _ =>
        measurable_const.mul (hhm n)).aestronglyMeasurable)
      (hi.abs.add hdi.abs) (fun N => ?_) ?_
    · filter_upwards [h1] with y hy
      rw [hform, Real.norm_eq_abs]
      obtain ⟨q0, q1⟩ := partial_log_bound (h0 y) hy N
      have l0 : 0 ≤ -Real.log (1 - v y) :=
        neg_nonneg.2 (Real.log_nonpos (by linarith) (by linarith [h0 y]))
      have p0 : 0 ≤ v y ^ N := pow_nonneg (h0 y) _
      have p1 : v y ^ N ≤ 1 := pow_le_one₀ (h0 y) hy.le
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_mul, abs_of_nonneg q0, mul_comm, ← abs_neg (Real.log _),
          abs_of_nonneg l0]
        gcongr
      · rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - v y ^ N)]
        calc (1 - v y ^ N) * |d y| ≤ 1 * |d y| := by gcongr; linarith
          _ = |d y| := one_mul _
    · filter_upwards [h1] with y hy
      simp_rw [hform]
      have t1 := tendsto_partial_log (h0 y) hy
      have t2 : Tendsto (fun N : ℕ => v y ^ N) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (h0 y) hy
      have := (t1.mul_const (D y)).add ((tendsto_const_nhds (x := (1 : ℝ)).sub t2).mul_const (d y))
      convert this using 2
      ring
  have hz : ∫ y, (-(D y * Real.log (1 - v y)) + d y) ∂ν = 0 := by
    refine tendsto_nhds_unique hlim ?_
    simp_rw [hQ]
    exact tendsto_const_nhds
  rw [integral_add (show Integrable (fun y => -(D y * Real.log (1 - v y))) ν from hi.neg) hdi,
    integral_neg] at hz
  linarith

end Abstract

theorem green_sum : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∀ (κ κ' δ : AlgChart p σ 1 → CxPts p σ → ℝ), IsDens κ → IsDens κ' → IsDens δ → ∀ (v f : CxPts p σ → ℝ) (S : Set (CxPts p σ)), Continuous v → (∀ y, 0 ≤ v y ∧ v y ≤ 1) → IsOpen S → Sᶜ.Finite → (∀ y ∈ S, v y < 1 ∧ f y = Real.log (1 - v y) / 2) → IntegrableOn f S (part κ) → IntegrableOn f S (part fun c y => -κ c y) → IntegrableOn f S (part κ') → IntegrableOn f S (part fun c y => -κ' c y) → (∀ n : ℕ, total (fun c y => v y ^ (n + 1) * (κ c y - κ' c y) + (n + 1) * v y ^ n * (1 - v y) * δ c y) = 0) → 2 * ((∫ y in S, f y ∂(part κ) - ∫ y in S, f y ∂(part fun c y => -κ c y)) - (∫ y in S, f y ∂(part κ') - ∫ y in S, f y ∂(part fun c y => -κ' c y))) = total δ := by
  intro k _ X p σ _ _ _ hR κ κ' δ hκ hκ' hδ v f S hv hv01 hSo hSf hSv i1 i2 i3 i4 H
  obtain ⟨ν, w, hfin, hno, hdens, hmeas⟩ := GlobalTheory.T.finite_measure_density_exists k X p σ hR
  obtain ⟨g, hg, hgw⟩ := hdens κ hκ
  obtain ⟨g', hg', hgw'⟩ := hdens κ' hκ'
  obtain ⟨d, hd, hdw⟩ := hdens δ hδ
  have p1 := (hmeas κ g hg hgw).1
  have p2 := (hmeas (fun c y => -κ c y) (fun y => -g y) hg.neg
    fun c y hy => by rw [hgw c y hy, neg_mul]).1
  have p3 := (hmeas κ' g' hg' hgw').1
  have p4 := (hmeas (fun c y => -κ' c y) (fun y => -g' y) hg'.neg
    fun c y hy => by rw [hgw' c y hy, neg_mul]).1
  have hSm : MeasurableSet S := hSo.measurableSet
  haveI : NullSingletonClass ν := hno
  have hae : ∀ᵐ y ∂ν, y ∈ S := mem_ae_iff.2 (hSf.measure_zero ν)
  have hres : ν.restrict S = ν := Measure.restrict_eq_self_of_ae_mem hae
  have hF : Set.EqOn f (fun y => Real.log (1 - v y) / 2) S := fun y hy => (hSv y hy).2
  rw [p1] at i1
  rw [p2] at i2
  rw [p3] at i3
  rw [p4] at i4
  obtain ⟨a1, e1⟩ := integrableOn_and_sub_withDensity hg.measurable hSm
    (i1.congr_fun hF hSm) (i2.congr_fun hF hSm)
  obtain ⟨a2, e2⟩ := integrableOn_and_sub_withDensity hg'.measurable hSm
    (i3.congr_fun hF hSm) (i4.congr_fun hF hSm)
  unfold IntegrableOn at a1 a2
  rw [hres] at a1 a2 e1 e2
  have hi : Integrable (fun y => (g y - g' y) * Real.log (1 - v y)) ν :=
    ((a1.sub a2).const_mul 2).congr (Eventually.of_forall fun y => by simp only [Pi.sub_apply]; ring)
  have key := integral_log_eq_of_forall_pow (ν := ν) (v := v) (D := fun y => g y - g' y) (d := d)
    hv.measurable (hg.sub hg').measurable hd.measurable
    (by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hg.sub hg').continuousOn
      exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩)
    (by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hd.continuousOn
      exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩)
    (fun y => (hv01 y).1) (hae.mono fun y hy => (hSv y hy).1) hi
    (fun n => by
      have hc : Continuous fun y => v y ^ (n + 1) * (g y - g' y) +
          ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y := by fun_prop
      rw [← (hmeas _ _ hc fun c y hy => ?_).2]
      · exact H n
      · rw [hgw c y hy, hgw' c y hy, hdw c y hy]
        ring)
  rw [p1, p2, p3, p4, (hmeas δ d hd hdw).2, ← key,
    setIntegral_congr_fun hSm hF, setIntegral_congr_fun hSm hF,
    setIntegral_congr_fun hSm hF, setIntegral_congr_fun hSm hF, e1, e2, ← integral_sub a1 a2,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

end GlobalTheory.CurveDens
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.density_inequality_log_one_sub_cosSq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∀ (κ κ' δ : AlgChart p σ 1 → CxPts p σ → ℝ), IsDens κ → IsDens κ' → IsDens δ → ∀ (v f : CxPts p σ → ℝ) (S : Set (CxPts p σ)), Continuous v → (∀ y, 0 ≤ v y ∧ v y ≤ 1) → IsOpen S → Sᶜ.Finite → (∀ y ∈ S, v y < 1 ∧ f y = Real.log (1 - v y) / 2) → IntegrableOn f S (part κ) → IntegrableOn f S (part fun c y => -κ c y) → IntegrableOn f S (part κ') → IntegrableOn f S (part fun c y => -κ' c y) → (∀ n : ℕ, total (fun c y => v y ^ (n + 1) * (κ c y - κ' c y) + (n + 1) * v y ^ n * (1 - v y) * δ c y) = 0) → 2 * ((∫ y in S, f y ∂(part κ) - ∫ y in S, f y ∂(part fun c y => -κ c y)) - (∫ y in S, f y ∂(part κ') - ∫ y in S, f y ∂(part fun c y => -κ' c y))) = total δ := by
  first | exact @GlobalTheory.CurveDens.green_sum | exact GlobalTheory.CurveDens.green_sum | (intros; apply GlobalTheory.CurveDens.green_sum <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_cosSq_angle_function : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (V L L' : X.Modules) (r : ℕ) (h : Met p σ V r) (l : L ⟶ V) (l' : L' ⟶ V), h.IsCInf → IsSubbundle l → IsSubbundle l' → IsVB L 1 → IsVB L' 1 → ∃ v : CxPts p σ → ℝ, IsCosSq h l l' v ∧ Continuous v ∧ ∀ y, 0 ≤ v y ∧ v y ≤ 1 := by
  first | exact @GlobalTheory.CurveDens.exists_isCosSq | exact GlobalTheory.CurveDens.exists_isCosSq | (intros; apply GlobalTheory.CurveDens.exists_isCosSq <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.CurveDens

theorem quotGram_pyth_rankTwo (G : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (hG : G.PosDef)
    (x : Fin 1 ⊕ Fin 1 → ℂ) (τ : ℂ) (v : Fin 1 → ℂ) (hv : v 0 = x (.inr 0)) :
    (form (quotGram G) v v).re * (form G (Sum.elim (fun _ => τ) 0) (Sum.elim (fun _ => τ) 0)).re =
      (form G x x).re * (form G (Sum.elim (fun _ => τ) 0) (Sum.elim (fun _ => τ) 0)).re -
        ‖form G x (Sum.elim (fun _ => τ) 0)‖ ^ 2 := by
  have hH := hG.isHermitian
  have h11 : G (.inl 0) (.inl 0) ≠ 0 := (hG.diag_pos (i := .inl 0)).ne'
  have hr : starRingEnd ℂ (G (.inl 0) (.inl 0)) = G (.inl 0) (.inl 0) := hH.apply _ _
  have h12 : G (.inl 0) (.inr 0) = starRingEnd ℂ (G (.inr 0) (.inl 0)) := (hH.apply _ _).symm
  have hinv : (G.toBlocks₁₁)⁻¹ 0 0 = (G (.inl 0) (.inl 0))⁻¹ := by
    rw [Matrix.inv_def, Matrix.det_unique, Matrix.adjugate_fin_one]
    simp [Matrix.toBlocks₁₁, Ring.inverse_eq_inv']
  obtain ⟨r, hr'⟩ : ∃ r : ℝ, G (.inl 0) (.inl 0) = r := ⟨_, (Complex.conj_eq_iff_re.1 hr).symm⟩
  simp only [form_eq_sum, Fintype.sum_sum_type, Finset.univ_unique,
    Finset.sum_singleton, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, map_zero, mul_zero, add_zero,
    quotGram, Matrix.sub_apply, Matrix.mul_apply, Matrix.toBlocks₂₂, Matrix.toBlocks₂₁,
    Matrix.toBlocks₁₂, Matrix.of_apply, Fin.default_eq_zero]
  rw [hinv, hv, h12]
  rw [hr'] at h11 ⊢
  generalize x (Sum.inl 0) = x₁ at ⊢
  generalize x (Sum.inr 0) = x₂ at ⊢
  generalize G (Sum.inr 0) (Sum.inl 0) = g at ⊢
  generalize G (Sum.inr 0) (Sum.inr 0) = d at ⊢
  have hr0 : (r : ℂ) ≠ 0 := h11
  have hB : τ * (r : ℂ) * starRingEnd ℂ τ + 0 * g * starRingEnd ℂ τ =
      ((r * Complex.normSq τ : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, ← Complex.mul_conj]; ring
  have hn (z : ℂ) : ‖z‖ ^ 2 = (z * starRingEnd ℂ z).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hB, Complex.ofReal_re, hn, ← Complex.re_mul_ofReal, ← Complex.re_mul_ofReal, ← Complex.sub_re]
  congr 1
  simp only [Complex.ofReal_mul, ← Complex.mul_conj, map_add, map_mul, Complex.conj_ofReal,
    Complex.conj_conj]
  field_simp
  ring

theorem quot_form_pyth_rankTwo : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    (S : ShortComplex X.Modules) (h : Met p σ S.X₂ (1 + 1)) (hS : S.ShortExact) (h₁ : IsVB S.X₁ 1)
    (h₃ : IsVB S.X₃ 1) (U : X.Opens) (t : Γ(S.X₁, U)) (w : Γ(S.X₂, U)),
    IsFrame (fun _ : Fin 1 => t) → ∀ y ∈ ptsIn p σ U,
      ((h.quot hS h₁ h₃).form (S.g.app U w) (S.g.app U w) y).re * (h.form (S.f.app U t) (S.f.app U t) y).re =
        (h.form w w y).re * (h.form (S.f.app U t) (S.f.app U t) y).re - ‖h.form w (S.f.app U t) y‖ ^ 2 := by
  intro k _ X p σ S h hS h₁ h₃ U t w _ y hy
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ y
  let u : Γ(S.X₂, U) → Fin 1 ⊕ Fin 1 → ℂ := fun s i => (a.mid hS).crd p σ s y (finSumFinEquiv i)
  have hform (s s' : Γ(S.X₂, U)) : h.form s s' y = form (h.gram a.frame y) (u s) (u s') := by
    rw [h.form_eq (a.mid hS) ha s s' hy, h.gram_frame hS a ha, form_eq_sum, form_eq_sum,
      ← finSumFinEquiv.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← finSumFinEquiv.sum_comp]
    rfl
  have hf : u (S.f.app U t) = Sum.elim (fun _ => a.sub.crd p σ t y 0) 0 := by
    funext i
    refine (congrFun ((a.mid hS).crd_app a.sub S.f t hy ha) (finSumFinEquiv i)).trans ?_
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_one]
    have e := a.crd_frame hS ha i (.inl 0)
    refine (congrArg (· * _) e).trans ?_
    rcases i with i | i <;> simp [Matrix.one_apply, Subsingleton.elim i 0]
  have hg : a.quot.crd p σ (S.g.app U w) y 0 = u w (.inr 0) := by
    refine (congrFun (a.quot.crd_app (a.mid hS) S.g w hy ha) 0).trans ?_
    have e₃ (b) : (a.mid hS).e (finSumFinEquiv b) = a.frame b := by simp [VBExt.AdaptedChart.mid]
    have e₁ : a.quot.crd p σ (S.g.app a.U (a.frame (.inl 0))) y = 0 := by
      rw [show S.g.app a.U (a.frame (.inl 0)) = 0 from congr(($(S.zero)).app a.U (a.e 0)),
        Chart.crd_zero]
    have e₂ : a.quot.crd p σ (S.g.app a.U (a.frame (.inr 0))) y = Pi.single 0 1 :=
      a.quot.crd_frame ha 0
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_one]
    refine (congrArg₂ (· + ·) (congrArg (· * _) (congrFun
        ((congrArg (fun t => a.quot.crd p σ (S.g.app a.U t) y) (e₃ _)).trans e₁) 0))
      (congrArg (· * _) (congrFun
        ((congrArg (fun t => a.quot.crd p σ (S.g.app a.U t) y) (e₃ _)).trans e₂) 0))).trans ?_
    simp [u]
  have hq : (h.quot hS h₁ h₃).form (S.g.app U w) (S.g.app U w) y =
      form (quotGram (h.gram a.frame y)) (a.quot.crd p σ (S.g.app U w) y)
        (a.quot.crd p σ (S.g.app U w) y) := by
    rw [(h.quot hS h₁ h₃).form_eq a.quot ha _ _ hy, h.quot_G hS h₁ h₃ a ha]
  rw [hq, hform, hform, hform, hf]
  exact quotGram_pyth_rankTwo _ (h.posDef_gram_frame hS a ha) _ _ _ hg

end GlobalTheory.CurveDens
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_metric_norm_product_formula : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (S : ShortComplex X.Modules) (h : Met p σ S.X₂ (1 + 1)) (hS : S.ShortExact) (h₁ : IsVB S.X₁ 1) (h₃ : IsVB S.X₃ 1) (U : X.Opens) (t : Γ(S.X₁, U)) (w : Γ(S.X₂, U)), IsFrame (fun _ : Fin 1 => t) → ∀ y ∈ ptsIn p σ U, ((h.quot hS h₁ h₃).form (S.g.app U w) (S.g.app U w) y).re * (h.form (S.f.app U t) (S.f.app U t) y).re = (h.form w w y).re * (h.form (S.f.app U t) (S.f.app U t) y).re - ‖h.form w (S.f.app U t) y‖ ^ 2 := by
  atlas_forward_decl GlobalTheory.CurveDens.quot_form_pyth_rankTwo
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineHomSec

variable {X : Scheme.{0}} {F Q : X.Modules} {U V W : X.Opens}

theorem eq_repr_smul (c : Chart F 1) (h : W ≤ c.U) (x : Γ(F, W)) :
    x = (c.isFrame.basis h).repr x 0 • resM F h (c.e 0) := by
  have := (c.isFrame.basis h).sum_repr x
  rw [Fin.sum_univ_one, IsFrame.basis_apply] at this
  exact this.symm

theorem smul_cancel (c : Chart F 1) (h : W ≤ c.U) {a b : Γ(X, W)}
    (e : a • resM F h (c.e 0) = b • resM F h (c.e 0)) : a = b := by
  rw [← c.isFrame.basis_apply h] at e
  have := congrArg (fun x => (c.isFrame.basis h).repr x 0) e
  simpa only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] using this

theorem resM_frame (c c' : Chart F 1) (h : W ≤ c.U) (h' : W ≤ c'.U) :
    resM F h' (c'.e 0) = resG X (le_inf h h') ((det F 1).g c c').val • resM F h (c.e 0) := by
  have e : ((det F 1).g c c').val = (c.isFrame.basis (inf_le_left : c.U ⊓ c'.U ≤ c.U)).repr
      (resM F inf_le_right (c'.e 0)) 0 := by
    refine (c.isFrame.val_detUnit c'.isFrame inf_le_left inf_le_right).trans ?_
    rw [Module.Basis.det_apply, Matrix.det_fin_one, Module.Basis.toMatrix_apply]
  have := congrArg (resM F (le_inf h h'))
    (eq_repr_smul c (inf_le_left : c.U ⊓ c'.U ≤ c.U) (resM F inf_le_right (c'.e 0)))
  rw [resM_smul, resM_resM, resM_resM] at this
  rw [e]
  exact this

variable (s : F ⟶ Q)

def coef (c' : Chart F 1) (c : Chart Q 1) : Γ(X, c'.U ⊓ c.U) :=
  (c.isFrame.basis inf_le_right).repr (resM Q inf_le_left (s.app c'.U (c'.e 0))) 0

theorem app_frame (c' : Chart F 1) (c : Chart Q 1) (h' : W ≤ c'.U) (h : W ≤ c.U) :
    s.app W (resM F h' (c'.e 0)) = resG X (le_inf h' h) (coef s c' c) • resM Q h (c.e 0) := by
  have := congrArg (resM Q (le_inf h' h))
    (eq_repr_smul c (inf_le_right : c'.U ⊓ c.U ≤ c.U) (resM Q inf_le_left (s.app c'.U (c'.e 0))))
  rw [resM_smul, resM_resM, resM_resM] at this
  rw [app_resM]
  exact this

theorem coef_trans (c' d' : Chart F 1) (c d : Chart Q 1) (h' : W ≤ c'.U) (h : W ≤ c.U)
    (k' : W ≤ d'.U) (k : W ≤ d.U) :
    resG X (le_inf h' k') ((det F 1).g c' d').val * resG X (le_inf h' h) (coef s c' c) =
      resG X (le_inf h k) ((det Q 1).g c d).val * resG X (le_inf k' k) (coef s d' d) := by
  have e := app_frame s d' d k' k
  rw [resM_frame c' d' h' k', resM_frame c d h k, Scheme.Modules.Hom.app_smul,
    app_frame s c' c h' h, smul_smul, smul_smul] at e
  rw [smul_cancel c h e, mul_comm]

def sec : (CechPic.tens (CechPic.dual (det F 1)) (det Q 1)).Sec where
  f i := coef s i.1 i.2
  compat i j := by
    have e := coef_trans s (W := (i.1.U ⊓ i.2.U) ⊓ (j.1.U ⊓ j.2.U)) i.1 j.1 i.2 j.2
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)
    have h : (i.1.U ⊓ i.2.U) ⊓ (j.1.U ⊓ j.2.U) ≤ i.1.U ⊓ j.1.U := inf_le_inf inf_le_left inf_le_left
    exact ((res h ((det F 1).g i.1 j.1)).eq_inv_mul_iff_mul_eq.2 e).trans (mul_assoc _ _ _).symm

theorem eq_zero_of_coef (hF : IsVB F 1) (hQ : IsVB Q 1)
    (H : ∀ (c' : Chart F 1) (c : Chart Q 1) (z : X), z ∈ c'.U ⊓ c.U → coef s c' c = 0) : s = 0 := by
  ext V x
  choose U' e' hU' he' using hF
  choose U e hU he using hQ
  refine TopCat.Sheaf.eq_of_locally_eq' (C := Ab) ⟨Q.presheaf, Q.isSheaf⟩
    (fun z : V => V ⊓ (U' z ⊓ U z)) V (fun z => homOfLE inf_le_left)
    (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hz, hU' z, hU z⟩) (s.app V x) 0 fun z => ?_
  have h' : V ⊓ (U' z ⊓ U z) ≤ U' z := inf_le_right.trans inf_le_left
  have h : V ⊓ (U' z ⊓ U z) ≤ U z := inf_le_right.trans inf_le_right
  change resM Q inf_le_left (s.app V x) = resM Q inf_le_left 0
  rw [map_zero, ← app_resM, eq_repr_smul ⟨_, _, he' z⟩ h' (resM F _ x),
    Scheme.Modules.Hom.app_smul, app_frame s ⟨_, _, he' z⟩ ⟨_, _, he z⟩ h' h,
    H ⟨_, _, he' z⟩ ⟨_, _, he z⟩ z ⟨hU' z, hU z⟩, RingHom.map_zero, zero_smul, smul_zero]

theorem genericPoint_mem [IsIntegral X] (hF : IsVB F 1) (hQ : IsVB Q 1) (hs : s ≠ 0) :
    genericPoint X ∈ nonzeroLocus (sec s) := by
  by_contra hn
  refine hs (eq_zero_of_coef s hF hQ fun c' c z hz => ?_)
  have h := mt (mem_nonzeroLocus_iff (sec s) (c', c) (gen_mem hz)).2 hn
  refine basicOpen_eq_bot_iff (coef s c' c) |>.1 ?_
  by_contra hb
  obtain ⟨w, hw⟩ := (Opens.ne_bot_iff_nonempty _).1 hb
  exact h (gen_mem hw)

theorem vanishesAt (hF : IsVB F 1) {z : X} (hz : z ∉ nonzeroLocus (sec s)) : VanishesAt s z := by
  intro U t e b hU he hb hzb
  obtain ⟨U', e', hU', he'⟩ := hF z
  let c' : Chart F 1 := ⟨_, _, he'⟩
  let c : Chart Q 1 := ⟨_, _, he⟩
  have hm : z ∈ c'.U ⊓ c.U := ⟨hU', hU⟩
  refine hz ((mem_nonzeroLocus_iff (sec s) (c', c) hm).2 ?_)
  have h' : c'.U ⊓ c.U ≤ c'.U := inf_le_left
  have h : c'.U ⊓ c.U ≤ c.U := inf_le_right
  have e₁ := congrArg (resM Q h) hb
  rw [← app_resM, eq_repr_smul c' h' (resM F _ t), Scheme.Modules.Hom.app_smul,
    app_frame s c' c h' h, LB.resG_self, smul_smul, resM_smul] at e₁
  have e₂ := smul_cancel c h e₁
  have : z ∈ X.basicOpen (resG X h b) := by
    have := X.basicOpen_res b (homOfLE h).op
    exact this.ge ⟨hm, hzb⟩
  rw [← e₂, Scheme.basicOpen_mul] at this
  exact this.2

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem form_app (h : Met p σ Q 1) (c' : Chart F 1) (c : Chart Q 1) {y : CxPts p σ}
    (hy' : y ∈ ptsIn p σ c'.U) (hy : y ∈ ptsIn p σ c.U) :
    (h.form (s.app c'.U (c'.e 0)) (s.app c'.U (c'.e 0)) y).re =
      ‖ev p σ _ (coef s c' c) y‖ ^ 2 * (h.G c y).det.re := by
  have hW := mem_ptsIn_inf.2 ⟨hy', hy⟩
  rw [← h.form_resM _ _ inf_le_left hW, ← app_resM, app_frame s c' c inf_le_left inf_le_right,
    LB.resG_self, h.form_smul_left, ← h.conj_form, h.form_smul_left, map_mul, h.conj_form,
    h.form_resM _ _ _ hW, h.form_frame c hy, ← mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul,
    Complex.normSq_eq_norm_sq, Matrix.det_fin_one]

theorem exists_ratSec : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (F Q : X.Modules) (g' : VMetric p F 1) (g : VMetric p Q 1) (H' : g'.IsCInf) (H : g.IsCInf) (s : F ⟶ Q), s ≠ 0 → ∃ (r : ((VMetric.det H').dual.tens (VMetric.det H)).B.ι → X.functionFieldˣ) (hr : IsRatSec ((VMetric.det H').dual.tens (VMetric.det H)).B r), (∀ z ∈ (((VMetric.det H').dual.tens (VMetric.det H)).div hr).supp, VanishesAt s z) ∧ ∀ σ : k →+* ℂ, ∀ y ∈ offSupp p σ (((VMetric.det H').dual.tens (VMetric.det H)).div hr), ∀ (U : X.Opens) (t : Γ(F, U)), IsFrame (fun _ : Fin 1 => t) → y ∈ ptsIn p σ U → 0 < ((g.met σ).form (s.app U t) (s.app U t) y).re ∧ logNorm (((VMetric.det H').dual.tens (VMetric.det H)).φ σ) r y = Real.log (((g.met σ).form (s.app U t) (s.app U t) y).re / ((g'.met σ).form t t y).re) / 2 := by
  intro k _ X p _ F Q g' g H' H s hs
  have hξ := genericPoint_mem s g'.isVB g.isVB hs
  let M := (VMetric.det H').dual.tens (VMetric.det H)
  let u : M.B.Sec := sec s
  refine ⟨ratOfSec u hξ, isRatSec_ratOfSec u hξ,
    fun z hz => vanishesAt s g'.isVB fun h => notMem_supp_divOfSec.2 h hz, ?_⟩
  intro σ y hy U t ht hU
  have hy' : y ∈ ptsIn p σ (nonzeroLocus u) := (offSupp_divOfSec (hL := M.isLB) (hs := hξ)).le hy
  let c' : Chart F 1 := ⟨_, _, ht⟩
  let c := g.isVB.pick y
  have hc : y ∈ ptsIn p σ c.U := g.isVB.mem_pick y
  have hi : y ∈ ptsIn p σ (M.B.U (c', c)) := mem_ptsIn_inf.2 ⟨hU, hc⟩
  have h0 : ev p σ _ (coef s c' c) y ≠ 0 := (secVal_ne_zero_iff u hi).2 hy'
  have hG := det_re_pos ((g.met σ).posDef c y hc)
  have hG' := det_re_pos ((g'.met σ).posDef c' y hU)
  have e : ((g.met σ).form (s.app U t) (s.app U t) y).re = _ := form_app s (g.met σ) c' c hU hc
  have e' : (g'.met σ).form t t y = ((g'.met σ).G c' y).det :=
    ((g'.met σ).form_frame c' hU 0 0).trans (Matrix.det_fin_one _).symm
  refine ⟨e ▸ by positivity, ?_⟩
  refine (logNorm_ratOfSec (s := u) (hs := hξ) (M.φ σ) hy').trans ?_
  rw [(M.φ σ).nsq_eq (secVal_mem u) hi, e, e']
  congr 2
  change ‖ev p σ _ (coef s c' c) y‖ ^ 2 * Real.exp (-(-(-Real.log ((g'.met σ).G c' y).det.re) +
    -Real.log ((g.met σ).G c y).det.re)) = _
  rw [neg_neg, ← sub_eq_add_neg, neg_sub, Real.exp_sub, Real.exp_log hG, Real.exp_log hG', mul_div_assoc]

end GlobalTheory.LineHomSec
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ratSec_det_dual_tensor_support : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (F Q : X.Modules) (g' : VMetric p F 1) (g : VMetric p Q 1) (H' : g'.IsCInf) (H : g.IsCInf) (s : F ⟶ Q), s ≠ 0 → ∃ (r : ((VMetric.det H').dual.tens (VMetric.det H)).B.ι → X.functionFieldˣ) (hr : IsRatSec ((VMetric.det H').dual.tens (VMetric.det H)).B r), (∀ z ∈ (((VMetric.det H').dual.tens (VMetric.det H)).div hr).supp, VanishesAt s z) ∧ ∀ σ : k →+* ℂ, ∀ y ∈ offSupp p σ (((VMetric.det H').dual.tens (VMetric.det H)).div hr), ∀ (U : X.Opens) (t : Γ(F, U)), IsFrame (fun _ : Fin 1 => t) → y ∈ ptsIn p σ U → 0 < ((g.met σ).form (s.app U t) (s.app U t) y).re ∧ logNorm (((VMetric.det H').dual.tens (VMetric.det H)).φ σ) r y = Real.log (((g.met σ).form (s.app U t) (s.app U t) y).re / ((g'.met σ).form t t y).re) / 2 := by
  first | exact @GlobalTheory.LineHomSec.exists_ratSec | exact GlobalTheory.LineHomSec.exists_ratSec | (intros; apply GlobalTheory.LineHomSec.exists_ratSec <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_of_equal_sublines_shortExact : ∀ (X : Scheme.{0}) (V L Q L' Q' : X.Modules) (l : L ⟶ V) (m : V ⟶ Q) (w : l ≫ m = 0) (l' : L' ⟶ V) (m' : V ⟶ Q') (w' : l' ≫ m' = 0), (ShortComplex.mk l m w).ShortExact → (ShortComplex.mk l' m' w').ShortExact → IsVB Q 1 → IsVB Q' 1 → l' ≫ m = 0 → ∃ e : L' ≅ L, e.hom ≫ l = l' := by
  first | exact @GlobalTheory.SameLine.eq_line | exact GlobalTheory.SameLine.eq_line | (intros; apply GlobalTheory.SameLine.eq_line <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_metric_shortExact_isometric : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (S : ShortComplex X.Modules) (r s : ℕ) (h : VMetric p S.X₂ (r + s)) (H : h.IsCInf) (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (hf : IsSubbundle S.f), ((VMetric.det (H.restrict hf h₁)).tens (VMetric.det (H.quot hS h₁ h₃))).Isometric (VMetric.det H) := by
  first | exact @GlobalTheory.VMetric.isometric_det_tens_det | exact GlobalTheory.VMetric.isometric_det_tens_det | (intros; apply GlobalTheory.VMetric.isometric_det_tens_det <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_metric_isometric_of_isometry : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E E' : X.Modules) (r : ℕ) (h : VMetric p E r) (h' : VMetric p E' r) (H : h.IsCInf) (H' : h'.IsCInf) (φ : E ≅ E'), h.IsIsometry h' φ → (VMetric.det H).Isometric (VMetric.det H') := by
  first | exact @GlobalTheory.CurveDens.det_isometric_of_isIsometry | exact GlobalTheory.CurveDens.det_isometric_of_isIsometry | (intros; apply GlobalTheory.CurveDens.det_isometric_of_isIsometry <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_metric_shortExact_iso_isometric : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (S S' : ShortComplex X.Modules) (r s : ℕ) (h : VMetric p S.X₂ (r + s)) (h' : VMetric p S'.X₂ (r + s)) (H : h.IsCInf) (H' : h'.IsCInf) (hS : S.ShortExact) (hS' : S'.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (h₁' : IsVB S'.X₁ r) (h₃' : IsVB S'.X₃ s) (e₁ : S.X₁ ≅ S'.X₁) (e₂ : S.X₂ ≅ S'.X₂), e₁.hom ≫ S'.f = S.f ≫ e₂.hom → h.IsIsometry h' e₂ → (VMetric.det (H.quot hS h₁ h₃)).Isometric (VMetric.det (H'.quot hS' h₁' h₃')) ∧ h.bcInt hS h₁ h₃ = h'.bcInt hS' h₁' h₃' := by
  first | exact @GlobalTheory.isometric_detQuot_and_bcInt_eq_of_iso | exact GlobalTheory.isometric_detQuot_and_bcInt_eq_of_iso | (intros; apply GlobalTheory.isometric_detQuot_and_bcInt_eq_of_iso <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shortExact_of_composition : ∀ (X : Scheme.{0}) (A M B L Q V : X.Modules) (f : A ⟶ M) (g : M ⟶ B) (u : A ⟶ B) (q₀ : M ⟶ L) (q₁ : B ⟶ Q) (q₂ : B ⟶ V) (w₀ : f ≫ q₀ = 0) (w₁ : g ≫ q₁ = 0) (w₂ : u ≫ q₂ = 0) (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact) (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact), f ≫ g = u → ∃ (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0), (ShortComplex.mk l m w₃).ShortExact ∧ q₀ ≫ l = g ≫ q₂ ∧ q₂ ≫ m = q₁ := by
  first | exact @GlobalTheory.ThirdIso.modules | exact GlobalTheory.ThirdIso.modules | (intros; apply GlobalTheory.ThirdIso.modules <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortExact_composition_compatibility : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (A M B L Q V : X.Modules) (f : A ⟶ M) (g : M ⟶ B) (u : A ⟶ B) (q₀ : M ⟶ L) (q₁ : B ⟶ Q) (q₂ : B ⟶ V) (w₀ : f ≫ q₀ = 0) (w₁ : g ≫ q₁ = 0) (w₂ : u ≫ q₂ = 0) (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact) (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0) (hS₃ : (ShortComplex.mk l m w₃).ShortExact) (n : ℕ) (hA : IsVB A n) (hM : IsVB M (n + 1)) (hL : IsVB L 1) (hQ : IsVB Q 1) (hV : IsVB V (1 + 1)) (hg : IsSubbundle g) (h : Met p σ B (n + 1 + 1)), f ≫ g = u → q₀ ≫ l = g ≫ q₂ → q₂ ≫ m = q₁ → ∀ hl : IsSubbundle l, (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV).restrict hl hL = Met.quot (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL ∧ Met.quot (S := ShortComplex.mk l m w₃) (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ = Met.quot (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ := by
  first | exact @GlobalTheory.MetStage.metStages | exact GlobalTheory.MetStage.metStages | (intros; apply GlobalTheory.MetStage.metStages <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.AdjFlag

open GlobalTheory.ArInt

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem height_eq {D : ℕ} (hX : IsArithVar p D) {L M : HermLB p} {h h' : X → ℝ}
    (H : L.IsArithHeight h) (H' : M.IsArithHeight h') {Z : Scheme.{0}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] (e : (L.restr i).Isometric (M.restr i)) :
    h (i (genericPoint Z)) = h' (i (genericPoint Z)) := by
  rcases hX.vertical_or_horizontal i with ⟨ℓ, _, ⟨_⟩⟩ | ⟨hc, d, hd⟩
  · obtain ⟨d, hd⟩ := hX.exists_dim_eq i
    have ⟨w, hw, _⟩ := e
    have e' : topSelfIntersection (ZMod ℓ) (L.B.pull i) d = topSelfIntersection (ZMod ℓ) (M.B.pull i) d :=
      interNum_congr_lbIso _ _ (fun _ => (L.restr i).isLB) (fun _ => (M.restr i).isLB)
        fun _ => ⟨w, hw⟩
    rw [H.vertical Z i (ZMod ℓ) d hd, H'.vertical Z i (ZMod ℓ) d hd, e']
  · have hZ := hX.of_isClosedImmersion i hc hd
    exact (e.isSelfInter hZ (H.isSelfInter_restrict hX i rfl)).unique hZ
      (H'.isSelfInter_restrict hX i rfl)

theorem selfInter_sub [IsIntegral X] [IsLocallyNoetherian X] (hC : Published.ArCalc)
    (hX : IsArithVar p 1) {L Q L' Q' : HermLB p} (e : (L.tens Q).Isometric (L'.tens Q'))
    {x y x' y' a a' : ℝ} (hx : L.IsSelfInter x) (hy : Q.IsSelfInter y) (hx' : L'.IsSelfInter x')
    (hy' : Q'.IsSelfInter y') (ha : (L'.dual.tens Q).IsInter L a)
    (ha' : (L'.dual.tens Q).IsInter L' a') : x + y - x' - y' = -2 * (a - a') := by
  let T : Fin 3 → HermLB p := ![L, Q, L']
  obtain ⟨Ψ, hΨ⟩ := ((hC.arExists k X p 1 hX).2 (Fin 3) T).1
  have e' : L.icls + Q.icls = L'.icls + Q'.icls := HermLB.icls_eq_iff.2 e
  have c₀ : (comb T ![1, 0, 0]).Isometric L := HermLB.icls_eq_iff.1 (by
    simp [icls_comb, Fin.sum_univ_three, T])
  have c₁ : (comb T ![0, 1, 0]).Isometric Q := HermLB.icls_eq_iff.1 (by
    simp [icls_comb, Fin.sum_univ_three, T])
  have c₂ : (comb T ![0, 0, 1]).Isometric L' := HermLB.icls_eq_iff.1 (by
    simp [icls_comb, Fin.sum_univ_three, T])
  have c₃ : (comb T ![1, 1, -1]).Isometric Q' := HermLB.icls_eq_iff.1 (by
    simp [icls_comb, Fin.sum_univ_three, T, e'])
  have c₄ : (comb T ![0, 1, -1]).Isometric (L'.dual.tens Q) := HermLB.icls_eq_iff.1 (by
    simp [icls_comb, Fin.sum_univ_three, T, HermLB.icls_tens, HermLB.icls_dual, add_comm])
  have I₀ := HermLB.isInter_of_comb hC.arExists hC.arMix hC.arIso hX hΨ c₄ c₀
  have I₂ := HermLB.isInter_of_comb hC.arExists hC.arMix hC.arIso hX hΨ c₄ c₂
  rw [hx.unique hX (c₀.isSelfInter hX (hΨ.1 _)), hy.unique hX (c₁.isSelfInter hX (hΨ.1 _)),
    hx'.unique hX (c₂.isSelfInter hX (hΨ.1 _)), hy'.unique hX (c₃.isSelfInter hX (hΨ.1 _)),
    ha.unique hX I₀, ha'.unique hX I₂, neg_mul, two_mul, ← map_add, ← map_sub, ← map_sub,
    ← map_sub, ← map_add, ← map_neg]
  congr 1
  simp [lin, Fin.sum_univ_three]
  ring

section Dens

variable [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)]
  {ρ ρ' : AlgChart p σ 1 → CxPts p σ → ℝ}

theorem total_add_sub (hR : Nonempty (AnRead p σ 1)) (h : IsDens ρ) (h' : IsDens ρ') :
    total (fun c y => ρ c y + ρ' c y) = total ρ + total ρ' ∧
      total (fun c y => ρ c y - ρ' c y) = total ρ - total ρ' := by
  obtain ⟨ν, w, _, -, h₁, h₂⟩ := T.finite_measure_density_exists k X p σ hR
  obtain ⟨g, hg, e⟩ := h₁ ρ h
  obtain ⟨g', hg', e'⟩ := h₁ ρ' h'
  have i := hg.integrable_of_hasCompactSupport (μ := ν) (HasCompactSupport.of_compactSpace _)
  have i' := hg'.integrable_of_hasCompactSupport (μ := ν) (HasCompactSupport.of_compactSpace _)
  rw [(h₂ ρ g hg e).2, (h₂ ρ' g' hg' e').2, ← integral_add i i', ← integral_sub i i']
  exact ⟨(h₂ _ _ (hg.add hg') fun c y hy => by rw [e c y hy, e' c y hy, Pi.add_apply, add_mul]).2,
    (h₂ _ _ (hg.sub hg') fun c y hy => by rw [e c y hy, e' c y hy, Pi.sub_apply, sub_mul]).2⟩

end Dens

theorem form_frame_pos {L : X.Modules} (g : Met p σ L 1) {U : X.Opens} {t : Γ(L, U)}
    (ht : IsFrame fun _ : Fin 1 => t) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    0 < (g.form t t y).re := by
  have := g.form_frame ⟨U, _, ht⟩ hy 0 0
  rw [show g.form t t y = _ from this]
  exact (Complex.pos_iff.1 ((g.posDef ⟨U, _, ht⟩ y hy).diag_pos)).1

theorem exists_frames {L L' : X.Modules} (hL : IsVB L 1) (hL' : IsVB L' 1) (y : CxPts p σ) :
    ∃ (U : X.Opens) (t : Γ(L, U)) (t' : Γ(L', U)), (IsFrame fun _ : Fin 1 => t) ∧
      (IsFrame fun _ : Fin 1 => t') ∧ y ∈ ptsIn p σ U := by
  have key {F : X.Modules} (c : Chart F 1) {U : X.Opens} (h : U ≤ c.U) :
      IsFrame fun _ : Fin 1 => Twist.resM F h (c.e 0) := fun V hV => by
    convert c.isFrame V (hV.trans h) using 3
    funext i
    rw [Twist.resM_resM, Subsingleton.elim i 0]
  exact ⟨_, _, _, key (hL.pick y) inf_le_left, key (hL'.pick y) inf_le_right,
    mem_ptsIn_inf.2 ⟨hL.mem_pick y, hL'.mem_pick y⟩⟩

section RankTwo

variable {V L Q L' Q' : X.Modules} {l : L ⟶ V} {m : V ⟶ Q} {w : l ≫ m = 0}
  {l' : L' ⟶ V} {m' : V ⟶ Q'} {w' : l' ≫ m' = 0} (hS : (ShortComplex.mk l m w).ShortExact)
  (hS' : (ShortComplex.mk l' m' w').ShortExact) (hL : IsVB L 1) (hQ : IsVB Q 1) (hL' : IsVB L' 1)
  (hQ' : IsVB Q' 1) (hl : IsSubbundle l) (hl' : IsSubbundle l')

include hl hl' hL' in

theorem div_eq_one_sub (h : Met p σ V (1 + 1)) {v : CxPts p σ → ℝ} (hv : IsCosSq h l l' v)
    {U : X.Opens} {t : Γ(L, U)} {t' : Γ(L', U)} (ht : IsFrame fun _ : Fin 1 => t)
    (ht' : IsFrame fun _ : Fin 1 => t') {y : CxPts p σ} (hU : y ∈ ptsIn p σ U) :
    ((Met.quot (S := .mk l m w) h hS hL hQ).form ((l' ≫ m).app U t') ((l' ≫ m).app U t') y).re /
      ((h.restrict hl' hL').form t' t' y).re = 1 - v y := by
  have p₁ := form_frame_pos (h.restrict hl hL) ht hU
  have p₂ := form_frame_pos (h.restrict hl' hL') ht' hU
  have p₃ : ((Met.quot (S := .mk l m w) h hS hL hQ).form ((l' ≫ m).app U t') ((l' ≫ m).app U t')
      y).re * (h.form (l.app U t) (l.app U t) y).re =
      (h.form (l'.app U t') (l'.app U t') y).re * (h.form (l.app U t) (l.app U t) y).re -
        ‖h.form (l'.app U t') (l.app U t) y‖ ^ 2 :=
    T.quotient_metric_norm_product_formula k X p σ (.mk l m w) h hS hL hQ U t (l'.app U t') ht y hU
  rw [div_eq_iff p₂.ne']
  rw [h.form_restrict hl hL t t hU] at p₁
  rw [h.form_restrict hl' hL' t' t' hU]
  refine mul_right_cancel₀ p₁.ne' (p₃.trans ?_)
  rw [hv U t t' y hU]
  ring

theorem green_log [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    [SecondCountableTopology (CxPts p σ)] (hR : Nonempty (AnRead p σ 1)) (h : Met p σ V (1 + 1))
    (H : h.IsCInf) {S : Set (CxPts p σ)} (ho : IsOpen S) (hf : Sᶜ.Finite) {f : CxPts p σ → ℝ}
    (hn : ∀ y ∈ S, ∀ (U : X.Opens) (t : Γ(L', U)), (IsFrame fun _ : Fin 1 => t) → y ∈ ptsIn p σ U →
      0 < ((Met.quot (S := .mk l m w) h hS hL hQ).form ((l' ≫ m).app U t) ((l' ≫ m).app U t) y).re ∧
      f y = Real.log (((Met.quot (S := .mk l m w) h hS hL hQ).form ((l' ≫ m).app U t)
        ((l' ≫ m).app U t) y).re / ((h.restrict hl' hL').form t t y).re) / 2)
    (j₁ : (h.restrict hl hL).detWeight.ChernIntegrableOn 1 S f)
    (j₂ : (h.restrict hl' hL').detWeight.ChernIntegrableOn 1 S f) :
    2 * ((h.restrict hl hL).detWeight.chernInt 1 S f - (h.restrict hl' hL').detWeight.chernInt 1 S f) =
      (Met.bcMeas (S := .mk l m w) h hS hL hQ Set.univ).toReal -
        (Met.bcMeas (S := .mk l' m' w') h hS' hL' hQ' Set.univ).toReal := by
  obtain ⟨v, hv, hc, hb⟩ := T.exists_continuous_cosSq_angle_function k X p σ V L L' _ h l l' H hl hl' hL hL'
  have d₁ := isDens_bcDens (S := .mk l m w) hS hL hQ H
  have d₂ := isDens_bcDens (S := .mk l' m' w') hS' hL' hQ' H
  rw [Weight.ChernIntegrableOn, (chernPart_eq _).1, (chernPart_eq _).2] at j₁ j₂
  rw [← total_bcDens (S := .mk l m w) hS hL hQ H,
    ← total_bcDens (S := .mk l' m' w') hS' hL' hQ' H, ← (total_add_sub hR d₁ d₂).2,
    Weight.chernInt, Weight.chernInt, (chernPart_eq _).1, (chernPart_eq _).2,
    (chernPart_eq _).1, (chernPart_eq _).2]
  refine T.density_inequality_log_one_sub_cosSq k X p σ hR _ _ _ ((T.chernDens_detWeight_eq_neg_levi_log k X p σ).1 _ _ (H.restrict hl hL).detWeight)
    ((T.chernDens_detWeight_eq_neg_levi_log k X p σ).1 _ _ (H.restrict hl' hL').detWeight) (d₁.sub d₂) v f S hc hb ho hf
    (fun y hy => ?_) j₁.1 j₁.2 j₂.1 j₂.2
    (T.line_pair_extension_cosSq_bound k X p σ hR V L Q L' Q' l m w l' m' w' hS hS' hL hQ hL' hQ' hl hl' h H v hv)
  obtain ⟨U, t, t', ht, ht', hU⟩ := exists_frames hL hL' y
  obtain ⟨n₁, n₂⟩ := hn y hy U t' ht' hU
  have e := div_eq_one_sub hS hL hQ hL' hl hl' h hv ht ht' hU
  have := div_pos n₁ (form_frame_pos (h.restrict hl' hL') ht' hU)
  rw [e] at this n₂
  exact ⟨by linarith, n₂⟩

variable [IsIntegral X] {h : VMetric p V (1 + 1)} (H : h.IsCInf)

theorem rank_two (hC : Published.ArCalc) (hX : IsRegSurf p) {x y x' y' : ℝ}
    (hx : (VMetric.det (H.restrict hl hL)).IsSelfInter x)
    (hy : (VMetric.det (VMetric.IsCInf.quot (S := .mk l m w) hS hL hQ H)).IsSelfInter y)
    (hx' : (VMetric.det (H.restrict hl' hL')).IsSelfInter x')
    (hy' : (VMetric.det (VMetric.IsCInf.quot (S := .mk l' m' w') hS' hL' hQ' H)).IsSelfInter y') :
    x + y - VMetric.bcInt (S := .mk l m w) h hS hL hQ =
      x' + y' - VMetric.bcInt (S := .mk l' m' w') h hS' hL' hQ' := by
  have hA := hX.toIsArithVar
  by_cases hs : l' ≫ m = 0
  · obtain ⟨e, he⟩ := T.iso_of_equal_sublines_shortExact X V L Q L' Q' l m w l' m' w' hS hS' hQ hQ' hs
    obtain ⟨e₁, e₂⟩ := T.det_metric_shortExact_iso_isometric k X p (.mk l' m' w') (.mk l m w) 1 1 h h H H hS' hS hL' hQ' hL hQ
      e (Iso.refl V) (he.trans (Category.comp_id _).symm) fun _ _ _ _ _ _ => rfl
    have e₃ := T.det_metric_isometric_of_isometry k X p L' L 1 (h.restrict hl' hL') (h.restrict hl hL) (H.restrict hl' hL')
      (H.restrict hl hL) e fun σ U s t y hy => by
        refine ((h.met σ).form_restrict hl hL _ _ hy).trans
          (Eq.trans ?_ ((h.met σ).form_restrict hl' hL' s t hy).symm)
        rw [← he]
        rfl
    rw [e₂, hx.unique hA (e₃.isSelfInter hA hx'), hy.unique hA (e₁.isSelfInter hA hy')]
  have := hA.isLocallyNoetherian
  have HQ := VMetric.IsCInf.quot (S := .mk l m w) hS hL hQ H
  obtain ⟨r, hr, hv, hn⟩ := T.exists_ratSec_det_dual_tensor_support k X p L' Q (h.restrict hl' hL')
    (VMetric.quot (S := .mk l m w) h hS hL hQ) (H.restrict hl' hL') HQ (l' ≫ m) hs
  have e₀ := fun a a' => selfInter_sub (a := a) (a' := a') hC hA
    ((T.det_metric_shortExact_isometric k X p (.mk l m w) 1 1 h H hS hL hQ hl).trans
      (T.det_metric_shortExact_isometric k X p (.mk l' m' w') 1 1 h H hS' hL' hQ' hl').symm) hx hy hx' hy'
  generalize (VMetric.det (H.restrict hl' hL')).dual.tens (VMetric.det HQ) = P at *
  obtain ⟨a, ha⟩ := (isInter_calculus hC k X p hA P P (VMetric.det (H.restrict hl hL))).1
  obtain ⟨a', ha'⟩ := (isInter_calculus hC k X p hA P P (VMetric.det (H.restrict hl' hL'))).1
  replace e₀ := e₀ a a' ha ha'
  obtain ⟨g, G, ha⟩ := ha
  obtain ⟨g', G', ha'⟩ := ha'
  obtain ⟨i₁, rfl⟩ := ha r hr
  obtain ⟨i₂, rfl⟩ := ha' r hr
  have e₁ : ∑ᶠ z, ((P.div hr).mult z : ℝ) * g z = ∑ᶠ z, ((P.div hr).mult z : ℝ) * g' z :=
    finsum_congr fun z => by
      by_cases hz : (P.div hr).mult z = 0
      · simp [hz]
      obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
      rw [height_eq hA G G' i (T.det_metric_restriction_vanishing_locus k X p V L Q L' l m w l' hS hQ hL hL' hl hl' h H Z i
        (hv _ (CartierDiv.mem_supp_of_mult_ne_zero hz)))]
  have key (σ : k →+* ℂ) :=
    have := hA.compactSpace σ
    have := CxPts.secondCountableTopology_of_isProjOver σ hA.isProjOver
    have := CxPts.t2Space_cxPts_of_isProjOver σ hA.isProjOver
    green_log hS hS' hL hQ hL' hQ' hl hl' ((RegGenSmooth.genSmooth_of_isRegSurf k X p hX).1 σ)
      (h.met σ) (H σ) (isOpen_offSupp (P.div hr))
      (SurfacePoints.finite_compl_ptsIn k X p hA _ (P.div hr).genericPoint_notMem_supp σ)
      (hn σ) (i₁ σ) (i₂ σ)
  have := hA.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have e₂ := Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) => key σ
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at e₂
  rw [HermLB.archInt, HermLB.archInt, finsum_eq_sum_of_fintype (α := k →+* ℂ),
    finsum_eq_sum_of_fintype (α := k →+* ℂ)] at e₀
  rw [VMetric.bcInt, VMetric.bcInt, finsum_eq_sum_of_fintype (α := k →+* ℂ),
    finsum_eq_sum_of_fintype (α := k →+* ℂ)]
  change 2 * (∑ σ, ((VMetric.det (H.restrict hl hL)).φ σ).chernInt 1 _ _ -
    ∑ σ, ((VMetric.det (H.restrict hl' hL')).φ σ).chernInt 1 _ _) = _ at e₂
  linarith

end RankTwo

theorem isSelfInter_congr [IsIntegral X] {E : X.Modules} {r : ℕ} {h h' : VMetric p E r} (e : h = h')
    {H : h.IsCInf} {H' : h'.IsCInf} {x : ℝ} (hx : (VMetric.det H').IsSelfInter x) :
    (VMetric.det H).IsSelfInter x := by
  subst e
  exact hx

section ThreeStep

variable [IsIntegral X] {A B V : X.Modules} {u : A ⟶ B} {q₂ : B ⟶ V} {w₂ : u ≫ q₂ = 0}
  (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) {n : ℕ} (hA : IsVB A n) (hV : IsVB V (1 + 1))
  {h : VMetric p B (n + 1 + 1)} (H : h.IsCInf)
  {M L Q : X.Modules} {f : A ⟶ M} {g : M ⟶ B} {q₀ : M ⟶ L} {q₁ : B ⟶ Q} {w₀ : f ≫ q₀ = 0}
  {w₁ : g ≫ q₁ = 0} (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact)
  (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact) (hM : IsVB M (n + 1)) (hL : IsVB L 1)
  (hQ : IsVB Q 1) (hg : IsSubbundle g)

omit [IsIntegral X] in
include H in

theorem three_step (hX : IsRegSurf p) (hu : f ≫ g = u) :
    ∃ (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0) (hS₃ : (ShortComplex.mk l m w₃).ShortExact)
      (hl : IsSubbundle l),
      (VMetric.quot (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV).restrict hl hL =
        VMetric.quot (S := .mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL ∧
      VMetric.quot (S := .mk l m w₃)
          (VMetric.quot (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ =
        VMetric.quot (S := .mk g q₁ w₁) h hS₁ hM hQ ∧
      VMetric.bcInt (S := .mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL +
          VMetric.bcInt (S := .mk g q₁ w₁) h hS₁ hM hQ =
        VMetric.bcInt (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV +
          VMetric.bcInt (S := .mk l m w₃)
            (VMetric.quot (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ := by
  obtain ⟨l, m, w₃, hS₃, e₁, e₂⟩ := T.exists_shortExact_of_composition X A M B L Q V f g u q₀ q₁ q₂ w₀ w₁ w₂ hS₀ hS₁ hS₂ hu
  have hl : IsSubbundle l := isSubbundle_of_shortExact hS₃ hQ
  have key (σ : k →+* ℂ) := T.shortExact_composition_compatibility k X p σ A M B L Q V f g u q₀ q₁ q₂ w₀ w₁ w₂ hS₀ hS₁ hS₂ l m
    w₃ hS₃ n hA hM hL hQ hV hg (h.met σ) hu e₁ e₂ hl
  refine ⟨l, m, w₃, hS₃, hl, VMetric.ext (funext fun σ => (key σ).1),
    VMetric.ext (funext fun σ => (key σ).2), ?_⟩
  have hX' := hX.toIsArithVar
  have := hX'.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  simp only [VMetric.bcInt, finsum_eq_sum_of_fintype, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have := hX'.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hX'.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver σ hX'.isProjOver
  have hR := (RegGenSmooth.genSmooth_of_isRegSurf k X p hX).1 σ
  have H₀ := (H σ).restrict hg hM
  have H₃ := Met.IsCInf.quot (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) hS₂ hA hV (H σ)
  have t₀ := total_bcDens (S := .mk f q₀ w₀) hS₀ hA hL H₀
  have t₁ := total_bcDens (S := .mk g q₁ w₁) hS₁ hM hQ (H σ)
  have t₂ := total_bcDens (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) hS₂ hA hV (H σ)
  have t₃ := total_bcDens (S := .mk l m w₃) hS₃ hL hQ H₃
  have s₁ := (total_add_sub hR (isDens_bcDens (S := .mk f q₀ w₀) hS₀ hA hL H₀)
    (isDens_bcDens (S := .mk g q₁ w₁) hS₁ hM hQ (H σ))).1
  have s₂ := (total_add_sub hR
    (isDens_bcDens (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) hS₂ hA hV (H σ))
    (isDens_bcDens (S := .mk l m w₃) hS₃ hL hQ H₃)).1
  rw [t₀, t₁] at s₁
  rw [t₂, t₃] at s₂
  exact s₁.symm.trans ((total_congr (T.shortExact_composition_metric_compat k X p σ A M B L Q V f g u q₀ q₁ q₂ w₀ w₁ w₂ hS₀ hS₁
    hS₂ l m w₃ hS₃ n hA hM hL hQ hV hg (h.met σ) hu e₁ e₂ (H σ))).trans s₂)

variable {M' L' Q' : X.Modules} {f' : A ⟶ M'} {g' : M' ⟶ B} {q₀' : M' ⟶ L'} {q₁' : B ⟶ Q'}
  {w₀' : f' ≫ q₀' = 0} {w₁' : g' ≫ q₁' = 0} (hS₀' : (ShortComplex.mk f' q₀' w₀').ShortExact)
  (hS₁' : (ShortComplex.mk g' q₁' w₁').ShortExact) (hM' : IsVB M' (n + 1)) (hL' : IsVB L' 1)
  (hQ' : IsVB Q' 1) (hg' : IsSubbundle g')

theorem two_steps (hC : Published.ArCalc) (hX : IsRegSurf p) (hu : f ≫ g = f' ≫ g') {x y x' y' : ℝ}
    (hx : (VMetric.det (VMetric.IsCInf.quot (S := .mk f q₀ w₀) hS₀ hA hL
      (H.restrict hg hM))).IsSelfInter x)
    (hy : (VMetric.det (VMetric.IsCInf.quot (S := .mk g q₁ w₁) hS₁ hM hQ H)).IsSelfInter y)
    (hx' : (VMetric.det (VMetric.IsCInf.quot (S := .mk f' q₀' w₀') hS₀' hA hL'
      (H.restrict hg' hM'))).IsSelfInter x')
    (hy' : (VMetric.det (VMetric.IsCInf.quot (S := .mk g' q₁' w₁') hS₁' hM' hQ' H)).IsSelfInter y') :
    x + y - (VMetric.bcInt (S := .mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL +
        VMetric.bcInt (S := .mk g q₁ w₁) h hS₁ hM hQ) =
      x' + y' - (VMetric.bcInt (S := .mk f' q₀' w₀') (h.restrict hg' hM') hS₀' hA hL' +
        VMetric.bcInt (S := .mk g' q₁' w₁') h hS₁' hM' hQ') := by
  have m₀ : Mono f := hS₀.mono_f
  have m₁ : Mono g := hS₁.mono_f
  have hS₂ : (ShortComplex.mk (f ≫ g) _ (Limits.cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  have hV : IsVB (Limits.cokernel (f ≫ g)) (1 + 1) := by
    obtain ⟨l, m, w₃, hS₃, -⟩ := T.exists_shortExact_of_composition X A M B L Q _ f g _ q₀ q₁ _ w₀ w₁ _ hS₀ hS₁ hS₂ rfl
    exact (VBExt.isVB_and_cls_det_of_shortExact X _ 1 1 hS₃ hL hQ).1
  obtain ⟨l, m, w₃, hS₃, hl, e₁, e₂, e₃⟩ := three_step hS₂ hA hV H hS₀ hS₁ hM hL hQ hg hX rfl
  obtain ⟨l', m', w₃', hS₃', hl', e₁', e₂', e₃'⟩ :=
    three_step hS₂ hA hV H hS₀' hS₁' hM' hL' hQ' hg' hX hu.symm
  have HV := VMetric.IsCInf.quot (S := .mk (f ≫ g) _ (Limits.cokernel.condition _)) (r := n)
    (s := 1 + 1) hS₂ hA hV H
  have aux {a a' b c c' d d' : ℝ} (e : d = b + c) (e' : d' = b + c') (k : a - c = a' - c') :
      a - d = a' - d' := by linarith
  exact aux e₃ e₃' (rank_two hS₃ hS₃' hL hQ hL' hQ' hl hl' HV hC hX (isSelfInter_congr e₁ hx)
    (isSelfInter_congr e₂ hy) (isSelfInter_congr e₁' hx') (isSelfInter_congr e₂' hy'))

end ThreeStep

section Flags

open VMetric

variable {E : X.Modules} {r : ℕ} {h : VMetric p E r} (H : h.IsCInf) {fl fl' : Vert.Flag E r}

noncomputable abbrev stepBc (h : VMetric p E r) (fl : Vert.Flag E r) (i : Fin r) : ℝ :=
  (h.stepMet fl i).bcInt (stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i)

theorem isIsometry_restrict {F F' : X.Modules} {s : ℕ} {i : F ⟶ E} {i' : F' ⟶ E}
    (hi : IsSubbundle i) (hi' : IsSubbundle i') (hF : IsVB F s) (hF' : IsVB F' s) (e : F ≅ F')
    (he : e.hom ≫ i' = i) : (h.restrict hi hF).IsIsometry (h.restrict hi' hF') e :=
  fun σ U s t y hy => by
    refine ((h.met σ).form_restrict hi' hF' _ _ hy).trans
      (Eq.trans ?_ ((h.met σ).form_restrict hi hF s t hy).symm)
    rw [← he]
    rfl

theorem step_eq {i : Fin r} (h₀ : fl.SameStep fl' i.castSucc) (h₁ : fl.SameStep fl' i.succ) :
    (grLB fl i H).Isometric (grLB fl' i H) ∧ stepBc h fl i = stepBc h fl' i := by
  obtain ⟨e₀, h₀⟩ := h₀
  obtain ⟨e₁, h₁⟩ := h₁
  refine T.det_metric_shortExact_iso_isometric k X p (stepSeq fl i) (stepSeq fl' i) i 1 (h.stepMet fl i) (h.stepMet fl' i)
    (H.restrict _ _) (H.restrict _ _) _ _ _ _ _ _ e₀ e₁ ?_ (isIsometry_restrict _ _ _ _ e₁ h₁)
  rw [← cancel_mono (fl'.ι i.succ)]
  simp only [Category.assoc, Vert.Flag.step_ι, h₀, h₁]

theorem mid_eq [IsIntegral X] (hC : Published.ArCalc) (hX : IsRegSurf p) {n : ℕ} (hn : n + 1 < r)
    (h₀ : fl.SameStep fl' (Fin.castSucc ⟨n, by omega⟩)) (h₂ : fl.SameStep fl' (Fin.succ ⟨n + 1, hn⟩))
    {x y x' y' : ℝ} (hx : (grLB fl ⟨n, by omega⟩ H).IsSelfInter x)
    (hy : (grLB fl ⟨n + 1, hn⟩ H).IsSelfInter y) (hx' : (grLB fl' ⟨n, by omega⟩ H).IsSelfInter x')
    (hy' : (grLB fl' ⟨n + 1, hn⟩ H).IsSelfInter y') :
    x + y - (stepBc h fl ⟨n, by omega⟩ + stepBc h fl ⟨n + 1, hn⟩) =
      x' + y' - (stepBc h fl' ⟨n, by omega⟩ + stepBc h fl' ⟨n + 1, hn⟩) := by
  have hA := hX.toIsArithVar
  set i₀ : Fin r := ⟨n, by omega⟩
  set i₁ : Fin r := ⟨n + 1, hn⟩
  obtain ⟨e₀, h₀⟩ := h₀
  obtain ⟨e₂, h₂⟩ := h₂
  let g : fl.F i₀.succ ⟶ fl.F i₁.succ := fl.step i₁
  let f' : fl.F i₀.castSucc ⟶ fl'.F i₀.succ := e₀.hom ≫ fl'.step i₀
  let g' : fl'.F i₀.succ ⟶ fl.F i₁.succ := fl'.step i₁ ≫ e₂.inv
  let q' : fl.F i₁.succ ⟶ fl'.gr i₁ := e₂.hom ≫ fl'.π i₁
  have w₀' : f' ≫ fl'.π i₀ = 0 := by
    simp only [f', Category.assoc]
    rw [show fl'.step i₀ ≫ fl'.π i₀ = 0 from Limits.cokernel.condition _, Limits.comp_zero]
  have w₁' : g' ≫ q' = 0 := by
    simp only [g', q', Category.assoc, Iso.inv_hom_id_assoc]
    exact Limits.cokernel.condition _
  have hS₀' : (ShortComplex.mk f' _ w₀').ShortExact :=
    ShortComplex.shortExact_of_iso (ShortComplex.isoMk (S₁ := stepSeq fl' i₀) e₀.symm (Iso.refl _) (Iso.refl _)
      (by simp [f']) (by simp)) (stepSeq_shortExact fl' i₀)
  have hS₁' : (ShortComplex.mk g' q' w₁').ShortExact :=
    ShortComplex.shortExact_of_iso (ShortComplex.isoMk (S₁ := stepSeq fl' i₁)
      (Iso.refl _) e₂.symm (Iso.refl _)
      (by simp [g']) (by simp [q'])) (stepSeq_shortExact fl' i₁)
  have hg : IsSubbundle g := isSubbundle_of_shortExact (stepSeq_shortExact fl i₁) (fl.isVB_gr i₁)
  have hg' : IsSubbundle g' := isSubbundle_of_shortExact hS₁' (fl'.isVB_gr i₁)
  have gι : g ≫ fl.ι i₁.succ = fl.ι i₀.succ := fl.step_ι i₁
  have gι' : g' ≫ fl.ι i₁.succ = fl'.ι i₀.succ := by
    rw [← h₂, Category.assoc, Iso.inv_hom_id_assoc]
    exact fl'.step_ι i₁
  have hu : fl.step i₀ ≫ g = f' ≫ g' := by
    rw [← cancel_mono (fl.ι i₁.succ), Category.assoc, Category.assoc, gι, gι', fl.step_ι,
      Category.assoc, fl'.step_ι, h₀]
  have HB : (h.stepMet fl i₁).IsCInf := H.restrict _ _
  have res {F : X.Modules} {a : F ⟶ fl.F i₁.succ} {b : F ⟶ E} (ha : IsSubbundle a)
      (hb : IsSubbundle b) (hF : IsVB F (n + 1)) (e : a ≫ fl.ι i₁.succ = b) :
      ((h.stepMet fl i₁).restrict ha hF).IsIsometry (h.restrict hb hF) (Iso.refl F) :=
    fun σ U s t y hy => by
      refine ((h.met σ).form_restrict hb hF _ _ hy).trans (Eq.trans ?_
        ((((h.stepMet fl i₁).met σ).form_restrict ha hF s t hy).trans
          ((h.met σ).form_restrict (fl.isSubbundle i₁.succ) (fl.isVB i₁.succ) _ _ hy)).symm)
      rw [← e]
      rfl
  obtain ⟨a₁, b₁⟩ := T.det_metric_shortExact_iso_isometric k X p (stepSeq fl i₀) (stepSeq fl i₀) n 1 _ (h.stepMet fl i₀)
    (HB.restrict hg (fl.isVB i₀.succ)) (H.restrict _ _) (stepSeq_shortExact fl i₀)
    (stepSeq_shortExact fl i₀) (fl.isVB i₀.castSucc) (fl.isVB_gr i₀) (fl.isVB i₀.castSucc)
    (fl.isVB_gr i₀) (Iso.refl _) (Iso.refl _) (by simp) (res hg _ _ gι)
  obtain ⟨a₂, b₂⟩ := T.det_metric_shortExact_iso_isometric k X p (.mk f' _ w₀') (stepSeq fl' i₀) n 1 _ (h.stepMet fl' i₀)
    (HB.restrict hg' (fl'.isVB i₀.succ)) (H.restrict _ _) hS₀'
    (stepSeq_shortExact fl' i₀) (fl.isVB i₀.castSucc) (fl'.isVB_gr i₀) (fl'.isVB i₀.castSucc)
    (fl'.isVB_gr i₀) e₀ (Iso.refl _) (Category.comp_id _).symm (res hg' _ _ gι')
  obtain ⟨a₃, b₃⟩ := T.det_metric_shortExact_iso_isometric k X p (.mk g' q' w₁') (stepSeq fl' i₁) (n + 1) 1 _ (h.stepMet fl' i₁)
    HB (H.restrict _ _) hS₁' (stepSeq_shortExact fl' i₁) (fl'.isVB i₀.succ) (fl'.isVB_gr i₁)
    (fl'.isVB i₁.castSucc) (fl'.isVB_gr i₁) (Iso.refl _) e₂ (by simp [g'])
    (isIsometry_restrict _ _ _ _ e₂ h₂)
  have key := two_steps (fl.isVB i₀.castSucc) HB (stepSeq_shortExact fl i₀)
    (stepSeq_shortExact fl i₁) (fl.isVB i₀.succ) (fl.isVB_gr i₀) (fl.isVB_gr i₁) hg hS₀' hS₁'
    (fl'.isVB i₀.succ) (fl'.isVB_gr i₀) (fl'.isVB_gr i₁) hg' hC hX hu
    (a₁.symm.isSelfInter hA hx) hy (a₂.symm.isSelfInter hA hx') (a₃.symm.isSelfInter hA hy')
  exact (congrArg (fun t => x + y - (t + stepBc h fl i₁)) b₁).symm.trans
    (key.trans (congrArg₂ (fun s t => x' + y' - (s + t)) b₂ b₃))

theorem sameStep_of_end {j : Fin (r + 1)} (hj : j = 0 ∨ j = Fin.last r) : fl.SameStep fl' j := by
  rcases hj with rfl | rfl
  · have z := isVB_zero_iff.1 (fl.isVB 0)
    exact ⟨z.iso (isVB_zero_iff.1 (fl'.isVB 0)), z.eq_of_src _ _⟩
  · have := fl.isIso_last
    have := fl'.isIso_last
    exact ⟨asIso (fl.ι _) ≪≫ (asIso (fl'.ι _)).symm, by simp⟩

end Flags

theorem isFlagCh2_eq_of_adjacent : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    (p : X ⟶ Sp k) [IsIntegral X], IsRegSurf p → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r)
    (H : h.IsCInf) (fl fl' : Vert.Flag E r), fl.Adjacent fl' → ∀ a b : ℝ,
    VMetric.IsFlagCh2 H fl a → VMetric.IsFlagCh2 H fl' b → a = b := by
  rintro hC k _ X p _ hX E r h H fl fl' ⟨j, hj⟩ _ _ ⟨-, x, hx, rfl⟩ ⟨-, x', hx', rfl⟩
  have hA := hX.toIsArithVar
  have same {i : Fin r} (h₀ : fl.SameStep fl' i.castSucc) (h₁ : fl.SameStep fl' i.succ) :
      x i - stepBc h fl i - (x' i - stepBc h fl' i) = 0 := by
    obtain ⟨e₁, e₂⟩ := step_eq H h₀ h₁
    rw [e₂, (e₁.isSelfInter hA (hx i)).unique hA (hx' i), sub_self]
  suffices e : ∑ i, (x i - stepBc h fl i - (x' i - stepBc h fl' i)) = 0 by
    simp only [Finset.sum_sub_distrib] at e
    rw [← Finset.sum_div, ← Finset.sum_div, VMetric.flagBc, VMetric.flagBc]
    linarith
  by_cases he : j = 0 ∨ j = Fin.last r
  · have all (i) : fl.SameStep fl' i := by
      by_cases hi : i = j
      · exact hi ▸ sameStep_of_end he
      · exact hj i hi
    exact Finset.sum_eq_zero fun i _ => same (all _) (all _)
  obtain ⟨_ | n, hn⟩ := j
  · exact absurd (.inl rfl) he
  have hn' : n + 1 < r := by
    have : n + 1 ≠ r := fun e => he (.inr (Fin.ext e))
    omega
  rw [Fintype.sum_eq_add (⟨n, by omega⟩ : Fin r) (⟨n + 1, hn'⟩ : Fin r) (by simp) fun i hi => same (i := i)
    (hj _ fun e => hi.2 (Fin.ext (congrArg Fin.val e :)))
    (hj _ fun e => hi.1 (Fin.ext (Nat.succ_injective (congrArg Fin.val e :))))]
  have := mid_eq H hC hX hn' (hj _ (by simp [Fin.ext_iff])) (hj _ (by simp [Fin.ext_iff]))
    (hx _) (hx _) (hx' _) (hx' _)
  linarith

end GlobalTheory.AdjFlag
end
