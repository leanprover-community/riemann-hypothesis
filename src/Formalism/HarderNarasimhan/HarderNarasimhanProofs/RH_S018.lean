import Mathlib
import Formalism.HarderNarasimhan.StatementFrameF
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FrameHermSharpB

/-!
S018 candidate, against the main-branch StatementFrameF and FrameHermSharpB.
No new axioms and no admitted proofs. NOT compiled in the authoring environment.
The finite-source bound and the scalar trace argument are separate from the
remaining geometric and integration obligations. This file does not prove
TheoremFRational, and does not replace FrameLA1 in the repository yet.
-/

open Finset Module NumberField
open Formalism.CorankShareLayerCake.FR
open scoped BigOperators

noncomputable section
namespace Formalism.HN.S018

/-- Finite layer-cake contribution of a single slope. -/
def clippedDeficit (s H x : ℝ) : ℝ := min H (max 0 (s - x))

/-- Denominator-free pointwise estimate, valid also at u = H = 0. -/
theorem clippedDeficit_mul_le (s u H x : ℝ)
    (hu : 0 ≤ u) (hH : 0 ≤ H) (hx : x ≤ s + u) :
    (u + H) * clippedDeficit s H x ≤ H * (s + u - x) := by
  unfold clippedDeficit
  by_cases hs : s ≤ x
  · rw [max_eq_left (by linarith : s - x ≤ 0), min_eq_right hH, mul_zero]
    exact mul_nonneg hH (by linarith)
  · have hp : 0 ≤ s - x := by linarith
    rw [max_eq_right hp]
    by_cases h : s - x ≤ H
    · rw [min_eq_right h]
      have hprod := mul_nonneg hu (show 0 ≤ H - (s - x) by linarith)
      nlinarith only [hprod]
    · rw [min_eq_left (le_of_not_ge h)]
      have hprod := mul_nonneg hH (show 0 ≤ s - x - H by linarith)
      nlinarith only [hprod]

/-- The source estimate in finite-sum form, without any logarithmic integral. -/
theorem source_sum_mul_le {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (s u H : ℝ) (hu : 0 ≤ u) (hH : 0 ≤ H)
    (hmean : (Fintype.card ι : ℝ) * s ≤ ∑ j, x j)
    (hmax : ∀ j, x j ≤ s + u) :
    (u + H) * (∑ j, clippedDeficit s H (x j)) ≤
      (Fintype.card ι : ℝ) * (u * H) := by
  classical
  calc
    (u + H) * (∑ j, clippedDeficit s H (x j)) =
        ∑ j, (u + H) * clippedDeficit s H (x j) := by rw [Finset.mul_sum]
    _ ≤ ∑ j, H * (s + u - x j) :=
        Finset.sum_le_sum fun j _ => clippedDeficit_mul_le s u H (x j) hu hH (hmax j)
    _ = H * ((Fintype.card ι : ℝ) * (s + u) - ∑ j, x j) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Fintype.card ι : ℝ) * (u * H) := by
        have haux := mul_nonneg hH (sub_nonneg.mpr hmean)
        nlinarith only [haux]

/-- Normalized truncated deficit. The degenerate case is handled explicitly. -/
theorem source_average_le {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (s u H : ℝ) (hu : 0 ≤ u) (hH : 0 ≤ H)
    (hn : 0 < Fintype.card ι)
    (hmean : (Fintype.card ι : ℝ) * s ≤ ∑ j, x j)
    (hmax : ∀ j, x j ≤ s + u) :
    (∑ j, clippedDeficit s H (x j)) / (Fintype.card ι : ℝ) ≤ u * H / (u + H) := by
  classical
  have hn' : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hn
  by_cases hzero : H = 0
  · subst H
    have hc : ∀ j, clippedDeficit s 0 (x j) = 0 := by
      intro j
      exact min_eq_left (le_max_left _ _)
    simp [hc]
  · have hden : 0 < u + H := by
      have : 0 < H := lt_of_le_of_ne hH (Ne.symm hzero)
      linarith
    apply (div_le_div_iff₀ hn' hden).2
    simpa [mul_comm] using source_sum_mul_le x s u H hu hH hmean hmax

/-- Rational loss is uniformly bounded by u, including at the origin. -/
theorem rational_le_u (u H : ℝ) (hu : 0 ≤ u) (hH : 0 ≤ H) :
    u * H / (u + H) ≤ u := by
  by_cases hz : u + H = 0
  · simp [hz, hu]
  · have hd : 0 < u + H := lt_of_le_of_ne (add_nonneg hu hH) (Ne.symm hz)
    apply (div_le_iff₀ hd).2
    nlinarith only [sq_nonneg u]

/-- Recover the old logarithmic loss via log y ≤ y - 1 at y = u/(u+H). -/
theorem rational_le_log (u H : ℝ) (hu : 0 ≤ u) (hH : 0 ≤ H) :
    u * H / (u + H) ≤ u * Real.log (1 + H / u) := by
  by_cases hz : u = 0
  · subst u
    simp
  · have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
    have hd : 0 < u + H := by linarith
    have hp : 0 < u / (u + H) := div_pos hup hd
    have hlog := Real.log_le_sub_one_of_pos hp
    rw [Real.log_div (ne_of_gt hup) (ne_of_gt hd)] at hlog
    have hrewrite : 1 + H / u = (u + H) / u := by field_simp [ne_of_gt hup] <;> ring
    rw [hrewrite, Real.log_div (ne_of_gt hd) (ne_of_gt hup)]
    have hone : u / (u + H) - 1 = -(H / (u + H)) := by field_simp [ne_of_gt hd] <;> ring
    rw [hone] at hlog
    have hmul := mul_le_mul_of_nonneg_left (show H / (u + H) ≤
        Real.log (u + H) - Real.log u by linarith) hu
    simpa [mul_div_assoc] using hmul

/-- Scalar end of the projection/trace proof. T = tr Q, A = tr(PQ).
The trace inequalities are hypotheses here, not assumed global axioms. -/
theorem trace_projection_bound (n D k T A ε η r : ℝ)
    (hn : 0 < n) (hD : 0 < D) (hT : 0 < T)
    (hε : 0 ≤ ε) (hη : 0 ≤ η) (hr : 0 ≤ r) (hr2 : r ≤ 1 / 2)
    (htrace : n * (1 - r) ≤ T) (hA : 0 ≤ A)
    (hsmall : A ≤ n * (ε + r))
    (hCS : (T - A)^2 * D ≤ (D - k) * (1 + η) * T^2) :
    k ≤ (η + 4 * ε + 4 * r) * D := by
  let θ : ℝ := A / T
  have hθT : θ * T = A := by dsimp [θ]; field_simp [ne_of_gt hT]
  have hθ0 : 0 ≤ θ := div_nonneg hA hT.le
  have hhalf : n / 2 ≤ T := by
    have hm := mul_nonneg hn.le (show 0 ≤ 1 / 2 - r by linarith)
    nlinarith only [hm, htrace]
  have hnle : n ≤ 2 * T := by linarith
  have hA' : A ≤ (2 * ε + 2 * r) * T := by
    have hm := mul_le_mul_of_nonneg_right hnle (add_nonneg hε hr)
    nlinarith only [hm, hsmall]
  have hθ : θ ≤ 2 * ε + 2 * r := by
    apply (le_of_mul_le_mul_right ?_ hT)
    rw [hθT]
    exact hA'
  have hfactor : T - A = (1 - θ) * T := by rw [← hθT]; ring
  rw [hfactor] at hCS
  have hT2 : 0 < T^2 := pow_pos hT _
  have hc : (1 - θ)^2 * D ≤ (D - k) * (1 + η) := by
    apply (le_of_mul_le_mul_right ?_ hT2)
    calc
      (1 - θ)^2 * D * T^2 = ((1 - θ) * T)^2 * D := by ring
      _ ≤ (D - k) * (1 + η) * T^2 := hCS
  by_cases hk : 0 ≤ k
  · have h1 := mul_nonneg hk hη
    have h2 := mul_nonneg hD.le (sq_nonneg θ)
    have h3 := mul_le_mul_of_nonneg_right hθ hD.le
    nlinarith only [hc, h1, h2, h3]
  · have hc0 : 0 ≤ η + 4 * ε + 4 * r := by linarith
    exact le_trans (le_of_not_ge hk) (mul_nonneg hc0 hD.le)

/-- The final algebraic integration step. The layer-cake and actual filter
bounds are explicit local hypotheses so their absence cannot be hidden. -/
theorem mean_of_integrated_corank (s u H e η δ μ A B : ℝ)
    (hδ : δ < 1)
    (hsource : A ≤ u * H / (u + H))
    (hcorank : (1 - δ) * B ≤ 4 * A + (η + 4 * Real.sqrt e) * H)
    (hmean : s - B ≤ μ) :
    s - (1 - δ)⁻¹ * (4 * (u * H / (u + H)) +
      (η + 4 * Real.sqrt e) * H) ≤ μ := by
  have hd : 0 < 1 - δ := by linarith
  have hB : B ≤ (4 * (u * H / (u + H)) +
      (η + 4 * Real.sqrt e) * H) / (1 - δ) := by
    apply (le_div_iff₀ hd).2
    nlinarith only [hsource, hcorank]
  rw [show (1 - δ)⁻¹ * (4 * (u * H / (u + H)) +
      (η + 4 * Real.sqrt e) * H) =
      (4 * (u * H / (u + H)) + (η + 4 * Real.sqrt e) * H) / (1 - δ) by
        rw [div_eq_mul_inv, mul_comm]]
  linarith

/-- Translate actual normalized slope counts to the existing hnStep rank.
This is one concrete interface to HN, not the full image-inclusion bridge. -/
theorem actual_slope_count {R V E : Type} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (ρ : V →+ E) (L : Submodule R V) (hL : IsLat ρ L) (a s t : ℝ) :
    ((univ.filter (fun j => 2 * slopeList ρ L j + a < s - t)).card : ℝ) =
      (rk ρ L : ℝ) - rk ρ (hnStep ρ L ((s - t - a) / 2)) := by
  classical
  have hfilter : (univ.filter (fun j => 2 * slopeList ρ L j + a < s - t)) =
      (univ.filter (fun j => slopeList ρ L j < (s - t - a) / 2)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h <;> linarith
  rw [hfilter]
  exact frameB_count_lt ρ L hL ((s - t - a) / 2)

end Formalism.HN.S018

namespace Formalism.HN.S018

/-- Same hypotheses as the repository's TheoremFSharp, with rational loss.
This is a proposition (the target), NOT a proof of that proposition. -/
def TheoremFRational : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K]
    [_root_.NumberField.IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, Module (𝓞 K) (V i)] [∀ i, IsScalarTower (𝓞 K) K (V i)]
    [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ) (s u HH e η δ : ℝ),
    (∀ w, IsUnit (X' w).det) → (∀ i w, IsUnit (X i w).det) → (∀ i, IsUnit (Y i).det) →
    IsUnit Y'.det →
    cc.FG → Submodule.span K (cc : Set W) = ⊤ →
    (∀ i, (N i).FG) → (∀ i, Submodule.span K (N i : Set (V i)) = ⊤) →
    0 < ∑ i, Fintype.card (ι i) → (∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ cc) →
    (∀ i, B i ≠ 0 → htMap (b i) (X i) b' X' (B i) ≤ h i) →
    s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
      ∑ i, (Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - h i) →
    0 ≤ u → (∀ i, muMaxDef (b i) (X i) (N i) - h i ≤ s + u) →
    s - muMinDef b' X' cc ≤ HH → 0 ≤ HH →
    0 ≤ δ → δ < 1 → (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ) →
    (∀ i (k : κ) (j : ι i),
      Ball i (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) k j) →
    (∀ i, 0 < γ i) →
    (∑ i, hs2 (frK (γ i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ) →
    0 ≤ e → e ≤ 1 / 4 →
    (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ γ (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
         frQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ^ 2 /
        (Fintype.card (κ ⊕ κ₁) : ℝ) →
    0 ≤ η →
    s - (1 - δ)⁻¹ * (4 * (u * HH / (u + HH)) + (η + 4 * Real.sqrt e) * HH) ≤ muDef b' X' cc

/-- Conditional recovery: once the strengthened proposition is proved,
its logarithmic predecessor is obtained without changing any assumptions. -/
theorem rational_implies_sharp (hR : TheoremFRational) : TheoremFSharp := by
  unfold TheoremFSharp
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _
  intro b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ
  intro hX' hX hY hY' hcc hccspan hN hNspan hdim hmap hheight hmean
    hu hmax hmin hHH hδ0 hδ1 hdimδ hBall hγ hHS he0 he1 htr hη
  have hnew := hR K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ s u HH e η δ
    hX' hX hY hY' hcc hccspan hN hNspan hdim hmap hheight hmean hu hmax hmin hHH
    hδ0 hδ1 hdimδ hBall hγ hHS he0 he1 htr hη
  have hmono := rational_le_log u HH hu hHH
  have hinv : 0 ≤ (1 - δ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hterm : 4 * (u * HH / (u + HH)) + (η + 4 * Real.sqrt e) * HH ≤
      4 * u * Real.log (1 + HH / u) + (η + 4 * Real.sqrt e) * HH := by linarith
  have hweighted := mul_le_mul_of_nonneg_left hterm hinv
  linarith

end Formalism.HN.S018

namespace Formalism.HN.S018

open MeasureTheory

/-- Integration of the pointwise corank inequality. This is independent of
the geometric proof that the pointwise inequality holds for HN filtrations. -/
theorem integrate_corank (α β : ℝ → ℝ) (H η e δ : ℝ)
    (hH : 0 ≤ H)
    (hα : IntervalIntegrable α volume 0 H)
    (hβ : IntervalIntegrable β volume 0 H)
    (hpoint : ∀ t ∈ Set.Icc (0 : ℝ) H,
      (1 - δ) * β t ≤ 4 * α t + (η + 4 * Real.sqrt e)) :
    (1 - δ) * (∫ t in (0 : ℝ)..H, β t) ≤
      4 * (∫ t in (0 : ℝ)..H, α t) + (η + 4 * Real.sqrt e) * H := by
  have hα4 : IntervalIntegrable (fun t => 4 * α t) volume 0 H := hα.const_mul 4
  have hβδ : IntervalIntegrable (fun t => (1 - δ) * β t) volume 0 H :=
    hβ.const_mul (1 - δ)
  have hc : IntervalIntegrable (fun _ : ℝ => η + 4 * Real.sqrt e) volume 0 H :=
    intervalIntegrable_const
  have hI := intervalIntegral.integral_mono_on hH hβδ (hα4.add hc) hpoint
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hα4 hc,
    intervalIntegral.integral_const_mul] at hI
  simpa [mul_comm] using hI

/-- Conditional finite-model assembly: the remaining hypotheses describe
exactly the two layer-cake links and the geometric corank bridge. -/
theorem finite_model_mean {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (α β : ℝ → ℝ) (s u H e η δ μ : ℝ)
    (hu : 0 ≤ u) (hH : 0 ≤ H) (hn : 0 < Fintype.card ι)
    (hδ : δ < 1)
    (hmean : (Fintype.card ι : ℝ) * s ≤ ∑ j, x j)
    (hmax : ∀ j, x j ≤ s + u)
    (hα : IntervalIntegrable α volume 0 H)
    (hβ : IntervalIntegrable β volume 0 H)
    (hsourceCake : (∫ t in (0 : ℝ)..H, α t) =
      (∑ j, clippedDeficit s H (x j)) / (Fintype.card ι : ℝ))
    (hpoint : ∀ t ∈ Set.Icc (0 : ℝ) H,
      (1 - δ) * β t ≤ 4 * α t + (η + 4 * Real.sqrt e))
    (htargetCake : s - (∫ t in (0 : ℝ)..H, β t) ≤ μ) :
    s - (1 - δ)⁻¹ * (4 * (u * H / (u + H)) +
      (η + 4 * Real.sqrt e) * H) ≤ μ := by
  apply mean_of_integrated_corank s u H e η δ μ
    (∫ t in (0 : ℝ)..H, α t) (∫ t in (0 : ℝ)..H, β t) hδ
  · rw [hsourceCake]
    exact source_average_le x s u H hu hH hn hmean hmax
  · exact integrate_corank α β H η e δ hH hα hβ hpoint
  · exact htargetCake

end Formalism.HN.S018
