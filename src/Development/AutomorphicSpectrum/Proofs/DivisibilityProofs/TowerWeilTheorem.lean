import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.WeilBound.CoreStatements.FlagImmersions.LinearRootPowerLipschitz
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelLogIntegralFormulaStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RationalWeightIntegralCoeffs
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CurveDegreeLinearNefCone
import Development.WeilBound.CoreStatements.FlagImmersions.TowerRationalWeightBound
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelArithIntersectionFormulaStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelPointHeightDegree
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelCurveDegreeNefStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelSemipositiveConj
import Development.WeilBound.CoreStatements.FlagImmersions.PerturbedWeightWallBounds
import Development.WeilBound.CoreStatements.FlagImmersions.FlagDegLeGap
import Development.WeilBound.CoreStatements.FlagImmersions.ContinuousBoundWallExtension

section
section
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem linA_pow_continuous_lipschitz : ∀ (Ψ : Type) [Fintype Ψ] (N d : ℕ), (∀ Φ : RPA Ψ N →ₗ[ℝ] ℝ, Continuous fun z : Wt Ψ N × ℝ => Φ (linA z.1 z.2 ^ d)) ∧ (∀ lam : Wt Ψ N, linA lam 0 = toA (linRoot lam)) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (b : ℝ), (∀ m, |Φ (monomial m 1)| ≤ b) → ∀ (lam mu : Wt Ψ N) (s s' : ℝ), ‖lam‖ ≤ 1 → ‖mu‖ ≤ 1 → |s| ≤ 1 → |s'| ≤ 1 → |Φ (linA lam s ^ d) - Φ (linA mu s' ^ d)| ≤ C * b * (‖lam - mu‖ + |s - s'|) :=
  @RootFieldNumerics.linear_root_power_lipschitz

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_functional_lipschitz_weights : ∀ (Ψ : Type) [Fintype Ψ] (N d : ℕ), (∀ Φ : RPA Ψ N →ₗ[ℝ] ℝ, Continuous fun z : Wt Ψ N × ℝ => Φ (linA z.1 z.2 ^ d)) ∧ (∀ lam : Wt Ψ N, linA lam 0 = toA (linRoot lam)) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (b : ℝ), (∀ m, |Φ (monomial m 1)| ≤ b) → ∀ (lam mu : Wt Ψ N) (s s' : ℝ), ‖lam‖ ≤ 1 → ‖mu‖ ≤ 1 → |s| ≤ 1 → |s'| ≤ 1 → |Φ (linA lam s ^ d) - Φ (linA mu s' ^ d)| ≤ C * b * (‖lam - mu‖ + |s - s'|) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.linA_pow_continuous_lipschitz
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem deg_bounds : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.Proportional → T.I7 → ∀ (B : ℕ) (c : T.Comp) (lam : Wt Ψ N) (s : ℚ), IsRatWt lam → 0 ≤ s → Dominant lam → Dominant (T.lamS lam s) → 0 ≤ T.mDeg B c lam s ∧ T.mDeg B c lam s ≤ T.vol c * flagDeg lam :=
  RootFieldNumerics.tower_rational_weight_bound

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_component_height_bound : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.Proportional → T.I7 → ∀ (B : ℕ) (c : T.Comp) (lam : Wt Ψ N) (s : ℚ), IsRatWt lam → 0 ≤ s → Dominant lam → Dominant (T.lamS lam s) → 0 ≤ T.mDeg B c lam s ∧ T.mDeg B c lam s ≤ T.vol c * flagDeg lam := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.deg_bounds
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem zhang_lower_bound_root_model : SuccessiveMinimaLowerBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ), IsRatWt lam →
      M.Semipos t lam s → M.NefFib lam s → (∀ W, M.IsPt W → e ≤ M.ht II t lam s W) →
      ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) ≤
        M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) := by
  intro hZ1 II hII Ψ _ N M t lam s e hrat hsemi hnef hpts
  obtain ⟨q, n, hq, hn⟩ := GlobalTheory.T.rational_weight_integral_coeffs Ψ N M lam s hrat
  have hp := GlobalTheory.T.root_model_semipositive_conj Ψ N M t lam s q n hn hsemi
  have hnf := (GlobalTheory.T.root_model_curve_degree_nef Ψ N M t lam s q n hn).2 hnef
  have hW : ∀ W, IsArithVar W 1 → M.P ≤ W →
      ((q : ℝ) * e) * degC W ≤ II M.K M.ι W 1 ![combLine (M.line t) n] := by
    intro W h1 h2
    have hpt : M.IsPt W := ⟨h1, h2⟩
    obtain ⟨hd, hI⟩ := GlobalTheory.T.root_model_point_height_degree II hII Ψ N M t lam s q n W hn hpt
    rw [hI]
    have hq' : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hd' : (0 : ℝ) ≤ degC W := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpts W hpt) hq') hd'
  have key := hZ1 M.K M.ι M.P M.P (dimFl Ψ N) (combLine (M.line t) n) ((q : ℝ) * e) II hII.1 M.arith le_rfl
    hp.1 hnf hp.2 hW
  have hgeo : geomDeg M.P (combLine (M.line t) n) (dimFl Ψ N) =
      (M.δ : ℝ) * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N) := by
    have := GlobalTheory.T.root_model_log_integral_formula II hII Ψ N M t (fun _ => lam) (fun _ => (s : ℝ)) q (fun _ => n) (fun _ j => hn j)
    simpa [geomDeg, Finset.prod_const] using this
  rw [hgeo, GlobalTheory.T.root_model_arith_intersection_formula II hII Ψ N M t lam s q n hn] at key
  have hδ : (0 : ℝ) < M.δ := by exact_mod_cast M.δ_pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : (0 : ℝ) < (M.δ : ℝ) * (q : ℝ) ^ (dimFl Ψ N + 1) := by positivity
  refine le_of_mul_le_mul_left ?_ hc
  calc (M.δ : ℝ) * (q : ℝ) ^ (dimFl Ψ N + 1) * (((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N))
      = ((dimFl Ψ N + 1 : ℕ) : ℝ) * ((q : ℝ) * e) *
          ((M.δ : ℝ) * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N)) := by
        push_cast; ring
    _ ≤ _ := key

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zhang_lower_bound_rational : SuccessiveMinimaLowerBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ), IsRatWt lam → M.Semipos t lam s → M.NefFib lam s → (∀ W, M.IsPt W → e ≤ M.ht II t lam s W) → ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) ≤ M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.zhang_lower_bound_root_model
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem zhang_upper_bound_root_model : SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ) (F : Set (Ideal (MRing M.ι))), IsRatWt lam → M.Semipos t lam s → M.NefFib lam s → IsZariskiDense M.P F → (∀ W ∈ F, M.IsPt W ∧ M.ht II t lam s W ≤ e) → M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) ≤ ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) := by
  intro hZ II hII Ψ _ N M t lam s e F hrat hsp hnef hF hpt
  obtain ⟨q, n, hq, hn⟩ := GlobalTheory.T.rational_weight_integral_coeffs Ψ N M lam s hrat
  have hsemi := GlobalTheory.T.root_model_semipositive_conj Ψ N M t lam s q n hn hsp
  have hnf := (GlobalTheory.T.root_model_curve_degree_nef Ψ N M t lam s q n hn).2 hnef
  have hA := GlobalTheory.T.root_model_arith_intersection_formula II hII Ψ N M t lam s q n hn
  have hG := GlobalTheory.T.root_model_log_integral_formula II hII Ψ N M t (fun _ => lam) (fun _ => (s : ℝ)) q (fun _ => n)
    (fun _ j => hn j)
  have hGeo : geomDeg M.P (combLine (M.line t) n) (dimFl Ψ N) =
      M.δ * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N) := by
    have hprod : (∏ _k : Fin (dimFl Ψ N), linA lam (s : ℝ)) = linA lam s ^ dimFl Ψ N := by
      simp
    rw [hprod] at hG
    exact hG
  have key := hZ M.K M.ι M.P M.P (dimFl Ψ N) (combLine (M.line t) n) ((q : ℝ) * e) F II hII.1
    M.arith le_rfl hsemi.1 hnf hsemi.2
    (by
      intro W hW
      obtain ⟨hp, hle⟩ := hpt W hW
      obtain ⟨-, hI⟩ := GlobalTheory.T.root_model_point_height_degree II hII Ψ N M t lam s q n W hn hp
      refine ⟨hp.1, hp.2, ?_⟩
      rw [hI]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg q))
        (Nat.cast_nonneg _))
    hF
  rw [hA, hGeo] at key
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hδ : (0 : ℝ) < M.δ := Nat.cast_pos.mpr M.δ_pos
  have hpos : (0 : ℝ) < M.δ * (q : ℝ) ^ (dimFl Ψ N + 1) := mul_pos hδ (pow_pos hqR _)
  refine le_of_mul_le_mul_left ?_ hpos
  calc _ ≤ _ := key
    _ = _ := by push_cast; ring

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zhang_upper_bound_dense_points : SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ) (F : Set (Ideal (MRing M.ι))), IsRatWt lam → M.Semipos t lam s → M.NefFib lam s → IsZariskiDense M.P F → (∀ W ∈ F, M.IsPt W ∧ M.ht II t lam s W ≤ e) → M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) ≤ ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.zhang_upper_bound_root_model
end

section
section
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem l1_le_card_mul_of_norm_le_one {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam : Wt Ψ N) (h : ‖lam‖ ≤ 1) :
    l1 lam ≤ (Fintype.card Ψ : ℝ) * N := by
  have hb : ∀ τ i, |lam τ i| ≤ 1 := fun τ i => by
    have h1 : ‖lam τ‖ ≤ ‖lam‖ := norm_le_pi_norm lam τ
    have h2 : ‖lam τ i‖ ≤ ‖lam τ‖ := norm_le_pi_norm (lam τ) i
    rw [← Real.norm_eq_abs]; linarith
  unfold l1
  calc ∑ τ, ∑ i, |lam τ i| ≤ ∑ _τ : Ψ, ∑ _i : Fin N, (1 : ℝ) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => hb τ i
    _ = (Fintype.card Ψ : ℝ) * N := by simp

theorem RootTower.isRatWt_lamS {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : RootTower Ψ N) {lam : Wt Ψ N}
    (s : ℚ) (h : IsRatWt lam) : IsRatWt (T.lamS lam s) := by
  intro τ i
  obtain ⟨q1, h1⟩ := h τ i
  obtain ⟨q2, h2⟩ := T.nu_rat τ i
  refine ⟨q1 - s * q2, ?_⟩
  simp only [RootTower.lamS, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, h2]
  push_cast; ring

theorem mbarTop_squeeze : SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.I3 → T.I5 II → T.I6 II →
    ∀ c₀ > (0 : ℝ), ∃ θ₀ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℕ, 2 ≤ B → ∀ (c : T.Comp) (lam : Wt Ψ N) (θ : ℝ) (s : ℚ),
      IsRatWt lam → ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (s : ℝ) = θ ^ 2 → (∀ τ, θ ≤ gap T.j lam τ) →
      CompactGapsGE T.j c₀ lam → Dominant (T.lamS lam s) → NefThreshold T.j B (T.lamS lam s) →
      0 ≤ T.mDeg B c lam s →
      |T.mbarTop II B c lam s| ≤ C * Real.log (B / (s : ℝ)) * T.mDeg B c lam s := by
  intro hZ1 hZ2 II hII Ψ _ _ N T hI3 hI5 hI6 c₀ hc₀
  obtain ⟨s₀, hs₀, h3⟩ := hI3 ((Fintype.card Ψ : ℝ) * N)
  obtain ⟨θ₅, hθ₅, C₅, h5⟩ := hI5 c₀ hc₀
  obtain ⟨θ₆, hθ₆, C₆, h6⟩ := hI6 c₀ hc₀
  have hD : (0 : ℝ) ≤ (dimFl Ψ N : ℝ) + 1 := by positivity
  refine ⟨min (min θ₅ θ₆) (min 1 s₀), lt_min (lt_min hθ₅ hθ₆) (lt_min one_pos hs₀),
    ((dimFl Ψ N : ℝ) + 1) * (max C₅ 0 + max C₆ 0),
    mul_nonneg hD (add_nonneg (le_max_right _ _) (le_max_right _ _)), ?_⟩
  intro B hB c lam θ s hrat hnorm hθ hθ₀ hs hgap hcg hdom hnef hdeg
  have hθ1 : θ ≤ 1 := le_trans hθ₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hθs : θ ≤ s₀ := le_trans hθ₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hθ5 : θ ≤ θ₅ := le_trans hθ₀ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hθ6 : θ ≤ θ₆ := le_trans hθ₀ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hspos : (0 : ℝ) < s := by rw [hs]; positivity
  have hs1 : (s : ℝ) ≤ 1 := by rw [hs]; nlinarith
  have hss₀ : (s : ℝ) ≤ s₀ := by rw [hs]; nlinarith
  have hl1 : l1 lam ≤ (Fintype.card Ψ : ℝ) * N := l1_le_card_mul_of_norm_le_one lam hnorm
  obtain ⟨hNef, hSemi⟩ := h3 B hB c lam (s : ℝ) hl1 hspos hss₀ hdom hnef
  have hrat' : IsRatWt (T.lamS lam s) := RootTower.isRatWt_lamS T s hrat
  have hlow := h5 B hB c lam θ s hrat hnorm hθ hθ5 hs hgap hcg
  obtain ⟨F, hF, hFpt⟩ := h6 B hB c lam θ s hrat hnorm hθ hθ6 hs hgap hcg
  have hL : ((dimFl Ψ N : ℝ) + 1) * (-(C₅ * Real.log (B / (s : ℝ)))) * T.mDeg B c lam s ≤
      T.mbarTop II B c lam s :=
    GlobalTheory.T.zhang_lower_bound_rational hZ1 II hII Ψ N (T.M B c) (scale s) (T.lamS lam s) s (-(C₅ * Real.log (B / (s : ℝ))))
      hrat' hSemi hNef (fun W hW => hlow W hW)
  have hU : T.mbarTop II B c lam s ≤
      ((dimFl Ψ N : ℝ) + 1) * (C₆ * Real.log B) * T.mDeg B c lam s :=
    GlobalTheory.T.zhang_upper_bound_dense_points hZ2 II hII Ψ N (T.M B c) (scale s) (T.lamS lam s) s (C₆ * Real.log B) F
      hrat' hSemi hNef hF (fun W hW => hFpt W hW)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B))
  have hlogBs : Real.log B ≤ Real.log (B / (s : ℝ)) :=
    Real.log_le_log hBpos (by rw [le_div_iff₀ hspos]; nlinarith)
  have hLg : 0 ≤ Real.log (B / (s : ℝ)) := le_trans hlogB hlogBs
  have hP : 0 ≤ ((dimFl Ψ N : ℝ) + 1) * Real.log (B / (s : ℝ)) * T.mDeg B c lam s :=
    mul_nonneg (mul_nonneg hD hLg) hdeg
  have hQ : 0 ≤ ((dimFl Ψ N : ℝ) + 1) * Real.log B * T.mDeg B c lam s :=
    mul_nonneg (mul_nonneg hD hlogB) hdeg
  have hQP : ((dimFl Ψ N : ℝ) + 1) * Real.log B * T.mDeg B c lam s ≤
      ((dimFl Ψ N : ℝ) + 1) * Real.log (B / (s : ℝ)) * T.mDeg B c lam s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogBs hD) hdeg
  have k1 := mul_le_mul_of_nonneg_right
    (show C₅ ≤ max C₅ 0 + max C₆ 0 by linarith [le_max_left C₅ 0, le_max_right C₆ 0]) hP
  have k2 := mul_le_mul_of_nonneg_right (le_max_left C₆ 0) hQ
  have k3 := mul_le_mul_of_nonneg_left hQP (le_max_right C₆ 0)
  have k4 := mul_le_mul_of_nonneg_right
    (show max C₆ 0 ≤ max C₅ 0 + max C₆ 0 by linarith [le_max_right C₅ 0]) hP
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

end GlobalTheory.CompanionTheory.Ar.Top
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_gap_height_uniform_bound : SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.I3 → T.I5 II → T.I6 II → ∀ c₀ > (0 : ℝ), ∃ θ₀ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℕ, 2 ≤ B → ∀ (c : T.Comp) (lam : Wt Ψ N) (θ : ℝ) (s : ℚ), IsRatWt lam → ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (s : ℝ) = θ ^ 2 → (∀ τ, θ ≤ gap T.j lam τ) → CompactGapsGE T.j c₀ lam → Dominant (T.lamS lam s) → NefThreshold T.j B (T.lamS lam s) → 0 ≤ T.mDeg B c lam s → |T.mbarTop II B c lam s| ≤ C * Real.log (B / (s : ℝ)) * T.mDeg B c lam s := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.mbarTop_squeeze
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem hypotheses_hold_for_large_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (c₀ θ₀ : ℝ), 0 < c₀ → 0 < θ₀ → ∃ B₁ : ℕ, ∀ B : ℕ, B₁ ≤ B → ∀ (τ₀ : Ψ) (lam₀ : Wt Ψ N), InWall T.j τ₀ c₀ lam₀ → let θ : ℝ := 5 * Fintype.card Ψ / B; let lam : Wt Ψ N := fun τ i => lam₀ τ i + (if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0); 3 ≤ B ∧ 0 < θ ∧ θ ≤ θ₀ ∧ θ ≤ 1 ∧ ‖lam‖ ≤ 1 ∧ ‖T.lamS lam (θ ^ 2)‖ ≤ 1 ∧ (∀ τ, θ ≤ gap T.j lam τ) ∧ gap T.j lam τ₀ = 2 * θ ∧ CompactGapsGE T.j c₀ lam ∧ Dominant lam ∧ Dominant (T.lamS lam (θ ^ 2)) ∧ NefThreshold T.j B (T.lamS lam (θ ^ 2)) ∧ ‖T.lamS lam (θ ^ 2) - lam₀‖ ≤ 2 * θ + ‖T.nu‖ * θ ^ 2 :=
  @RootFieldNumerics.perturbed_weight_wall_bounds

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perturbed_weight_gap_bounds : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (c₀ θ₀ : ℝ), 0 < c₀ → 0 < θ₀ → ∃ B₁ : ℕ, ∀ B : ℕ, B₁ ≤ B → ∀ (τ₀ : Ψ) (lam₀ : Wt Ψ N), InWall T.j τ₀ c₀ lam₀ → let θ : ℝ := 5 * Fintype.card Ψ / B; let lam : Wt Ψ N := fun τ i => lam₀ τ i + (if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0); 3 ≤ B ∧ 0 < θ ∧ θ ≤ θ₀ ∧ θ ≤ 1 ∧ ‖lam‖ ≤ 1 ∧ ‖T.lamS lam (θ ^ 2)‖ ≤ 1 ∧ (∀ τ, θ ≤ gap T.j lam τ) ∧ gap T.j lam τ₀ = 2 * θ ∧ CompactGapsGE T.j c₀ lam ∧ Dominant lam ∧ Dominant (T.lamS lam (θ ^ 2)) ∧ NefThreshold T.j B (T.lamS lam (θ ^ 2)) ∧ ‖T.lamS lam (θ ^ 2) - lam₀‖ ≤ 2 * θ + ‖T.nu‖ * θ ^ 2 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.hypotheses_hold_for_large_bound
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem flagDeg_le_mul_gap : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : Wt Ψ N) (τ₀ : Ψ), ‖lam‖ ≤ 1 → Dominant lam → flagDeg lam ≤ C * gap j lam τ₀ := by
  exact @RootFieldNumerics.flagDeg_le_gap

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_degree_le_gap : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : Wt Ψ N) (τ₀ : Ψ), ‖lam‖ ≤ 1 → Dominant lam → flagDeg lam ≤ C * gap j lam τ₀ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.flagDeg_le_mul_gap
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem rat_points_suffice_on_walls : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (c₀ b : ℝ) (τ₀ : Ψ) (Φ : Wt Ψ N → ℝ), 1 ≤ j → j < N → 0 < c₀ → Continuous Φ → (∀ lam, IsRatWt lam → InWall j τ₀ (c₀ / 2) lam → |Φ lam| ≤ b) → ∀ lam, InWall j τ₀ c₀ lam → |Φ lam| ≤ b :=
  @RootFieldNumerics.continuous_bound_wall_extension

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_wall_bound_extend : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (c₀ b : ℝ) (τ₀ : Ψ) (Φ : Wt Ψ N → ℝ), 1 ≤ j → j < N → 0 < c₀ → Continuous Φ → (∀ lam, IsRatWt lam → InWall j τ₀ (c₀ / 2) lam → |Φ lam| ≤ b) → ∀ lam, InWall j τ₀ c₀ lam → |Φ lam| ≤ b := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.rat_points_suffice_on_walls
end

section
section
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

namespace WallBound

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem l1_le_card_mul_of_norm_le_one' (lam : Wt Ψ N) (h : ‖lam‖ ≤ 1) : l1 lam ≤ (Fintype.card Ψ : ℝ) * N := by
  have hb : ∀ τ i, |lam τ i| ≤ 1 := fun τ i => by
    have h1 : ‖lam τ‖ ≤ ‖lam‖ := norm_le_pi_norm lam τ
    have h2 : ‖lam τ i‖ ≤ ‖lam τ‖ := norm_le_pi_norm (lam τ) i
    rw [Real.norm_eq_abs] at h2
    linarith
  unfold l1
  calc ∑ τ, ∑ i, |lam τ i| ≤ ∑ _τ : Ψ, ∑ _i : Fin N, (1 : ℝ) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => hb τ i
    _ = (Fintype.card Ψ : ℝ) * N := by simp

theorem toA_linRoot_pow (lam : Wt Ψ N) (d : ℕ) : toA (linRoot lam ^ d) = linA lam 0 ^ d := by
  simp [toA, linA, map_pow]

theorem continuous_lin_zero (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (d : ℕ)
    (h : Continuous fun z : Wt Ψ N × ℝ => Φ (linA z.1 z.2 ^ d)) :
    Continuous fun lam : Wt Ψ N => Φ (linA lam 0 ^ d) := by
  have hz : Continuous fun lam : Wt Ψ N => ((lam, (0 : ℝ)) : Wt Ψ N × ℝ) :=
    Continuous.prodMk continuous_id continuous_const
  have h2 := h.comp hz
  simp only [Function.comp_def] at h2
  exact h2

theorem continuous_PB (T : RootTower Ψ N) (II : IntersectionSystem) (B : ℕ) :
    Continuous fun lam : Wt Ψ N => T.PB II B lam := by
  obtain ⟨hcont, -, -⟩ := GlobalTheory.T.arith_functional_lipschitz_weights Ψ N (dimFl Ψ N + 1)
  have h : (fun lam : Wt Ψ N => T.PB II B lam) =
      fun lam => ∑ c, (T.M B c).PP II (linA lam 0 ^ (dimFl Ψ N + 1)) := by
    funext lam
    simp only [RootTower.PB, RootTower.PPt, RootTower.PPc, toA_linRoot_pow]
  rw [h]
  exact continuous_finset_sum _ fun c _ => continuous_lin_zero _ _ (hcont _)

theorem one_le_log {B : ℕ} (h : 3 ≤ B) : 1 ≤ Real.log B := by
  have hB : (3 : ℝ) ≤ B := by exact_mod_cast h
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem log_div_le {B : ℕ} (h : 3 ≤ B) (a : ℝ) (ha : 1 ≤ a) :
    Real.log (B / (a / B) ^ 2) ≤ 3 * Real.log B := by
  have hB : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have ha0 : 0 < a := by linarith
  have h1 : (B : ℝ) / (a / B) ^ 2 ≤ (B : ℝ) ^ 3 := by
    rw [div_pow, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ a ^ 2 := by nlinarith
    nlinarith [pow_pos hB 3]
  have h2 : 0 < (B : ℝ) / (a / B) ^ 2 := by positivity
  calc Real.log (B / (a / B) ^ 2) ≤ Real.log ((B : ℝ) ^ 3) := Real.log_le_log h2 h1
    _ = 3 * Real.log B := by rw [Real.log_pow]; norm_num

theorem three_terms {q a p cs c3 c2 cp c8 v n θ L Ls md dist s : ℝ} (hcs : 0 ≤ cs) (hc8 : 0 ≤ c8) (hcp : 0 ≤ cp)
    (hv : 0 ≤ v) (hn : 0 ≤ n) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hL : 1 ≤ L) (hs : s = θ ^ 2)
    (hLs : Ls ≤ 3 * L) (hLs0 : 0 ≤ Ls) (hmd0 : 0 ≤ md) (hmd : md ≤ v * (c8 * (2 * θ)))
    (hsq : |a| ≤ cs * Ls * md) (hap : |a - p| ≤ c3 * s)
    (hpq : |p - q| ≤ cp * (|c2| * L) * (dist + |s - 0|)) (hdist : dist ≤ 2 * θ + n * θ ^ 2) :
    |q| ≤ (|c3| + 6 * cs * c8 * v + cp * |c2| * (3 + n)) * (θ * L) := by
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hθL : 0 ≤ θ * L := by positivity
  have t1 : |a| ≤ 6 * cs * c8 * v * (θ * L) := by
    have e1 : Ls * md ≤ (3 * L) * (v * (c8 * (2 * θ))) :=
      mul_le_mul hLs hmd hmd0 (by linarith)
    calc |a| ≤ cs * Ls * md := hsq
      _ = cs * (Ls * md) := by ring
      _ ≤ cs * ((3 * L) * (v * (c8 * (2 * θ)))) := mul_le_mul_of_nonneg_left e1 hcs
      _ = 6 * cs * c8 * v * (θ * L) := by ring
  have t2 : |a - p| ≤ |c3| * (θ * L) := by
    have e : s ≤ θ * L := by
      rw [hs]
      nlinarith
    have hs0 : 0 ≤ s := by rw [hs]; positivity
    calc |a - p| ≤ c3 * s := hap
      _ ≤ |c3| * s := mul_le_mul_of_nonneg_right (le_abs_self _) hs0
      _ ≤ |c3| * (θ * L) := mul_le_mul_of_nonneg_left e (abs_nonneg _)
  have t3 : |p - q| ≤ cp * |c2| * (3 + n) * (θ * L) := by
    have hs0 : 0 ≤ s := by rw [hs]; positivity
    have e : dist + |s - 0| ≤ (3 + n) * θ := by
      rw [sub_zero, abs_of_nonneg hs0, hs]
      nlinarith [mul_le_mul_of_nonneg_left hθ2 hn]
    have hk : 0 ≤ cp * (|c2| * L) := by positivity
    calc |p - q| ≤ cp * (|c2| * L) * (dist + |s - 0|) := hpq
      _ ≤ cp * (|c2| * L) * ((3 + n) * θ) := mul_le_mul_of_nonneg_left e hk
      _ = cp * |c2| * (3 + n) * (θ * L) := by ring
  have tri : |q| ≤ |a| + |a - p| + |p - q| := by
    have h1 : q = a - (a - p) - (p - q) := by ring
    calc |q| = |a - (a - p) - (p - q)| := by rw [← h1]
      _ ≤ |a - (a - p)| + |p - q| := abs_sub _ _
      _ ≤ |a| + |a - p| + |p - q| := by gcongr; exact abs_sub _ _
  linarith

end WallBound

open WallBound in

theorem thmW_tower : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement →
    (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) →
    ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem,
    IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N),
    T.Proportional → T.I1 II → T.I2 II → T.I3 → T.I5 II → T.I6 II → T.I7 → T.ThmW II := by
  intro hKl hEx hDs hZ1 hZ2 II hII Ψ _ _ N T hP h1 h2 h3 h5 h6 h7 c₀ hc₀
  have hc₁ : 0 < c₀ / 2 := by positivity
  obtain ⟨θ₀, hθ₀, Cs, hCs, hsq⟩ := GlobalTheory.T.tower_gap_height_uniform_bound hZ1 hZ2 II hII Ψ N T h3 h5 h6 (c₀ / 2) hc₁
  obtain ⟨s₀, hs₀, C3, hI2⟩ := h2 ((Fintype.card Ψ : ℝ) * N)
  obtain ⟨C2, hI1⟩ := h1
  obtain ⟨C8, hC8, hdeg⟩ := GlobalTheory.T.flag_degree_le_gap Ψ N T.j T.j_pos T.j_lt
  obtain ⟨-, hlin, Cp, hCp, hLip⟩ := GlobalTheory.T.arith_functional_lipschitz_weights Ψ N (dimFl Ψ N + 1)
  obtain ⟨B₁, hB₁⟩ := GlobalTheory.T.perturbed_weight_gap_bounds Ψ N T (c₀ / 2) (min θ₀ s₀) hc₁ (lt_min hθ₀ hs₀)
  refine ⟨(∑ c, (|C3| + 6 * Cs * C8 * T.vol c + Cp * |C2| * (3 + ‖T.nu‖))) * (5 * Fintype.card Ψ), B₁,
    fun B hB τ₀ lam₀ hlam₀ => ?_⟩
  refine GlobalTheory.T.continuous_wall_bound_extend Ψ N T.j c₀ _ τ₀ (fun l => T.PB II B l) T.j_pos T.j_lt hc₀ (continuous_PB T II B) ?_ lam₀ hlam₀
  intro l hlr hlw
  obtain ⟨hB3, hθ, hθle, hθ1, hnl, hnl2, hgaps, hgap0, hcg, hdom, hdom2, hnef, hdist⟩ := hB₁ B hB τ₀ l hlw
  have hf : (1 : ℝ) ≤ Fintype.card Ψ := by
    have : 0 < Fintype.card Ψ := Fintype.card_pos_iff.mpr ⟨τ₀⟩
    exact_mod_cast this
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  set θ : ℝ := 5 * (Fintype.card Ψ : ℝ) / B with hθdef
  set lam : Wt Ψ N := fun τ i => l τ i + (if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0) with hlamdef
  let s : ℚ := (5 * (Fintype.card Ψ : ℚ) / B) ^ 2
  have hs : (s : ℝ) = θ ^ 2 := by simp [s, hθdef]
  have hdist' : ‖T.lamS lam s - l‖ ≤ 2 * θ + ‖T.nu‖ * θ ^ 2 := by rw [hs]; exact hdist
  rw [← hs] at hnl2 hdom2 hnef
  have hrat : IsRatWt lam := by
    intro τ i
    obtain ⟨q, hq⟩ := hlr τ i
    by_cases h : τ = τ₀ ∧ (i : ℕ) < T.j
    · exact ⟨q + 2 * (5 * (Fintype.card Ψ : ℚ) / B), by
        show l τ i + (if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0) = _
        rw [if_pos h, hq, hθdef]
        push_cast
        ring⟩
    · exact ⟨q, by
        show l τ i + (if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0) = _
        rw [if_neg h, hq, add_zero]⟩
  have hs0 : (0 : ℝ) < s := by rw [hs]; positivity
  have hsQ : (0 : ℚ) ≤ s := by exact_mod_cast hs0.le
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  have hsle : (s : ℝ) ≤ s₀ := by
    rw [hs]
    exact hθ2.trans (hθle.trans (min_le_right _ _))
  have hs1 : |(s : ℝ)| ≤ 1 := by
    rw [abs_of_pos hs0, hs]
    linarith
  have hnl0 : ‖l‖ ≤ 1 := hlw.1.trans (by norm_num)
  have hL := one_le_log hB3
  have hper : ∀ c, |T.PPc II B c (linRoot l ^ (dimFl Ψ N + 1))| ≤
      (|C3| + 6 * Cs * C8 * T.vol c + Cp * |C2| * (3 + ‖T.nu‖)) * (θ * Real.log B) := by
    intro c
    obtain ⟨hm0, hm1⟩ := GlobalTheory.T.tower_component_height_bound hKl hEx hDs II hII Ψ N T hP h7 B c lam s hrat hsQ hdom hdom2
    have hsqc := hsq B (by omega) c lam θ s hrat hnl hθ (hθle.trans (min_le_left _ _)) hs hgaps hcg hdom2 hnef hm0
    have hI2c := hI2 B (by omega) c lam s (l1_le_card_mul_of_norm_le_one' lam hnl) hs0 hsle hdom2
    have hmono : ∀ m, |(T.M B c).PP II (monomial m 1)| ≤ |C2| * Real.log B := fun m =>
      (hI1 B (by omega) c m).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
    have hLipc := hLip ((T.M B c).PP II) (|C2| * Real.log B) hmono (T.lamS lam s) l s 0 hnl2 hnl0 hs1 (by simp)
    have hv : 0 < T.vol c := hP.1 c
    have hmd : T.mDeg B c lam s ≤ T.vol c * (C8 * (2 * θ)) := by
      refine hm1.trans (mul_le_mul_of_nonneg_left ?_ hv.le)
      rw [← hgap0]
      exact hdeg lam τ₀ hnl hdom
    have hLs : Real.log (B / (s : ℝ)) ≤ 3 * Real.log B := by
      rw [hs]
      exact log_div_le hB3 (5 * (Fintype.card Ψ : ℝ)) (by linarith)
    have hLs0 : 0 ≤ Real.log (B / (s : ℝ)) := by
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ hs0, hs]
      have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
      nlinarith
    have hq : T.PPc II B c (linRoot l ^ (dimFl Ψ N + 1)) = (T.M B c).PP II (linA l 0 ^ (dimFl Ψ N + 1)) := by
      simp only [RootTower.PPc, toA_linRoot_pow]
    rw [hq]
    exact three_terms hCs hC8 hCp hv.le (norm_nonneg _) hθ hθ1 hL hs hLs hLs0 hm0 hmd hsqc hI2c hLipc hdist'
  have hsum : |T.PB II B l| ≤
      (∑ c, (|C3| + 6 * Cs * C8 * T.vol c + Cp * |C2| * (3 + ‖T.nu‖))) * (θ * Real.log B) := by
    rw [Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => hper c)
  refine hsum.trans (le_of_eq ?_)
  rw [hθdef]
  ring

end GlobalTheory.CompanionTheory.Ar.Top
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_weil_theorem : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.Proportional → T.I1 II → T.I2 II → T.I3 → T.I5 II → T.I6 II → T.I7 → T.ThmW II := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.thmW_tower
end
