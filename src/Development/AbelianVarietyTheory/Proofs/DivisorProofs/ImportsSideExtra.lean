import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussManinPeriodsOfSpanAndTaylorClauses
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSpanTopAndFinrankFromCechPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallinePeriodEqCechDeRhamPeriod
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveCrystallineBaseChangeNilpotentThickenin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPeriodEqPeriodOverThickening
import BuildAid.ForwardExisting

section
open GlobalTheory.AnPer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussManinPeriods_of_span_and_taylor_clauses : PSpan → PTaylor → GlobalTheory.Published.GaussManinPeriods := by
  first | exact @GlobalTheory.AnPer.gaussManinPeriods_of_span_taylor | exact GlobalTheory.AnPer.gaussManinPeriods_of_span_taylor | (intros; apply GlobalTheory.AnPer.gaussManinPeriods_of_span_taylor <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_map_span_top_and_finrank_from_cech_periods : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ P : u.Λ →+ HdR A, (∀ c : primDR A, IsPer u.ex u.Λ (cmp1 (str A) c.1) fun l => P l c) → Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (HdR A) = 2 * g := by
  first | exact @GlobalTheory.CechPer.span_periods_eq_top_and_finrank | exact GlobalTheory.CechPer.span_periods_eq_top_and_finrank | (intros; apply GlobalTheory.CechPer.span_periods_eq_top_and_finrank <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_period_eq_cechDeRham_period : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (c : FirstDeRham (str A)) (q : u.Λ →+ ℂ) (per : u.Λ →+ Hol (fibFam u).V), (∀ l, per l = algebraMap ℂ _ (q l)) → IsPeriod (fibUnif u) c per → IsPer u.ex u.Λ (cmp1 (str A) c) q := by
  first | exact @GlobalTheory.PerLink.main | exact GlobalTheory.PerLink.main | (intros; apply GlobalTheory.PerLink.main <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PeriodSpan

theorem main : PSpan := by
  intro A _ g hA _ L u P hP
  refine GlobalTheory.T.period_map_span_top_and_finrank_from_cech_periods A g L u hA P fun c => ?_
  exact GlobalTheory.T.crystalline_period_eq_cechDeRham_period A g L u c.1
    { toFun := fun l => P l c, map_zero' := by simp, map_add' := fun x y => by simp }
    _ (fun _ => rfl) (hP c)

end GlobalTheory.PeriodSpan
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_span_deRhamHomology_rank_two_g : PSpan := by
  atlas_forward_decl GlobalTheory.PeriodSpan.main
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem isNilpotent_of_isDPNilpotent : ∀ {D : Type} [CommRing D] [Algebra ℂ D] {J : Ideal D}
    (dl : DividedPowers J), IsNilDP dl → IsNilpotent J := by
  intro D _ _ J dl hdl
  obtain ⟨N, h⟩ := hdl
  have h0 : ∀ l : List D, (∀ b ∈ l, b ∈ J) → N ≤ l.length → l.prod = 0 := by
    intro l hl hN
    have k := h (l.map fun b ↦ (1, b)) (by simpa using hl)
      (by simpa [List.map_map, Function.comp_def] using hN)
    rw [List.map_map] at k
    have e : l.map ((fun p : ℕ × D ↦ dl.dpow p.1 p.2) ∘ fun b ↦ (1, b)) = l.map id :=
      List.map_congr_left fun b hb ↦ dl.dpow_one (hl b hb)
    rwa [e, List.map_id] at k
  have key : ∀ n : ℕ, ∀ x ∈ J ^ n, ∀ l : List D, (∀ b ∈ l, b ∈ J) →
      N ≤ n + l.length → x * l.prod = 0 := by
    intro n
    induction n with
    | zero => intro x _ l hl hN; rw [h0 l hl (by simpa using hN), mul_zero]
    | succ n ih =>
      intro x hx l hl hN
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_)
        fun a b ha hb ↦ by rw [add_mul, ha, hb, add_zero]
      have := ih a ha (b :: l) (by simpa using ⟨hb, hl⟩) (by simp; omega)
      rwa [List.prod_cons, ← _root_.mul_assoc] at this
  refine ⟨N, eq_bot_iff.2 fun x hx ↦ ?_⟩
  simpa using key N x hx [] (by simp) (by simp)

end GlobalTheory.AnPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNilpotent_of_nilpotentDividedPowers_ideal : ∀ {D : Type} [CommRing D] [Algebra ℂ D] {J : Ideal D} (dl : DividedPowers J), IsNilDP dl → IsNilpotent J := by
  atlas_forward_decl GlobalTheory.AnPer.isNilpotent_of_isDPNilpotent
end

section
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem isSeparated_left_of_isAbelianScheme {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (h : IsAbelianScheme A) : A.left.IsSeparated := by
  have h1 : IsProper A.hom := h.proper
  have h2 : IsSeparated A.hom := inferInstance
  rw [Scheme.isSeparated_iff, ← terminal.comp_from A.hom]
  infer_instance

theorem pTaylor : PTaylor := by
  intro I _ _ g B _ _ 𝒜 _ hA hg y₀ A₀ _ φ₀ hφ₀ L₀ u₀ F σ e h0 hy hE hτ P₀ hP₀ D _ _ π κ hκ hπ N t ht htN
    j hj A' _ φ' _ m' i h hi k x d hd c per hper
  obtain ⟨hA₀, hg₀⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ 𝒜 A₀ φ₀ g hφ₀ hA hg
  have hspan := (GlobalTheory.T.primitiveCrystalline_baseChange_nilpotent_thickening A₀ g hA₀ hg₀ D π κ hκ hπ k).2
  have hmem : (liftMor κ h).pull (m'.pull c) ∈ Submodule.span D (Set.range k.pull) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨n, f, v, hv⟩ := Submodule.mem_span_set'.1 hmem
  choose a ha using fun r : Fin n ↦ (v r).2
  have hsum : (liftMor κ h).pull (m'.pull c) = ∑ r, f r • k.pull (a r) := by
    rw [← hv]; exact Finset.sum_congr rfl fun r _ ↦ by rw [ha]
  let πa : D →ₐ[ℂ] ℂ := { π with commutes' := hπ }
  have M := (m'.comp (liftMor κ h)).isMor
  have nn : IsMor (dp0 B) (𝒜.hom ≫ 𝟙 _) κ (A₀.hom ≫ spMap π) (j : B →+* D) φ₀ := by
    rw [RingHom.id_comp, hi] at M
    exact M
  have hpull : nn.pull1 c.1 = ∑ r ∈ Finset.univ, f r • k.isMor.pull1 (a r).1 := by
    have e1 := IsMor.pullback1_comp m'.isMor (liftMor κ h).isMor nn (fun _ ↦ rfl) hi c.1
    have e2 := congrArg (Submodule.subtype _) hsum
    rw [map_sum] at e2
    exact e1.symm.trans e2
  have key := GlobalTheory.T.taylor_period_eq_period_over_thickening_alt (F := F) (F₀ := fibFam u₀) e (fibUnif u₀)
    (isSeparated_left_of_isAbelianScheme 𝒜 hA) (isSeparated_left_of_isAbelianScheme A₀ hA₀) h0
    (fun _ ↦ trivial) (fun l _ ↦ (hτ l).symm) φ₀ (fun p ↦ (hE p.2).symm) πa (GlobalTheory.T.isNilpotent_of_nilpotentDividedPowers_ideal κ hκ) κ
    (fun _ hd ↦ hd) N t ht htN (j : B →+* D) hj (A₀.hom ≫ spMap π)
    (by rw [Category.comp_id]; rfl) nn _ k.isMor rfl c.1 per hper Finset.univ f (fun r ↦ (a r).1)
    (fun r l ↦ P₀ l (a r)) _ (fun _ _ ↦ rfl) (fun r ↦ hP₀ (a r)) hpull x
  rw [crysToDR_apply, hsum, map_sum, ← key]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [map_smul, hd (a r), smul_eq_mul]

end GlobalTheory.AnPer
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCycleExtension_taylorPeriod_of_thickeningComparison : GlobalTheory.AnPer.PTaylor := by
  atlas_forward_decl GlobalTheory.AnPer.pTaylor
end

section
namespace GlobalTheory.GaussManinTop

theorem main : GlobalTheory.Published.GaussManinPeriods :=
  GlobalTheory.T.gaussManinPeriods_of_span_and_taylor_clauses GlobalTheory.T.periods_span_deRhamHomology_rank_two_g GlobalTheory.T.constantCycleExtension_taylorPeriod_of_thickeningComparison

end GlobalTheory.GaussManinTop
end
