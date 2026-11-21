import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem regroup_fib_tsum {X M : Type} [AddCommMonoid M] [TopologicalSpace M] (n : X → ℕ) (i : ℕ)
    (h : {α | n α = i}.Finite) (f : X → M) :
    ∑' b : n ⁻¹' {i}, f b = ∑ α ∈ h.toFinset, f α := by
  have hs : n ⁻¹' {i} = (h.toFinset : Set X) := by ext; simp
  rw [← Finset.tsum_subtype', ← hs]

theorem lattice_series_regroup : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (X : Type) (n : X → ℕ) (π : C) (a : X → C) (b : ℝ), π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ α, ‖a α‖ ≤ b * ‖π‖ ^ n α) → ∃ Θ : PowerSeries C, (∀ i, ‖PowerSeries.coeff i Θ‖ ≤ max b 0) ∧ ∑' i, PowerSeries.coeff i Θ * π ^ i = ∑' α, a α ∧ ∀ (e : C →+* ℂ) (u : ℂ), (Summable fun α => ‖e (a α) * (u / e π) ^ n α‖) → (Summable fun i => ‖e (PowerSeries.coeff i Θ) * u ^ i‖) ∧ ∑' i, e (PowerSeries.coeff i Θ) * u ^ i = ∑' α, e (a α) * (u / e π) ^ n α := by
  intro C _ _ _ X n π a b hπ0 hπ1 hfin hb
  classical
  have hmem : ∀ i α, α ∈ (hfin i).toFinset ↔ n α = i := fun i α => by simp
  have hn : Filter.Tendsto n Filter.cofinite Filter.atTop := by
    refine Filter.tendsto_atTop.2 fun N => Filter.eventually_cofinite.2 ?_
    refine ((Set.finite_lt_nat N).biUnion fun i _ => hfin i).subset ?_
    intro α hα
    simp only [Set.mem_setOf_eq, not_le] at hα
    exact Set.mem_biUnion (x := n α) hα rfl
  have hpow : Filter.Tendsto (fun α => b * ‖π‖ ^ n α) Filter.cofinite (nhds 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg π) hπ1).comp hn).const_mul b
  have ha0 : Filter.Tendsto a Filter.cofinite (nhds 0) := squeeze_zero_norm hb hpow
  have ha : Summable a := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ha0
  refine ⟨PowerSeries.mk fun i => ∑ α ∈ (hfin i).toFinset, a α / π ^ i, ?_, ?_, ?_⟩
  · intro i
    rw [PowerSeries.coeff_mk]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (le_max_right _ _) fun α hα => ?_
    have hpi : 0 < ‖π‖ ^ i := pow_pos (norm_pos_iff.2 hπ0) _
    rw [norm_div, norm_pow, div_le_iff₀ hpi]
    have := hb α
    rw [(hmem i α).1 hα] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpi.le)
  · rw [← ((ha.hasSum.tsum_fiberwise n).tsum_eq)]
    refine tsum_congr fun i => ?_
    rw [PowerSeries.coeff_mk, regroup_fib_tsum n i (hfin i), Finset.sum_mul]
    exact Finset.sum_congr rfl fun α _ => div_mul_cancel₀ _ (pow_ne_zero _ hπ0)
  · intro e u hsum
    have heπ : e π ≠ 0 := (map_ne_zero e).2 hπ0
    have hkey : ∀ i, e (PowerSeries.coeff i (PowerSeries.mk fun i => ∑ α ∈ (hfin i).toFinset, a α / π ^ i)) * u ^ i
        = ∑ α ∈ (hfin i).toFinset, e (a α) * (u / e π) ^ n α := by
      intro i
      rw [PowerSeries.coeff_mk, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [(hmem i α).1 hα, map_div₀, map_pow, div_pow]
      field_simp
    simp_rw [hkey]
    have hf : Summable fun α => e (a α) * (u / e π) ^ n α := hsum.of_norm
    refine ⟨?_, ?_⟩
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => norm_sum_le _ _) ?_
      have := (hsum.hasSum.tsum_fiberwise n).summable
      exact this.congr fun i => regroup_fib_tsum n i (hfin i) (fun α => ‖e (a α) * (u / e π) ^ n α‖)
    · rw [← ((hf.hasSum.tsum_fiberwise n).tsum_eq)]
      exact tsum_congr fun i => (regroup_fib_tsum n i (hfin i) _).symm

end GlobalTheory.MBLow
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem deform_of_lattice_series : ∀ (κ : Rule) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [CharZero C] (e : C →+* ℂ) (x : KeyIn C) (g : ℕ) (hg : x.P.g = g) (m : ℕ) (ζ : Cˣ)
    (lev : Out.Level x.P (m ^ 2) (unitOn ζ)) (k : C) (X : Type) (n : X → ℕ) (π : C) (B : ℝ)
    (a : (Fin (2 * g) → ZMod (m ^ 2)) → X → C) (b : (Fin (2 * g) → ZMod (m ^ 2)) → Fin g → X → C),
    π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ i α, ‖a i α‖ ≤ B * ‖π‖ ^ n α) →
    (∀ i j α, ‖b i j α‖ ≤ B * ‖π‖ ^ n α) →
    ThJet x hg m (levelPoint lev hg) (fun i => ∑' α, a i α) (fun i j => ∑' α, b i j α) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      ((∀ i, Summable fun α => ‖e (a i α) * u ^ n α‖) ∧ ∀ i j, Summable fun α => ‖e (b i j α) * u ^ n α‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map e.toMonoidHom ζ))),
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) (fun i => ∑' α, e (a i α) * u ^ n α)
          (fun i j => ∑' α, e (b i j α) * u ^ n α) ∧ (κ ℂ x₀ : ℂ) = e k) →
    Deform κ e x hg m ζ lev k := by
  intro κ C _ _ _ _ e x g hg m ζ lev k X n π B a b hπ0 hπ1 hfin ha hb hJ hE
  have hA := fun i => lattice_series_regroup C X n π (a i) B hπ0 hπ1 hfin (ha i)
  have hB := fun i j => lattice_series_regroup C X n π (b i j) B hπ0 hπ1 hfin (hb i j)
  choose Θ hΘb hΘs hΘc using hA
  choose Γ hΓb hΓs hΓc using hB
  obtain ⟨ε, hε, hu⟩ := hE
  have heπ : e π ≠ 0 := (map_ne_zero e).2 hπ0
  have hnπ : 0 < ‖e π‖ := norm_pos_iff.2 heπ
  refine ⟨Θ, Γ, π, max B 0, hπ1, fun i l => ⟨hΘb i l, fun j => hΓb i j l⟩, ?_, ε * ‖e π‖, mul_pos hε hnπ, ?_⟩
  · have h1 : (fun i => ∑' l, PowerSeries.coeff l (Θ i) * π ^ l) = fun i => ∑' α, a i α := funext hΘs
    have h2 : (fun i j => ∑' l, PowerSeries.coeff l (Γ i j) * π ^ l) = fun i j => ∑' α, b i j α :=
      funext fun i => funext (hΓs i)
    rw [h1, h2]; exact hJ
  · intro u hu0 hul
    have hv0 : u / e π ≠ 0 := div_ne_zero hu0 heπ
    have hvl : ‖u / e π‖ < ε := by rw [norm_div, div_lt_iff₀ hnπ]; exact hul
    obtain ⟨⟨hsa, hsb⟩, x₀, hg₀, lev₀, hJ₀, hk⟩ := hu (u / e π) hv0 hvl
    refine ⟨fun i => ⟨(hΘc i e u (hsa i)).1, fun j => (hΓc i j e u (hsb i j)).1⟩, x₀, hg₀, lev₀, ?_, hk⟩
    have h1 : (fun i => ∑' l, e (PowerSeries.coeff l (Θ i)) * u ^ l) = fun i => ∑' α, e (a i α) * (u / e π) ^ n α :=
      funext fun i => (hΘc i e u (hsa i)).2
    have h2 : (fun i j => ∑' l, e (PowerSeries.coeff l (Γ i j)) * u ^ l) =
        fun i j => ∑' α, e (b i j α) * (u / e π) ^ n α :=
      funext fun i => funext fun j => (hΓc i j e u (hsb i j)).2
    rw [h1, h2]; exact hJ₀

end GlobalTheory.MBLow
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesDeformation_of_boundedLatticeSeries : ∀ (κ : Rule) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [CharZero C] (e : C →+* ℂ) (x : KeyIn C) (g : ℕ) (hg : x.P.g = g) (m : ℕ) (ζ : Cˣ)
    (lev : Out.Level x.P (m ^ 2) (unitOn ζ)) (k : C) (X : Type) (n : X → ℕ) (π : C) (B : ℝ)
    (a : (Fin (2 * g) → ZMod (m ^ 2)) → X → C) (b : (Fin (2 * g) → ZMod (m ^ 2)) → Fin g → X → C),
    π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ i α, ‖a i α‖ ≤ B * ‖π‖ ^ n α) →
    (∀ i j α, ‖b i j α‖ ≤ B * ‖π‖ ^ n α) →
    ThJet x hg m (levelPoint lev hg) (fun i => ∑' α, a i α) (fun i j => ∑' α, b i j α) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      ((∀ i, Summable fun α => ‖e (a i α) * u ^ n α‖) ∧ ∀ i j, Summable fun α => ‖e (b i j α) * u ^ n α‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map e.toMonoidHom ζ))),
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) (fun i => ∑' α, e (a i α) * u ^ n α)
          (fun i j => ∑' α, e (b i j α) * u ^ n α) ∧ (κ ℂ x₀ : ℂ) = e k) →
    Deform κ e x hg m ζ lev k := by
  atlas_forward_decl GlobalTheory.MBLow.deform_of_lattice_series
end
