module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsomorphicLinesPotentialDifference
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CmpBuild
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TopCmp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.CompanionTheory.Relay.comparison_of_inputs_avoidance : Inputs → AvoidStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → CmpSt := by
  intro hIn hAv hRes II hII K _ ι _ K₁ _ ι₁ _ K₂ _ ι₂ _ κ₁ v₁ κ₂ v₂ Ω _ _ y D σ _ S₁ S₂ Re₁ Re₂ β b
    hb₁ hb₂ hAr hβ hβy halg₁ halg₂ hsing w
  obtain ⟨K', _, ι', _, κ, v, y', S, Re, f, g, d, hbl, hyv, hfield, hdeg, ht₁, ht₂, hpull, hiso,
    hsm, hph, hrel⟩ :=
    GlobalTheory.CompanionTheory.Ar.Cmp.BuildK.joint_system hIn hRes K ι K₁ ι₁ K₂ ι₂ κ₁ v₁ κ₂ v₂ Ω y D σ S₁ S₂ Re₁ Re₂ β b
      hb₁ hb₂ hAr hβ hβy halg₁ halg₂ hsing
  have hlim := GlobalTheory.CompanionTheory.Ar.Cmp.OneModel.cmp_one hIn hAv II hII K' ι' (mCoordIdeal y') D σ S Re f g d
    hiso hsm hph hrel w
  have hpos₁ : 0 < S₁.t₀ := (S₁.reg (w 0)).1
  have hpos₂ : 0 < S₂.t₀ := (S₂.reg (w 0)).1
  have hPF : HasPFCoord II := hII.2.2.1
  refine hlim.congr' ?_
  have hmem : Set.Ioc (0 : ℝ) (min S₁.t₀ S₂.t₀) ∈ 𝓝[>] (0 : ℝ) :=
    Ioc_mem_nhdsGT (lt_min hpos₁ hpos₂)
  filter_upwards [hmem] with t ht
  rw [GlobalTheory.CompanionTheory.Ar.Cmp.CoordK.side_eq II hPF Re₁ Re Sum.inl hb₁ hbl hyv hfield hdeg
      (fun a t => (hpull a t).1) w t ht.1 (le_trans ht.2 (min_le_left _ _)),
    GlobalTheory.CompanionTheory.Ar.Cmp.CoordK.side_eq II hPF Re₂ Re Sum.inr hb₂ hbl hyv hfield hdeg
      (fun a t => (hpull a t).2) w t ht.1 (le_trans ht.2 (min_le_right _ _))]
