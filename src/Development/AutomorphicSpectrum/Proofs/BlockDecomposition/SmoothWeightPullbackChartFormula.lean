module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjSpace
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes

@[expose] public section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.PullDens


open Filter Topology in
theorem locDens_pullback_eq : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → ∀ (c : GlobalTheory.AlgChart q σ D) (j : Fin A.n) (u : Fin D → ℂ),
      u ∈ (A.chart j).target → F ((A.chart j).symm u) ∈ c.e.source →
      AnalyticAt ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u ∧
      locDens A (fun _ => φ.locPot.pullback F hF) j u =
        ‖LinearMap.det (fderiv ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u :
          (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 * c.chernDens φ (F ((A.chart j).symm u)) := by
  intro k _ X q σ D T _ A F hF hH B φ h c j u hu hsrc
  have hcont : ContinuousAt (F ∘ (A.chart j).symm) u :=
    hF.continuousAt.comp ((A.chart j).continuousAt_symm hu)
  have hN : ∀ᶠ w in 𝓝 u, F ((A.chart j).symm w) ∈ c.e.source :=
    hcont.eventually (c.e.open_source.mem_nhds hsrc)
  have hG : AnalyticAt ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u := by
    refine analyticAt_pi_iff.2 fun a => ?_
    refine (hH c.U (c.x a) j u ⟨hu, c.source_subset hsrc⟩).congr ?_
    filter_upwards [hN] with w hw
    exact (c.finChart_eq_ev hw a).symm
  refine ⟨hG, ?_⟩
  set G := c.finChart ∘ F ∘ (A.chart j).symm with hGdef
  set y₀ := F ((A.chart j).symm u) with hy₀
  have hGu : G u = c.finChart y₀ := rfl
  have hsy : c.finChart.symm (G u) = y₀ := c.finChart.left_inv hsrc
  have hz : G u ∈ c.finChart.target := c.finChart.map_source hsrc
  have hma := h.maDens_eq c hz
  rw [hsy] at hma
  have hr : c.e y₀ = GlobalTheory.FinChart.toV D (G u) := rfl
  have hd := h.contDiffAt c hsrc (mem_pick φ.isLB y₀)
  rw [hr] at hd
  have hψ : ContDiffAt ℝ 2 (fun w => φ.locPot.φ y₀ (c.finChart.symm w)) (G u) :=
    (hd.comp (G u) (GlobalTheory.FinChart.toV D).contDiff.contDiffAt).div_const 2
  have hcomp := ReciprocityTheory.AnForm.A.maDens_comp (fun _ w => φ.locPot.φ y₀ (c.finChart.symm w)) G u hG
    (fun _ => hψ)
  rw [ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq, hma] at hcomp
  rw [mul_comm, ← hcomp]
  unfold locDens
  refine maDens_congr_hessC _ _ _ fun _ => hessCGerm _ _ _ ?_
  filter_upwards [hN] with w hw
  simp only [LocPot.pullback, Function.comp_apply, hGdef]
  rw [c.finChart.left_inv hw]

end GlobalTheory.CompanionTheory.MixZ.PullDens
