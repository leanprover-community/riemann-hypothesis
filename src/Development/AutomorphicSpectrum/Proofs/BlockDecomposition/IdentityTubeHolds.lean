module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.Eis

theorem tube_isOpen {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) : IsOpen (tube Ω) := by
  have hc : Continuous fun l : ℂ × ℂ => (l.1.re, l.2.re) :=
    (Complex.continuous_re.comp continuous_fst).prodMk (Complex.continuous_re.comp continuous_snd)
  exact hc.isOpen_preimage Ω hΩ

theorem line_tube_convex {Ω : Set (ℝ × ℝ)} (hc : Convex ℝ Ω) (p v : ℂ × ℂ) :
    Convex ℝ {τ : ℂ | p + τ • v ∈ tube Ω} := by
  intro x hx y hy a b ha hb hab
  have key := hc hx hy ha hb hab
  simp only [tube, Set.mem_ofPred_eq] at hx hy key ⊢
  convert key using 1
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, Complex.add_re, smul_eq_mul, Complex.real_smul,
      Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Prod.fst_add, Prod.smul_mk, Prod.mk_add_mk]
    linear_combination (-p.1.re) * hab
  · simp only [Prod.snd_add, Prod.smul_snd, Complex.add_re, smul_eq_mul, Complex.real_smul,
      Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Prod.smul_mk, Prod.mk_add_mk]
    linear_combination (-p.2.re) * hab

theorem idTube : IdTube := by
  intro X _ _ _ Ω Ω' F F' hΩ hc hΩ' hne hsub hF hF' heq z hz
  obtain ⟨ω, hω⟩ := hne
  set z0 : ℂ × ℂ := ((ω.1 : ℂ), (ω.2 : ℂ)) with hz0
  have hz0' : z0 ∈ tube Ω' := by simpa [tube, hz0] using hω
  have hline : Continuous fun τ : ℂ => z0 + τ • (z - z0) := by fun_prop
  have hDo : IsOpen {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := (tube_isOpen hΩ).preimage hline
  have hDc : Convex ℝ {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := line_tube_convex hc z0 (z - z0)
  have h0 : (0 : ℂ) ∈ {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := by
    show z0 + (0 : ℂ) • (z - z0) ∈ tube Ω
    rw [zero_smul, add_zero]
    exact hsub hz0'
  have h1 : (1 : ℂ) ∈ {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := by simpa using hz
  have hA := (hF z0 (z - z0)).analyticOnNhd hDo
  have hA' := (hF' z0 (z - z0)).analyticOnNhd hDo
  have hev : (fun τ : ℂ => F (z0 + τ • (z - z0))) =ᶠ[𝓝 0] (fun τ : ℂ => F' (z0 + τ • (z - z0))) := by
    have hO' : IsOpen {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω'} := (tube_isOpen hΩ').preimage hline
    filter_upwards [hO'.mem_nhds (by simpa using hz0')] with τ hτ
    exact heq hτ
  have := hA.eqOn_of_preconnected_of_eventuallyEq hA' hDc.isPreconnected h0 hev h1
  simpa using this

end GlobalTheory.CompanionTheory.Eis
