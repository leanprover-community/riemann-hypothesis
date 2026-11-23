module

public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeDimensionUpperStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeLeSpanNormStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeSpanTwistShiftStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalChartLatticeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinrankLeAddOfMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoOfAsymptoticBoundsStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.ProjLineLimit
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefSectionsAsymptotic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PositivityTheory.Tls2.Nef

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

theorem nefRR : GlobalTheory.CompanionTheory.Ar.Pub.NefRR := by
  intro K _ ι _ Ω _ _ y D a hV hB hN
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact GlobalTheory.CompanionTheory.Ar.Pub.NefRRModel.nefRR_dimZero y a hV hB
  obtain ⟨e, c, hc, hmem⟩ := GlobalTheory.T.chart_lattice_span_twist_shift K ι Ω y D hV hB
  have hinj : Function.Injective (LinearMap.mulLeft ℚ c) := mul_right_injective₀ hc
  have hle : ∀ τ : ℕ, (Submodule.span ℚ (chartLatNm y a τ : Set Ω)).map (LinearMap.mulLeft ℚ c) ≤
      chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1 := by
    intro τ
    rintro _ ⟨s, hs, rfl⟩
    exact hmem a τ s hs
  have hfd : ∀ τ : ℕ, FiniteDimensional ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) := by
    intro τ
    haveI := GlobalTheory.T.finiteDimensional_chart_lattice K ι Ω y D ((τ : ℤ) • a + fun k => (e k : ℤ)) hV
    haveI : FiniteDimensional ℚ ((Submodule.span ℚ (chartLatNm y a τ : Set Ω)).map (LinearMap.mulLeft ℚ c)) :=
      Submodule.finiteDimensional_of_le (hle τ)
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ hinj _).symm
  have hup : ∀ τ : ℕ, Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) ≤
      Module.finrank ℚ (chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1) := by
    intro τ
    haveI := GlobalTheory.T.finiteDimensional_chart_lattice K ι Ω y D ((τ : ℤ) • a + fun k => (e k : ℤ)) hV
    rw [(Submodule.equivMapOfInjective _ hinj (Submodule.span ℚ (chartLatNm y a τ : Set Ω))).finrank_eq]
    exact Submodule.finrank_mono (hle τ)
  have hlow : ∀ τ : ℕ, Module.finrank ℚ (chartLatQ y ((τ : ℤ) • a + 0) 1) ≤
      Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) := by
    intro τ
    haveI := hfd τ
    have hsub : chartLatQ y ((τ : ℤ) • a + 0) 1 ≤ Submodule.span ℚ (chartLatNm y a τ : Set Ω) := by
      rw [add_zero, ← chartLatQ_eq_smul_one]
      exact GlobalTheory.T.chart_lattice_le_span_norm K ι Ω y a τ
    exact Submodule.finrank_mono hsub
  refine ⟨hfd, ?_⟩
  apply GlobalTheory.T.tendsto_of_asymptotic_bounds (fun τ => (Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) : ℝ)) _ D
  · intro ε hε
    filter_upwards [GlobalTheory.CompanionTheory.NefLower.nef_sections_lower K ι Ω y D a 0 hD hV hB hN ε hε] with n hn
    exact hn.trans (by exact_mod_cast hlow n)
  · intro ε hε
    filter_upwards [GlobalTheory.T.chart_lattice_dimension_upper K ι Ω y D a (fun k => (e k : ℤ)) hD hV hB hN ε hε] with n hn
    exact le_trans (by exact_mod_cast hup n) hn

end PositivityTheory.Tls2.Nef
