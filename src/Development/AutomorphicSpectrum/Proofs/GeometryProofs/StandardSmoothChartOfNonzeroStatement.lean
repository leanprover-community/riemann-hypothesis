module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StandardSmoothChartOfNonzero
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes

theorem _root_.GlobalTheory.T.standard_smooth_chart_of_nonzero : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ) (hb : IsMultiHomog β b) (hβ : β ∉ mCoordIdeal y) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)) (hs : s ≠ 0) [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s)], ∃ (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (g₀ : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)), Gz.IsHomogeneous (d + 1) ∧ (X c₀ : MvPolynomial _ ℤ) ∣ Gz ∧ (g₀ : Ω) = aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) Gz ∧ g₀ ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀) ∧ ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 → eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRes.exists_segre_form | exact GlobalTheory.CompanionTheory.Ar.SncRes.exists_segre_form | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRes.exists_segre_form <;> assumption)
