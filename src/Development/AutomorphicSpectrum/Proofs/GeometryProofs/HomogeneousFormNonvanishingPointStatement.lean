module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogeneousFormNonvanishingPoint
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes

theorem _root_.GlobalTheory.T.homogeneous_form_nonvanishing_point : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (r : ℕ) (x' : Fin (r + 1) → Ω) (hG : Gz.IsHomogeneous (d + 1)) (h0 : aeval (fun j => ∏ k, y ⟨k, E j k⟩) Gz ≠ 0) (hβ : ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 → eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0) (hx' : x' ≠ 0) (hF : ∀ i l, x' l ≠ 0 → x' i / x' l ∈ blockFnField y) (hch : ∀ a l, (∏ k, y ⟨k, E a k⟩) ≠ 0 → x' l ≠ 0 → SncChart (Algebra.adjoin ℚ (Set.range (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) ∪ Set.range (fun k => x' k / x' l))) e (aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) (map (algebraMap ℤ ℚ) Gz))), ∃ (y' : (Σ _ : Unit, Fin (r + 1)) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin (r + 1)))), (∃ i, y' ⟨(), i⟩ ≠ 0) ∧ blockFnField (joinVec y y') = blockFnField y ∧ IsMultiHomogIdeal J ∧ ¬ J ≤ mCoordIdeal (joinVec y y') ∧ IsSncModel (joinVec y y') e J ∧ ∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), evC z (rename (joinInl ι fun _ : Unit => Fin (r + 1)) β) = 0 → z ∈ mcPts J := by
  exact @GlobalTheory.CompanionTheory.Ar.SegreChart.final_data_main
