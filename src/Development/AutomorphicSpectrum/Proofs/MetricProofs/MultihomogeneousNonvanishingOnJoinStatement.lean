module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MultihomogeneousNonvanishingOnJoin
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology

theorem _root_.GlobalTheory.T.multihomogeneous_nonvanishing_on_join : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (M : ℕ) (y' : (Σ _ : Unit, Fin M) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin M))) (R : AnLogRes (mCoordIdeal (joinVec y y')) J e) (γ : MRing ι) (c : K → ℕ), IsEmbedded R.A (mCoordIdeal (joinVec y y')) R.U R.lift → (∃ i, y' ⟨(), i⟩ ≠ 0) → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → IsMultiHomog γ c → γ ∉ mCoordIdeal y → (∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), evC z (rename (joinInl ι fun _ : Unit => Fin M) γ) = 0 → z ∈ mcPts J) → (∀ z ∈ mcPts (mCoordIdeal y), evC z γ ≠ 0 → ∃ (G : Fin M → MRing ι) (g : K → ℕ), (∀ i, IsMultiHomog (G i) g) ∧ (∀ i j, y' ⟨(), i⟩ * aeval y (G j) = y' ⟨(), j⟩ * aeval y (G i)) ∧ ∃ i, evC z (G i) ≠ 0) → Nonempty (AnLogRes (mCoordIdeal y) (Ideal.span {γ}) e) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.anLogRes_of_embedded_join | exact GlobalTheory.CompanionTheory.Ar.Giv.anLogRes_of_embedded_join | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.anLogRes_of_embedded_join <;> assumption)
