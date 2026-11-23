module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.HolomorphicFamilySmoothHermitian
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

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.CompanionTheory.Relay.holomorphic_family_smooth_entries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ), IsOpen U → IsHolFam U R → (∀ i j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ((R t).Hm i j).re) U ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ((R t).Hm i j).im) U) ∧ (∀ a x, DifferentiableOn ℂ (fun t => (R t).B a x) U) ∧ ∀ (m : ℕ) (u : Fin m → (Fin n → ℂ) → Fin g → ℂ), (∀ i, DifferentiableOn ℂ (u i) U) → (∀ t ∈ U, LinearIndependent ℂ fun i => u i t) → ReciprocityTheory.AnForm.A.IsPsh U fun t => Real.log ((R t).gram fun i => u i t).det.re := by
  first | exact @LevelTowerAlt.holomorphic_family_smooth_hermitian | exact LevelTowerAlt.holomorphic_family_smooth_hermitian
