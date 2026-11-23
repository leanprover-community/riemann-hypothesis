module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSpaceApproximation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

theorem _root_.GlobalTheory.T.typed_space_approximation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
  (R ε δ : ℝ) (α : GA E N → ℂ) (F : Set (GA E N)), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → 0 < ε →
  Continuous α → HasCompactSupport α → 0 < δ → IsFundamentalDomain (latticeGL E N) F μ →
  ∃ Ω : Set (GA E N), IsCompact Ω ∧ ∀ (V : Submodule ℂ (Sm E N)) (ψ : Sm E N), IsDiscrete V → ψ ∈ V → TypeB K W ψ →
    InfBdd R V → (∀ r, 0 < r → r < N → ∀ c ∈ ExpV r V, pE E N r c ≤ -ε * (r * ((N : ℝ) - r))) →
    (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ.1 (x * y) ∂μ = s * ψ.1 x) →
    (∫⁻ x in F, ‖ψ.1 x‖ₑ ^ 2 ∂μ) = 1 → 1 ≤ 2 * ∫⁻ x in Ω, ‖ψ.1 x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Conc.conc | exact GlobalTheory.CompanionTheory.Conc.conc | (intros; apply GlobalTheory.CompanionTheory.Conc.conc <;> assumption)
