module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorQuotientQuantumDeterminantEigen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport

theorem _root_.GlobalTheory.T.tensor_quotient_quantum_determinant_eigen : StepChar → TensDecomp → ∀ {m : ℕ} (M : GMod m) (χ : Fin m → ℂ), HasChar M χ → ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin m → Fin m → Module.End ℂ V), GlRel E → ∀ Φ : (Fin m → M.V) →ₗ[ℂ] V, (∀ a b u, Φ (tensE M a b u) = E a b (Φ u)) → Φ ≠ 0 → ∃ r, ∃ w ∈ LinearMap.range Φ, w ≠ 0 ∧ ∀ Y : ℂ, qdet E (Y + ((m : ℂ) - 1) / 2) w = Formalism.QuantumDeterminants.capP (χ + Pi.single r 1) Y • w := by
  first | exact @GlobalTheory.CompanionTheory.RgTransport.Raise.exists_raised | exact GlobalTheory.CompanionTheory.RgTransport.Raise.exists_raised | (intros; apply GlobalTheory.CompanionTheory.RgTransport.Raise.exists_raised <;> assumption)
