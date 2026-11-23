module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Basic.Complex.Basic
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CommutingLocallyNilpotentCommonKernel
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.KeepsMul
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub

@[expose] public section

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport

theorem _root_.GlobalTheory.T.commuting_locally_nilpotent_common_kernel : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (I : Submodule ℂ V), I ≠ ⊥ → ∀ (D : ℂ → Module.End ℂ V), (∀ Y Y', Commute (D Y) (D Y')) → (∀ Y, ∀ x ∈ I, D Y x ∈ I) → (∀ Y, ∀ x ∈ I, ∃ N : ℕ, (D Y ^ N) x = 0) → ∀ (l : ℕ) (c : ℕ → Module.End ℂ V), (∀ Y, D Y = ∑ j ∈ Finset.range l, Y ^ j • c j) → ∃ w ∈ I, w ≠ 0 ∧ ∀ Y, D Y w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgTransport.exists_joint_kernel_polynomial_family | exact GlobalTheory.CompanionTheory.RgTransport.exists_joint_kernel_polynomial_family | (intros; apply GlobalTheory.CompanionTheory.RgTransport.exists_joint_kernel_polynomial_family <;> assumption)
