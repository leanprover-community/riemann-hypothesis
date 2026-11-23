module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedOrbitalPairConvolution
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

theorem _root_.GlobalTheory.T.twisted_orbital_pair_convolution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H),
  Continuous σ → (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → IsOpen (K : Set H) → IsCompact (K : Set H) → ∀ (d d' : H) (f₁ f₂ : H → ℂ) (K' : Subgroup H),
  IsOpen (K' : Set H) → K' ≤ K → (∀ k ∈ K', σ k ∈ K') → IsHecke K' f₁ → IsHecke K' f₂ →
  Good (MonoidHom.id H) K (d * σ d') →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  twOrb ((MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (K.prod K) (d, d') (fun y => f₁ y.1 * f₂ (σ y.2)) =
    twOrb (MonoidHom.id H) K (d * σ d') (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) := by
  first | exact @GlobalTheory.CompanionTheory.SplitConvF.splitConv_of_finite | exact GlobalTheory.CompanionTheory.SplitConvF.splitConv_of_finite | (intros; apply GlobalTheory.CompanionTheory.SplitConvF.splitConv_of_finite <;> assumption)
