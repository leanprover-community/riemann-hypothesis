module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL

noncomputable section

namespace GlobalTheory.Block5c

def TypeCusp : Prop :=
  ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] (J : Subgroup (GL ι K)), IsOpen (J : Set (GL ι K)) → IsCompact (J : Set (GL ι K)) →
  ∀ χ : J →* ℂˣ, IsOpen (χ.ker : Set J) →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ h : GL ι K, ∃ X, ∃ hX : h⁻¹ * u X * h ∈ J, χ ⟨_, hX⟩ ≠ 1) →
  ∀ f : GL ι K → ℂ, (∀ g (hg : g ∈ J), f g = (((χ ⟨g, hg⟩)⁻¹ : ℂˣ) : ℂ)) → (∀ g, g ∉ J → f g = 0) →
  IsLocallyConstant f ∧ HasCompactSupport f ∧
  (∀ x ∈ (χ.ker.map J.subtype), ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (x * g * y) = f g) ∧
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0)

end GlobalTheory.Block5c
