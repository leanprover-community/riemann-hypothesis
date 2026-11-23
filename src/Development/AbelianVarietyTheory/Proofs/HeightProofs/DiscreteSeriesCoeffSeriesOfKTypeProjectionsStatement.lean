module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesCoeffSeriesOfKTypeProjections
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.discreteSeriesCoeffSeries_of_kTypeProjections : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ f : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    (∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun ε e →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (x : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, IsKFin ε σ (x j)) ∧
        ∀ y ∈ UJset ε, (∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) = ∑ j, ℓ j (σ y (x j))) →
    GlobalTheory.TypeSum.HasTypeAll (GlobalTheory.SmoothGlob.lieSet ε) (UJset ε) σ f := by
  first | exact @GlobalTheory.TypeSum.KSeries.hasTypeAll_of_kTypes | exact GlobalTheory.TypeSum.KSeries.hasTypeAll_of_kTypes | (intros; apply GlobalTheory.TypeSum.KSeries.hasTypeAll_of_kTypes <;> assumption)
