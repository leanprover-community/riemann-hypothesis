module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Finset
open scoped Matrix

noncomputable section

namespace Formalism.MainNotions.DiscreteSeriesWeylDimension

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def HasTypeU (k : ℕ) (u : Fin k → ℝ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsHCTypeU k u π

def HighestWeightExists : Prop := ∀ (k : ℕ) (u : Fin k → ℝ), Formalism.QuantumDeterminants.IsHCParam u → HasTypeU k u


variable {eps : ℝ} (Fm : FamP eps)



variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]



variable {eps : ℝ} (Fm : FamP eps)


def WeylForK : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
    IsURepOn (Formalism.REAL.Kset ε) σ → IsKTypeOf ε σ Λ S →
    (Module.finrank ℂ S : ℝ) =
      (∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b),
        ((Λ + Formalism.REAL.rhoC ε) a - (Λ + Formalism.REAL.rhoC ε) b)) /
      ((∏ i ∈ Finset.range (LocalBesselAndTopKernel.nPl ε), (i.factorial : ℝ)) * ∏ i ∈ Finset.range (LocalBesselAndTopKernel.nMi ε), (i.factorial : ℝ))

def LowKMultOne : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    ∀ S S' : Submodule ℂ H, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S → IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S = S'


variable {eps : ℝ} (Fm : FamP eps)



variable {eps : ℝ} (Fm : FamP eps)



variable {eps : ℝ} (Fm : FamP eps)



variable {eps : ℝ} (Fm : FamP eps)


section FiniteOrder

open Polynomial

end FiniteOrder


open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] {N : Type*} [Fintype N] [DecidableEq N]


end Formalism.MainNotions.DiscreteSeriesWeylDimension

end
