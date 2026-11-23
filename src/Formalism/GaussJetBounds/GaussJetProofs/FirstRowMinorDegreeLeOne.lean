module

public import Formalism.GaussJetBounds.StatementI
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open MvPolynomial

section Slices

variable {R : Type u} [CommRing R] {T σ ρ : Type}

end Slices

section Rows

end Rows

section Jets

lemma jetPair_monomial_left {K : Type u} [Field K] {ι : Type} (κ : ι →₀ ℕ)
    (F : MvPowerSeries ι K) :
    jetPair (monomial κ (1 : K)) F = ((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ F := by
  classical
  rw [jetPair_eq_sum _ _ {κ} (MvPolynomial.support_monomial_subset)]
  simp

end Jets

section Sums

end Sums

section Frames

variable {K : Type u} [Field K] {H : Type} {N0 : ℕ}

def bM (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (τ : Bool × H) : Matrix (Fin N0) (Fin N0) K :=
  if τ.1 = true then ((x (false, τ.2))⁻¹).transpose else x (false, τ.2)

def bT (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (τ : Bool × H) : Matrix (Fin N0) (Fin N0) K :=
  if τ.1 = true then x τ * (x (false, τ.2)).transpose else 1

end Frames

section Norms

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {H : Type} {N0 : ℕ}

end Norms

end Formalism.DworkPowerSeriesWeights
