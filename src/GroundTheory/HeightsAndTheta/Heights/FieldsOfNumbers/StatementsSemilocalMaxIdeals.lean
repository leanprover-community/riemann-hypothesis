module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalLengthSum
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

abbrev degZeroLoc.algebraOfSubset {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (P : Ideal (MRing ι F)) [P.IsPrime] {𝒲₁ 𝒲₂ : Set (Ideal (MRing ι F))} (h𝒲 : 𝒲₁ ⊆ 𝒲₂) :
    Algebra (degZeroLoc P 𝒲₂) (degZeroLoc P 𝒲₁) :=
  (Subalgebra.inclusion (degZeroLoc_anti P h𝒲)).toRingHom.toAlgebra


set_option synthInstance.maxHeartbeats 100000 in
set_option synthInstance.maxHeartbeats 400000 in
def SemilocalMaxIdeals.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
      haveI := hP'.isPrime
      ∃ (𝔪 : fibrePrimes j P' W → Ideal (degZeroLoc P' (fibrePrimes j P' W)))
        (h𝔪 : ∀ W', (𝔪 W').IsMaximal),
        Function.Injective 𝔪 ∧
        (∀ M : Ideal (degZeroLoc P' (fibrePrimes j P' W)), M.IsMaximal → ∃ W', M = 𝔪 W') ∧
        ∀ W' : fibrePrimes j P' W,
          (haveI := (h𝔪 W').isPrime
           letI := degZeroLoc.algebraOfSubset P' (Set.singleton_subset_iff.mpr W'.2)
           IsLocalization.AtPrime (degZeroLoc P' {W'.1}) (𝔪 W')) ∧
          haveI := W'.2.1.isPrime
          Module.length (degZeroLoc (contractPrime j P') {W})
              (degZeroLoc P' (fibrePrimes j P' W) ⧸ 𝔪 W') = (relDeg j W'.1 : ℕ∞)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
