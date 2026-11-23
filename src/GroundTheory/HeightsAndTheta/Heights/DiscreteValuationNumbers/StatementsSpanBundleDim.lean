module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SpanBundleDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (M i : ℕ) (G : Fin M → Fin i → Ω), 0 < i → LinearIndependent Ω (fun j l => G l j) →
    ∀ (c : ∀ k, ι k) (a : K → ℤ) (H : Matrix (Fin i) (Fin i) Ω), segreVec y c ≠ 0 → IsUnit H.det →
      (∀ l m, (Matrix.of G * H) l m ∈ degLat F y a c) →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (s : Fin i → Φ), AlgebraicIndependent Ω s →
      IsMultiProjPrime (projIdeal F y (Pi.basisFun Ω (Fin i))
          (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) ∧
        FieldNumbers.relDim (projIdeal F y (Pi.basisFun Ω (Fin i))
          (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) =
          ((e + i - 1 : ℕ) : WithBot (WithTop ℤ))

end

end GroundTheory.Heights₂.Heights.NumbersDVR
