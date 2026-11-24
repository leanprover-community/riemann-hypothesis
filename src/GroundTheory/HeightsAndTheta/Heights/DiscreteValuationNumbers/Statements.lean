module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LocalLengthAdditivityTorsionFree
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

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u v

abbrev LengthFormulaDimTwo.Statement : Prop := ReciprocityTheory.ChartRestriction.G.AI.LocalLengthMultiplicativity.{u}

def ConservationOfNumber.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
      ∀ a : Fin d → K → ℤ,
        cycEval (fun W => vNum W a) (divCycle P (C ϖ)) = gNum P a


open scoped Classical in
open Classical in
def CutByEffectiveDivisor.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
      ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
      ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
      (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
      ∀ L : Fin d → K → ℤ,
        cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P f g) =
          cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
              else cycEval (fun G => vNum G L) (ratDiv W f g)) (divCycle P s)

def VerticalDivisorsCommute.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
      ∀ (b b' : K → ℤ) (f g f' g' : MRing ι O),
        IsVerticalDivisor P ϖ b f g → IsVerticalDivisor P ϖ b' f' g' →
      ∀ L : Fin d → K → ℤ,
        cycEval (fun G => vNum G (Matrix.vecCons b' L)) (ratDiv P f g) =
          cycEval (fun G => vNum G (Matrix.vecCons b L)) (ratDiv P f' g')

section Examples

theorem isPrime_of_divCycle_ne_zero {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {f : MRing ι R} {W : Ideal (MRing ι R)} (h : divCycle P f W ≠ 0) :
    W.IsPrime := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact hW.1.1.1
  · exact absurd rfl h

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
