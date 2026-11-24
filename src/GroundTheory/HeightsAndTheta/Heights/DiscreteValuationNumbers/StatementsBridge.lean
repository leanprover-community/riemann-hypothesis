module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def VocabMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (s : MRing ι R) (a : K → ℕ),
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a ↔ IsMultiHomog s a

def VocabMultiHomogIdeal.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι R)),
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal P ↔ IsMultiHomogIdeal P

def VocabDivCycle.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι R)) (s : MRing ι R) (W : Ideal (MRing ι R)),
    ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W : ℕ) : ℤ) = divCycle P s W

def IntNumPoint.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (i : ∀ k, ι k), IsMultiProjPrime V →
    ringKrullDim (MRing ι F ⧸ V) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    (∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V) →
    intNum F V (![] : Fin 0 → K → ℤ) = ReciprocityTheory.ChartRestriction.G.AI.I1.ptDeg V i

def IntNumRatSection.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (V : Ideal (MRing ι F)), IsMultiProjPrime V →
    ringKrullDim (MRing ι F ⧸ V) = ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (L : Fin n → K → ℤ) (A : K → ℤ) (f g : MRing ι F) (α β : K → ℕ),
      IsMultiHomog f α → IsMultiHomog g β → f ∉ V → g ∉ V → (∀ k, (α k : ℤ) - β k = A k) →
      intNum F V (Fin.snoc (α := fun _ => K → ℤ) L A) =
        cycEval (fun W => intNum F W L) (ratDiv V f g)

def IntNumIsFieldIntersection.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)],
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection (F := F) (ι := ι) (fun V _ L => intNum F V L)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
