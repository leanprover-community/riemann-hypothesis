module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def AddAt {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (n : ℕ) : Prop :=
  ∀ (W : Ideal (MRing ι)) (L : Fin n → HermLine ι) (A C : HermLine ι),
    IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm C →
    I W (n + 1) (Fin.snoc L (A.tensor C)) = I W (n + 1) (Fin.snoc L A) + I W (n + 1) (Fin.snoc L C)

def RPositionAdd.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A C B : HermLine ι) (s : MRing ι),
    AddAt I n → IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSmoothHerm C → IsSmoothHerm B → IsSectionOn P B s →
    recR I P (Fin.snoc L (A.tensor C)) B s = recR I P (Fin.snoc L A) B s + recR I P (Fin.snoc L C) B s

def WellDefined.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin (n + 1) → HermLine ι) (B : HermLine ι) (s t : MRing ι),
    HasRAt I n → AddAt I n → IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm B →
    IsSectionOn P B s → IsSectionOn P B t → recR I P L B s = recR I P L B t

end

end GroundTheory.Heights₂.Heights.Inter
