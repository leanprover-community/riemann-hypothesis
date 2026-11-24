module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def conjIdeal (H : Host E) (P : Ideal (𝓞 E)) : Ideal (𝓞 E) := P.map (H.bar : 𝓞 E →+* 𝓞 E)

def IsSplitPrimeOff (l : Level H) (p : ℕ) (P : Ideal (𝓞 E)) : Prop :=
  p.Prime ∧ P.IsMaximal ∧ (p : 𝓞 E) ∈ P ∧ conjIdeal H P ≠ P ∧ ¬ p ∣ l.M'

section Fibre

variable {k : Type} [Field k]

abbrev Pts (t : SAB H (Sp k)) : Type := 𝟙_ (Over (Sp k)) ⟶ t.G

def KilledBy (t : SAB H (Sp k)) (I : Ideal (𝓞 E)) (x : Pts t) : Prop :=
  ∀ a ∈ I, x ≫ t.act.act a = 1

def KilledByPow (t : SAB H (Sp k)) (I : Ideal (𝓞 E)) (x : Pts t) : Prop :=
  ∃ n : ℕ, KilledBy t (I ^ n) x

def IsHeckeDatum (t : SAB H (Sp k)) (P : Ideal (𝓞 E)) (i : ℕ) (C₀ : Subgroup (Pts t)) : Prop :=
  (∀ a, ∀ x ∈ C₀, x ≫ t.act.act a ∈ C₀) ∧ (∀ x ∈ C₀, KilledBy t (conjIdeal H P) x) ∧
    Finite C₀ ∧ Nat.card C₀ = Ideal.absNorm P ^ i

def heckeKernel (t : SAB H (Sp k)) (p : ℕ) (P : Ideal (𝓞 E)) (C₀ : Subgroup (Pts t)) : Set (Pts t) :=
  {x | ∃ x₁ x₂ x₃ : Pts t, x = x₁ * x₂ * x₃ ∧
    (x₁ ^ p = 1 ∧ ∃ a : 𝓞 E, a ∉ P ∧ a ∉ conjIdeal H P ∧ x₁ ≫ t.act.act a = 1) ∧
    (KilledByPow t (conjIdeal H P) x₂ ∧ x₂ ^ p ∈ C₀) ∧
    (x₃ ^ p = 1 ∧ KilledByPow t P x₃ ∧ ∀ c ∈ C₀, Out.WeilIs t.G t.PP.L (p : ℤ) x₃ c 1)}

end Fibre

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels
