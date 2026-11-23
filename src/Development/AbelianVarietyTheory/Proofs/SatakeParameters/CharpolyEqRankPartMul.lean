module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Algebra.Polynomial.Coeff
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

namespace GlobalTheory.CharpolyFrobDense

def CoeffCont {Γ K : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K] (F : Γ → K[X]) : Prop :=
  ∀ k, Continuous fun g => (F g).coeff k

theorem CoeffCont.mul {Γ K : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {F F' : Γ → K[X]} (h : CoeffCont F) (h' : CoeffCont F') :
    CoeffCont (F * F') := by
  intro k
  simp only [Pi.mul_apply, coeff_mul]
  exact continuous_finsetSum _ fun x _ => (h x.1).mul (h' x.2)

theorem coeffCont_one {Γ K : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K] :
    CoeffCont (1 : Γ → K[X]) := fun _ => continuous_const

theorem coeffCont_X_sub_C {Γ K : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {a : Γ → K} (ha : Continuous a) :
    CoeffCont fun g => (X - C (a g)) := by
  intro k
  rcases k with _ | _ | k
  · simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
    exact ha.neg
  · simpa using continuous_const
  · simp only [coeff_sub, coeff_X, coeff_C]
    simpa using continuous_const

theorem coeffCont_prod {Γ K ι : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (s : Finset ι) (F : ι → Γ → K[X]) (h : ∀ c ∈ s, CoeffCont (F c)) :
    CoeffCont fun g => ∏ c ∈ s, F c g := by
  have : (fun g => ∏ c ∈ s, F c g) = ∏ c ∈ s, F c := by
    funext g; simp [Finset.prod_apply]
  rw [this]
  exact Finset.prod_induction _ (fun G => CoeffCont G) (fun _ _ ha hb => ha.mul hb) coeffCont_one h

end GlobalTheory.CharpolyFrobDense
