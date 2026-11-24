module

public import GroundTheory.AutomorphicForms.DefiniteClassNumber.HermTraceSelfOfHermValue
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
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

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]

section TotallyReal

abbrev realEmb (hreal : ∀ w : InfinitePlace K, w.IsReal) (w : InfinitePlace K) : K →+* ℝ :=
  embedding_of_isReal (hreal w)

end TotallyReal

section Form

variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

def traceGram : Matrix (ι × κ) (ι × κ) K :=
  fun a c => hermTrace K H K (stdVec K b a) (stdVec K b c)

variable (R : Type*) [CommRing R] [Algebra K R]

def vecOfCoords (c : ι × κ → R) : ι → R ⊗[K] E :=
  fun i => (Algebra.TensorProduct.basis R b).equivFun.symm fun k => c (i, k)

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
theorem vecCoords_vecOfCoords (c : ι × κ → R) : vecCoords R b (vecOfCoords b R c) = c := by
  funext a
  simp only [vecCoords, vecOfCoords]
  rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

variable {H b}


omit [NumberField K] in
theorem hermTrace_eq_sum_traceGram (x y : ι → R ⊗[K] E) :
    hermTrace K H R x y = ∑ a : ι × κ, ∑ c : ι × κ, vecCoords R b x a * vecCoords R b y c *
      algebraMap K R (traceGram H b a c) :=
  hermTrace_eq_sum H b x y

end Form

end GroundTheory.Automorphic
