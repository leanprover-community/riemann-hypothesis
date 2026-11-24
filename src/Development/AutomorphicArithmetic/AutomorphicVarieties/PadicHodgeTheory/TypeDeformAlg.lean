module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Map
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

@[expose] public section

open TensorProduct

namespace UpperTheory.V.Loc.Thick

variable {Q E B : Type} [Field Q] [Field E] [CommRing B] [Algebra Q E] [Algebra Q B] [Algebra E B]
  [IsScalarTower Q E B] (π : B →ₐ[E] E)

variable {π}

section

variable {X X' : Type} [AddCommGroup X] [Module B X] [Module Q X] [AddCommGroup X'] [Module E X'] [Module Q X']
  {p : X →ₗ[Q] X'} {Λ : (B →ₗ[E] E) → X →ₗ[Q] X'}

variable [IsScalarTower Q B X] [IsScalarTower Q E X']

end

section Sm

variable {A V : Type} [CommRing A] [Algebra Q A] [AddCommGroup V] [Module A V] [Module Q V] [IsScalarTower Q A V]
  {F P : Type} [Field F] [Algebra Q F] [CommRing P] [Algebra Q P] [Algebra F P] [IsScalarTower Q F P]


variable (V P) in
noncomputable def sm : A ⊗[Q] F →ₗ[Q] Module.End Q (V ⊗[Q] P) :=
  (TensorProduct.homTensorHomMap (RingHom.id Q) V P V P).comp
    (TensorProduct.map (Algebra.lsmul Q Q V : A →ₐ[Q] Module.End Q V).toLinearMap
      (Algebra.lsmul Q Q P : F →ₐ[Q] Module.End Q P).toLinearMap)

variable {A' V' : Type} [CommRing A'] [Algebra Q A'] [AddCommGroup V'] [Module A' V'] [Module Q V']
  [IsScalarTower Q A' V']

end Sm

end UpperTheory.V.Loc.Thick
