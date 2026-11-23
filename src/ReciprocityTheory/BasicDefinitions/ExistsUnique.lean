module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Defs.Basic

@[expose] public section

namespace ReciprocityTheory.Def

open IsLocalRing Matrix

universe u v w w'

class IsCNL (O : Type u) (A : Type w) [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A]
    [Algebra O A] : Prop where
  noeth : IsNoetherianRing A
  complete : IsAdicComplete (maximalIdeal A) A
  localHom : IsLocalHom (algebraMap O A)
  resSurj : Function.Surjective fun x : O => residue A (algebraMap O A x)

attribute [instance] IsCNL.noeth IsCNL.complete IsCNL.localHom

structure Pattern (n : ℕ) where
  rel : Fin n → Fin n → Prop
  refl : ∀ i, rel i i
  trans : ∀ i j l, rel i j → rel j l → rel i l

namespace Pattern

variable {n : ℕ}

end Pattern

section Lift

variable (O : Type u) [CommRing O] [IsLocalRing O]
variable {G : Type v} [Group G] [TopologicalSpace G] {n : ℕ}

def push {A : Type w} {B : Type w'} [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] (f : A →ₐ[O] B)
    (ρ : G →* GL (Fin n) A) : G →* GL (Fin n) B :=
  (Matrix.GeneralLinearGroup.map f.toRingHom).comp ρ

end Lift

end ReciprocityTheory.Def
