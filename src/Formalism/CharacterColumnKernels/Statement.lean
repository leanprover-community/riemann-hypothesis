module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset Polynomial

noncomputable section

namespace Formalism.NG

section Idem

variable {T A : Type*} [CommRing T] [Ring A] [Algebra T A]

end Idem

section Pres

variable {R : Type*} [Ring R] {m g : Type*} [Fintype m] [Fintype g]

def relSpan (Θ : Matrix m g R) : Submodule R (g → R) := Submodule.span R (Set.range Θ)

abbrev Coker (Θ : Matrix m g R) : Type _ := (g → R) ⧸ relSpan Θ

def relMap (O : Type*) [CommRing O] (M : Type*) [AddCommGroup M] [Module R M] [Module O M]
    [SMulCommClass R O M] (Θ : Matrix m g R) : (g → M) →ₗ[O] (m → M) where
  toFun v i := ∑ j, Θ i j • v j
  map_add' v w := by ext i; simp [smul_add, Finset.sum_add_distrib]
  map_smul' c v := by ext i; simp [Finset.smul_sum, smul_comm]

end Pres

section DVR

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

abbrev KO : Type _ := FractionRing O ⧸ (1 : Submodule O (FractionRing O))

def matQ {ι : Type*} [Fintype ι] (A : Matrix ι ι O) : (ι → KO O) →ₗ[O] (ι → KO O) :=
  relMap O (KO O) A

end DVR

def StatLenKer : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ι : Type) [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι O),
    Module.length O (LinearMap.ker (matQ O A)) = IsDiscreteValuationRing.addVal O A.det

def bigMat {R O : Type*} [CommRing O] {g d : Type*} (ρ : R → Matrix d d O) (Θ : Matrix g g R) :
    Matrix (g × d) (g × d) O :=
  fun p q => ρ (Θ p.1 q.1) p.2 q.2

abbrev baseChange {T : Type*} (T' : Type*) [CommRing T] [CommRing T'] [Algebra T T'] (J : Ideal T) :
    Type _ :=
  T' ⧸ Ideal.map (algebraMap T T') J

end Formalism.NG
