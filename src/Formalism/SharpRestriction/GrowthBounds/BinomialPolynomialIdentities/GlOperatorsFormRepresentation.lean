module

public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.IntegralJointTypeSum
public import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GrowthBounds.RootWeights.TwistSubEqMatrixSubst

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints Formalism.MainNotions.LemmaBAlt

def GlOperatorsFormRepresentation : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N m k : ℕ) (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k),
    Function.Injective e → IsGLRep (glOpsE F LL S e)

def IsotypicZeroOfNonDominant : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N m k : ℕ) (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k),
    Function.Injective e → ∀ a : Fin m → ℤ, ¬ Dominant a → isoSub (glOpsE F LL S e) a = ⊥

def ProjectorsPreserveMultidegree : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N m k : ℕ) (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k),
    Function.Injective e → ∀ pr : (Fin m → ℤ) → Module.End F (MvPolynomial (Fin N × Fin k) F),
    DecSys (isoSub (glOpsE F LL S e)) pr → ∀ (B : Fin N → ℕ) (a : Fin m → ℤ), ∀ x ∈ Pol F k B, pr a x ∈ Pol F k B

def TypeSumsByEvaluation : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N m k : ℕ) (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k)
    (dcd : Fin k → Option (Fin m)), (∀ a, dcd (e a) = some a) → (∀ c a, dcd c = some a → c = e a) →
    ∀ (pi : Set (Fin m → ℤ)) (x : MvPolynomial (Fin N × Fin k) F),
    (x ∈ ⨆ a ∈ pi, isoSub (glOpsE F LL S e) a) ↔ ∀ y, Tev dcd y x ∈ ⨆ a ∈ pi, isoSub (glOps F m LL S) a

def ProjectorsCommuteNested : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N m k : ℕ) (LL : Letters (Fin N)) (S S' : Set (Fin N)) (e : Fin m → Fin k),
    Function.Injective e → (S ⊆ S' ∨ S' ⊆ S) →
    ∀ pr pr' : (Fin m → ℤ) → Module.End F (MvPolynomial (Fin N × Fin k) F),
    DecSys (isoSub (glOpsE F LL S e)) pr → DecSys (isoSub (glOpsE F LL S' e)) pr' →
    ∀ a b, pr a * pr' b = pr' b * pr a

def ProjectorsCommuteDisjoint : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N m m' k : ℕ) (LL : Letters (Fin N)) (S S' : Set (Fin N))
    (e : Fin m → Fin k) (e' : Fin m' → Fin k), Function.Injective e → Function.Injective e' →
    (∀ a a', e a ≠ e' a') →
    ∀ (pr : (Fin m → ℤ) → Module.End F (MvPolynomial (Fin N × Fin k) F))
      (pr' : (Fin m' → ℤ) → Module.End F (MvPolynomial (Fin N × Fin k) F)),
    DecSys (isoSub (glOpsE F LL S e)) pr → DecSys (isoSub (glOpsE F LL S' e')) pr' →
    ∀ a b, pr a * pr' b = pr' b * pr a

def ExternalProductBasis : Prop :=
  ∀ (R : Type) [CommRing R] (N r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ),
    LinearIndependent R (pvec R r K LL B) ∧ Submodule.span R (Set.range (pvec R r K LL B)) = Pol R (r + K) B

def RestLowPl : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (i : Fin (N + 1))
    (pi : Set (Fin r → ℤ)), DomLowerSet pi →
    Pol F (r + K) B ⊓ (⨆ a ∈ pi, isoSub (glOpsE F LL {j | j.val < i.val} (Fin.castAdd K)) a) =
      Submodule.span F (pvec F r K LL B '' {x | x.1.1.1 i ∈ pi})

def RestLowTan : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (i : Fin (N + 1))
    (pi : Set (Fin K → ℤ)), DomLowerSet pi →
    Pol F (r + K) B ⊓ (⨆ a ∈ pi, isoSub (glOpsE F LL {j | j.val < i.val} (Fin.natAdd r)) a) =
      Submodule.span F (pvec F r K LL B '' {x | x.1.2.1 i ∈ pi})

end Formalism.MainNotions.G.ColumnFamilies
