module

public import Formalism.SharpRestriction.GrowthBounds.ObjPol
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def highestWeightVectors {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (lam : Fin n → ℤ) :
    Submodule K V :=
  weightSp E lam ⊓ ⨅ a : Fin n, ⨅ b : Fin n, ⨅ (_ : a < b), LinearMap.ker (E a b)

def generatedSubrep {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (h : V) :
    Submodule K V :=
  Submodule.span K {x | ∃ u ∈ Umon E, x = u h}

def IsotypicProjectorFixedMem : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ (lam : Fin n → ℤ) (e : Module.End K V), IsIsoProj E lam e →
      ∀ Y : V, e Y = Y → Y ∈ isoSub E lam

def GeneratedMultipleOfHWV : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ (lam : Fin n → ℤ) (h : V), h ∈ highestWeightVectors E lam →
      generatedSubrep E h ≤ Submodule.span K {h} ⊔ ⨆ mu ∈ {mu : Fin n → ℤ | mu ≠ lam}, (weightSp E mu ⊓ generatedSubrep E h)

def DualLatticeDivisibility : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    [FiniteDimensional (KK O) V] (M : Submodule O V), M.FG → MQ (K := KK O) M = ⊤ →
    ∀ (t : KK O) (z : V),
      (∀ f : V →ₗ[KK O] KK O, (∀ x ∈ M, ∃ o : O, f x = algebraMap O (KK O) o) →
        ∃ o : O, f z = t * algebraMap O (KK O) o) →
      ∃ m ∈ M, z = t • m

def LatticeSubspaceBasis : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    [FiniteDimensional (KK O) V] (M : Submodule O V), M.FG → MQ (K := KK O) M = ⊤ →
    ∀ H : Submodule (KK O) V, ∃ (k : ℕ) (h : Fin k → V), (∀ j, h j ∈ M ∧ h j ∈ H) ∧
      LinearIndependent (KK O) h ∧ H ≤ Submodule.span (KK O) (Set.range h) ∧
      ∀ x ∈ M, x ∈ H → ∃ o : Fin k → O, x = ∑ j, o j • h j

def GeneratedLatticeCorollary : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) [NeZero n] (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
      [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M →
      ∀ lam : Fin n → ℤ, Dominant lam →
      ∀ π : Module.End (KK O) V, IsWtProj E lam π →
      ∀ h : V, h ∈ M → h ∈ highestWeightVectors E lam → h ≠ 0 →
      ∀ (c : ℤ) (y : V), y ∈ generatedSubrep E h →
        (∀ u ∈ UZmon E, ∃ o : O, π (u y) = ((p : KK O) ^ c * algebraMap O (KK O) o) • h) →
        ∃ m ∈ M, y = ((p : KK O) ^ (c - ((N0 n * deF p n (ellWt lam) : ℕ) : ℤ))) • m

end Formalism.MainNotions.G.GLWeightTheory
