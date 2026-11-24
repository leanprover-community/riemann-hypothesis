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

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def restrictStableOperators {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (W : Submodule K V)
    (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W) : GLOps n K W := fun a b => (E a b).restrict (h a b)

def CompleteReducibilityIsotypic : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V),
    IsGLRep E → (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤

def ContravariantIsotypicOrthogonal : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V),
    IsGLRep E → ∀ B : V →ₗ[K] V →ₗ[K] K, (∀ a b x y, B (E a b x) y = B x (E b a y)) →
      ∀ lam mu : Fin n → ℤ, lam ≠ mu → ∀ x ∈ isoSub E lam, ∀ y ∈ isoSub E mu, B x y = 0

def HighestWeightDominant : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ lam v, IsHWV E lam v → Dominant lam

def SubrepRestrictionRep : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V),
    IsGLRep E → ∀ (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W),
      IsGLRep (restrictStableOperators E W h) ∧
      (∀ (mu : Fin n → ℤ) (x : W), x ∈ weightSp (restrictStableOperators E W h) mu ↔ (x : V) ∈ weightSp E mu) ∧
      (∀ a b k (x : W), ((divPowE (restrictStableOperators E W h) a b k x : W) : V) = divPowE E a b k x) ∧
      (∀ a k (x : W), ((binomE (restrictStableOperators E W h) a k x : W) : V) = binomE E a k x) ∧
      (∀ lam (e : Module.End K V), IsIsoProj E lam e →
        ∃ e' : Module.End K W, IsIsoProj (restrictStableOperators E W h) lam e' ∧ ∀ x : W, ((e' x : W) : V) = e x) ∧
      (∀ lam (e : Module.End K V), IsIsoProj E lam e → (¬ ∃ v : W, IsHWV (restrictStableOperators E W h) lam v) →
        ∀ x ∈ W, e x = 0)

def PolynomialGLRepresentation : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (LL : Letters ι),
    (∀ S, IsGLRep (glOps K n LL S)) ∧
    (∀ S S' : Set ι, Disjoint S S' → ∀ a b c d,
      glOps K n LL S a b * glOps K n LL S' c d = glOps K n LL S' c d * glOps K n LL S a b) ∧
    (∀ S S' : Set ι, S ⊆ S' → ∀ a b, glOps K n LL S' a b = glOps K n LL S a b + glOps K n LL (S' \ S) a b) ∧
    (∀ S d a b, ∀ F ∈ Pol K n d, glOps K n LL S a b F ∈ Pol K n d) ∧
    (∀ d : ι → ℕ, FiniteDimensional K (Pol K n d)) ∧
    (∀ S mu F, F ∈ weightSp (glOps K n LL S) mu → ∀ m ∈ F.support, wtS LL S m = mu) ∧
    (∃ B : MvPolynomial (ι × Fin n) K →ₗ[K] MvPolynomial (ι × Fin n) K →ₗ[K] K,
      (∀ F G, B F G = fock F G) ∧ ∀ S a b F G, B (glOps K n LL S a b F) G = B F (glOps K n LL S b a G))

def latticeMultidegreePart {O : Type} [CommRing O] [IsDomain O] {ι : Type} {n : ℕ}
    (L : Submodule O (MvPolynomial (ι × Fin n) (KK O))) (d : ι → ℕ) : Submodule O (Pol (KK O) n d) :=
  L.comap (((Pol (KK O) n d).subtype).restrictScalars O)

def AdmissibleDVRIntegralFormLatticesStable : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O → CharZero (KK O) ∧
    ∀ (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι),
      (∀ S : Set ι, PolUZStable LL S (IntPol O (ι × Fin n)) ∧
        ∀ u ∈ polUZgens (KK O) LL S, ∀ F : MvPolynomial (ι × Fin n) (KK O),
          InBB (O := O) p F → InBB (O := O) p (u F)) ∧
      (∀ S : Set ι, ∀ u ∈ UZgens (glOps (KK O) n LL S),
        (∀ F ∈ IntPol O (ι × Fin n), u F ∈ IntPol O (ι × Fin n)) ∧
        ∀ F : MvPolynomial (ι × Fin n) (KK O), InBB (O := O) p F → InBB (O := O) p (u F)) ∧
      ∃ BBs : Submodule O (MvPolynomial (ι × Fin n) (KK O)), (∀ F, F ∈ BBs ↔ InBB (O := O) p F) ∧
        ∀ d : ι → ℕ, (latticeMultidegreePart (IntPol O (ι × Fin n)) d).FG ∧ MQ (K := KK O) (latticeMultidegreePart (IntPol O (ι × Fin n)) d) = ⊤ ∧
          (latticeMultidegreePart BBs d).FG ∧ MQ (K := KK O) (latticeMultidegreePart BBs d) = ⊤

end Formalism.MainNotions.G.GLWeightTheory
