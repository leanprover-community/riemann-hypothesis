module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def normForm (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S] {n : ℕ}
    (η : Fin n → S) : MvPolynomial (Fin n) R := by
  classical
  exact (Matrix.of fun i j =>
    ∑ m, X m * C (Algebra.leftMulMatrix (Module.Free.chooseBasis R S) (η m) i j)).det

def NormFormEval.Statement : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S] (n : ℕ)
    (η : Fin n → S) (u : Fin n → R),
    eval u (normForm R S η) = Algebra.norm R (∑ m, u m • η m)

def NormFormEmbeddings.Statement : Prop :=
  ∀ (K L Ω : Type) [Field K] [Infinite K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (n : ℕ) (η : Fin n → L),
    map (algebraMap K Ω) (normForm K L η) = ∏ σ : L →ₐ[K] Ω, ∑ m, X m * C (σ (η m))

def LinearFormPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (a : Fin n → F), a ≠ 0 →
    Prime (∑ m, X m * C (a m) : MvPolynomial (Fin n) F)

def MapDvdDescent.Statement : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (σ : Type) (f g : MvPolynomial σ K),
    map (algebraMap K Ω) f ∣ map (algebraMap K Ω) g → f ∣ g

def NormFormDvd.Statement : Prop :=
  ∀ (K L : Type) [Field K] [Infinite K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (n : ℕ) (η : Fin n → L) (t : Fin n → K) (P : MvPolynomial (Fin n) K),
    Algebra.adjoin K (Set.range η) = ⊤ → ∑ m, t m • η m = 1 →
      (∑ m, X m * C (η m)) ∣ map (algebraMap K L) P → normForm K L η ∣ P

def PrimeMapFractionRing.Statement : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (n : ℕ)
    (P : MvPolynomial (Fin n) O),
    Prime P → (∀ a : O, P ≠ C a) → Prime (map (algebraMap O K) P)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
