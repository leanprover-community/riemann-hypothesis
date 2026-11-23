module

public import Formalism.ThetaLogCoordinates.SandwichModelDomains.StatementW
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FockR
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility Formalism.InvariantFactorPaths.INST

def WeylPair : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [CharZero K]
    (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∀ P ∈ (weyl O r n hn ν).map (toK O K), ∀ Q ∈ (dualWeyl O r n ν).map (toK O K),
      ∃ z : O, fockR P Q = algebraMap O K z * fockR (hw K hn ν) (hw K hn ν)

def DualWeylIn : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [CharZero K]
    (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ Q ∈ dualWeyl K r n ν,
    (∀ P ∈ (weyl O r n hn ν).map (toK O K), ∃ z : O, fockR P Q = algebraMap O K z * fockR (hw K hn ν) (hw K hn ν)) →
    Q ∈ (dualWeyl O r n ν).map (toK O K)

def NondegK : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (r n : ℕ) (_hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ Q ∈ dualWeyl K r n ν,
    (∀ P ∈ dualWeyl K r n ν, fockR P Q = 0) → Q = 0

def FormCoreG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CharZero K], ¬ IsUnit ((p : ℕ) : O) →
    ∀ (r n : ℕ) (_hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∃ B : MvPolynomial (Fin r × Fin n) K →ₗ[K] MvPolynomial (Fin r × Fin n) K →ₗ[K] K,
      (∀ (g : Matrix (Fin r) (Fin r) K) (P Q : MvPolynomial (Fin r × Fin n) K),
        B (rowAct K g P) Q = B P (rowAct K g.transpose Q)) ∧
      (∀ Q ∈ dualWeyl K r n ν, (∀ P ∈ dualWeyl K r n ν, B P Q = 0) → Q = 0) ∧
      (∀ Q ∈ dualWeyl K r n ν,
        (∀ P ∈ (dualWeyl O r n ν).map (toK O K), B P Q ∈ Set.range (algebraMap O K)) → Q ∈ (dualWeyl O r n ν).map (toK O K)) ∧
      (∀ l : ℕ, LBound r ν l → ∀ Q ∈ (dualWeyl O r n ν).map (toK O K), ∀ P ∈ (dualWeyl O r n ν).map (toK O K),
        B P (((p : K) ^ sExp p r l) • Q) ∈ Set.range (algebraMap O K)) ∧
      ((∀ t, ν t = 0) → ∀ Q ∈ (dualWeyl O r n ν).map (toK O K), ∀ P ∈ (dualWeyl O r n ν).map (toK O K),
        B P Q ∈ Set.range (algebraMap O K))

end Formalism.L2.G.Model.TS
