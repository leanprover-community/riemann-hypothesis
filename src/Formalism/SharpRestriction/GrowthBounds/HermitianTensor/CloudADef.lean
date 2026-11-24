module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CloudDefs
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

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def intO (O : Type) {K : Type} [CommRing O] [Field K] [Algebra O K] (k : ℕ) (ν : Fin k → ℕ) :
    Submodule O (MvPolynomial (Fin k × Fin k) K) :=
  Submodule.map (mapAlgHom (Algebra.ofId O K)).toLinearMap (dualWeyl O k k ν)

def Row0 {K : Type} [CommRing K] {k : ℕ} (f : MvPolynomial (Fin (k + 1) × Fin (k + 1)) K) (d : ℕ) : Prop :=
  ∀ u, AddMonoidAlgebra.coeff f u ≠ 0 → rowDeg u 0 = d

def ContractionStandardLattice : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (mm : ℕ), 1 ≤ mm → ∀ (a ccl P Q : ℕ) (lam : Fin (mm + 1 + 1) → ℤ), Antitone lam →
    lam 0 = (P : ℤ) + ccl → lam (Fin.last (mm + 1)) = -((Q : ℤ) + ccl) →
    (∀ i : Fin (mm + 1 + 1), 0 < i.val → i.val < mm + 1 → |lam i| ≤ ccl) → 2 * ccl ≤ 8 * a →
    ∃ abelian₂ : MvPolynomial (Bool × (Fin (mm + 1 + 1) × Fin (mm + 1 + 1))) R.Kf →ₗ[R.Kf]
        MvPolynomial (Fin (mm + 1 + 1) × Fin (mm + 1 + 1)) R.Kf,
      (∀ v ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam),
        ∀ t ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))),
          abelian₂ (blockEmb R.Kf true v * blockEmb R.Kf false t) ∈
            dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl)))) ∧
      (∀ g : Matrix (Fin (mm + 1 + 1)) (Fin (mm + 1 + 1)) R.Kf, IsUnit g.det →
        ∀ v ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam),
        ∀ t ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))),
          abelian₂ (blockEmb R.Kf true (rowAct R.Kf g v) * blockEmb R.Kf false (rowAct R.Kf g t)) =
            rowAct R.Kf g (abelian₂ (blockEmb R.Kf true v * blockEmb R.Kf false t))) ∧
      (∀ v ∈ intO R.O (mm + 1 + 1) (nuOf lam),
        ∀ t ∈ intO R.O (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))),
          abelian₂ (blockEmb R.Kf true v * blockEmb R.Kf false t) ∈
            intO R.O (mm + 1 + 1) (nuOf (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl)))) ∧
      ∃ (nb : ℕ) (s s' : Fin nb → MvPolynomial (Fin (mm + 1 + 1) × Fin (mm + 1 + 1)) R.Kf) (ka : Fin nb → ℕ),
        (nb : ℚ) = weylDim mm (fun j => lam j.castSucc.succ) ∧ (∀ b, ka b ≤ ⌈kappaOneExponent p a (mm + 1)⌉₊) ∧
        (∀ b, s b ∈ intO R.O (mm + 1 + 1) (nuOf (lam - wtPQ (mm + 1) P Q)) ∧ Row0 (s b) (2 * ccl)) ∧
        (∀ a', s' a' ∈ intO R.O (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) ∧ Row0 (s' a') (2 * ccl)) ∧
        ∀ a' b, ∀ F ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) P Q)),
          abelian₂ (blockEmb R.Kf true (F * s b) * blockEmb R.Kf false (s' a')) =
            if a' = b then ((p : R.Kf) ^ ka b) •
              (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl))) * F) else 0

end Formalism.MainNotions.flipOneThree.Pf

end
