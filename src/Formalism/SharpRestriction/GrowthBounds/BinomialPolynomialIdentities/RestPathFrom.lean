module

public import Formalism.SharpRestriction.GrowthBounds.ObjPol
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.IndexWeightsDominance
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GrowthBounds.ConclusionA2

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def isV {N : ℕ} (LL : Letters (Fin N)) : ℕ → Bool := fun i => if h : i < N then LL.vec ⟨i, h⟩ else true

def Bn {N : ℕ} (B : Fin N → ℕ) : ℕ → ℕ := fun i => if h : i < N then B ⟨i, h⟩ else 0

def ext {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : ℕ → Fin n → ℤ := fun i => if h : i < N + 1 then mu ⟨i, h⟩ else 0

def res (N : ℕ) {n : ℕ} (μ : ℕ → Fin n → ℤ) : Fin (N + 1) → Fin n → ℤ := fun i => μ i.val

def iv (N n : ℕ) : Fin N × Fin n → ℕ × Fin n := fun x => (x.1.val, x.2)

def RestPathTo : Prop :=
  ∀ (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (P : PPath n N LL B),
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsPath n (isV LL) (Bn B) (ext P.mu) N

def RestPathFrom : Prop :=
  ∀ (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (μ : ℕ → Fin n → ℤ),
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsPath n (isV LL) (Bn B) μ N → ∃ P : PPath n N LL B, P.mu = res N μ

def RestStd : Prop :=
  ∀ (n N : ℕ) (mu : Fin (N + 1) → Fin n → ℤ) (I : ℤ → Finset (Fin n)),
    IsSt mu I ↔ Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsStd (pEnd mu) I

def RestPsi : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (P : PPath n N LL B)
    (I : ℤ → Finset (Fin n)), Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex (pEnd P.mu) I →
    rename (iv N n) (Psi R P.mu I) = Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath R (isV LL) (ext P.mu) N I

def RestPol : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (B : Fin N → ℕ),
    (Pol R n B).map (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toLinearMap =
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.polB R n N (Bn B)

end Formalism.MainNotions.G.ColumnFamilies
