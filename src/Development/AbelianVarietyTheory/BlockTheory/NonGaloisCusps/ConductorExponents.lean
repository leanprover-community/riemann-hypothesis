module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents

open PowerSeries GlobalTheory.BK

def eW (N r : ℕ) : ℕ := 2 * (N - 1) * r

def eL (N η : ℕ) : ℕ := (N + 1) * η

def c₁ (η r : ℕ) : ℕ := η * (r + 1)

def c₂ (N η r : ℕ) : ℕ := c₁ η r + eW N r

def kExp (N η r : ℕ) : ℕ := c₂ N η r + η + eL N η + eW N r

structure Numerics (l e N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ) : Prop where
  frob_mem : ∀ c ∈ Sig, (l : ZMod e) * c ∈ Sig
  zero_mem_Sig : (0 : ZMod e) ∈ Sig
  card_Sig : Sig.card ≤ N
  two_le : 2 ≤ N
  range_U : ∀ i ∈ U, -(η : ℤ) ≤ i ∧ i ≤ H
  zero_mem_U : (0 : ℤ) ∈ U
  card_U : U.card ≤ N + 1
  one_le : 1 ≤ η
  lt : η < H
  large : 40 * (H * N ^ 2 + N ^ 3) < l

section

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a] {ι₀ ι₁ ι₂ : Type} [Fintype ι₀] [DecidableEq ι₀] [Fintype ι₁]
  [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] {η H : ℕ}
  {D₀ : BKDat O K l e a ι₀ η H} {D₁ : BKDat O K l e a ι₁ η H} {D₂ : BKDat O K l e a ι₂ η H}

def Hyp (F : BKHom D₀ D₁) (G : BKHom D₁ D₂) (N : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ) : Prop :=
  IsExactTriple F.toHom G.toHom ∧ Numerics l e N η H Sig U ∧
    D₁.IsOfType (Sig : Set (ZMod e)) (U : Set ℤ) ∧ ∀ τ, D₂.desc.chars τ ⊆ (Sig : Set (ZMod e))

def Lifts (G : BKHom D₁ D₂) (k : ℕ) (y₂' m₂ : Vec K a ι₂) : Prop :=
  ∃ y' ∈ D₁.Y', ∃ m ∈ D₁.Minv, D₁.Mon (y' + D₁.phi m) = 0 ∧
    G.app (y' + D₁.phi m) = (l : K) ^ k • (y₂' + D₂.phi m₂)

end

def Lifting : Prop :=
  ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] [CompleteSpace K] (ι₀ ι₁ ι₂ : Type) [Fintype ι₀] [DecidableEq ι₀]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] (η H : ℕ)
    (D₀ : BKDat O K l e a ι₀ η H) (D₁ : BKDat O K l e a ι₁ η H) (D₂ : BKDat O K l e a ι₂ η H)
    (F : BKHom D₀ D₁) (G : BKHom D₁ D₂) (N : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ),
    Hyp F G N Sig U → ∀ y₂' ∈ D₂.Y', ∀ m₂ ∈ D₂.Minv, D₂.Mon (y₂' + D₂.phi m₂) = 0 →
      Lifts G (kExp N η (maxPeriod l Sig)) y₂' m₂

end GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents
