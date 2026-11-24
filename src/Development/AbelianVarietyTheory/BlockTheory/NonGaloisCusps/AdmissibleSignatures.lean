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

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures

open GlobalTheory.BK PowerSeries

structure Admissible (l e N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ) : Prop where
  frob_mem : ∀ c ∈ Sig, (l : ZMod e) * c ∈ Sig
  zero_mem_Sig : (0 : ZMod e) ∈ Sig
  card_Sig : Sig.card ≤ N
  two_le : 2 ≤ N
  range_U : ∀ i ∈ U, -(η : ℤ) ≤ i ∧ i ≤ (H : ℤ)
  zero_mem_U : (0 : ℤ) ∈ U
  card_U : U.card ≤ N + 1
  one_le : 1 ≤ η
  lt : η < H
  large : 40 * (H * N ^ 2 + N ^ 3) < l

def cOne (l : ℕ) {e : ℕ} (η : ℕ) (Sig : Finset (ZMod e)) : ℕ := η * (maxPeriod l Sig + 1)

def ZetaBound : Prop :=
  ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
    [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
    (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), Admissible l e N η H Sig U →
    ∀ D : BKDat O K l e a ι η H, D.IsOfType (Sig : Set (ZMod e)) (U : Set ℤ) →
    ∀ y' ∈ D.Y', ∀ m ∈ D.Minv, D.Mon (y' + D.phi m) = 0 →
      (l : K) ^ cOne l η Sig • D.zeta (y' + D.phi m) ∈ D.MM

section Basic₂

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}
  {D : BKDat O K l e a ι η H}

omit [NeZero e]

theorem add_phi_mem_Y {y' m : Vec K a ι} (hy : y' ∈ D.Y') (hm : m ∈ D.Minv) :
    y' + D.phi m ∈ D.Y :=
  add_mem (D.desc.Y'_le_Y η hy)
    ⟨D.upper _ (D.phi_mem_L hm.1), fun g => by rw [D.desc.act_phi, hm.2 g]⟩

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures
