module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RdArith
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.rho_art :
    ∀ {φ : Frame} (H : HostRaw φ) {f : ℕ}, f ∣ H.condN → Formalism.HC.Der.Rd.rho H.art.ker f = 1 - 1 / (Nat.card (H.imgOne f) : ℝ) := by
  intro φ H f hf
  classical
  rw [Formalism.HC.Der.Rd.rho_eq _ hf]
  have h1 := (H.art.ker.subgroupOf (H.unitsOne f)).card_mul_index
  have h2 : (H.art.ker.subgroupOf (H.unitsOne f)).index = Nat.card (H.imgOne f) :=
    Subgroup.relIndex_ker (H.unitsOne f) H.art
  have h3 : Nat.card (H.unitsOne f) = (Formalism.HC.Der.Rd.KK H.condN f).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => by
      rw [Formalism.HC.Der.Rd.mem_KK, H.mem_unitsOne hf])
  have h4 : Nat.card (H.art.ker.subgroupOf (H.unitsOne f)) =
      ((Formalism.HC.Der.Rd.KK H.condN f).filter fun u => u ∈ H.art.ker).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (fun u => u ∈ H.unitsOne f)
      (fun u => u ∈ H.art.ker)).trans (Equiv.subtypeEquivRight fun u => ?_))
    rw [Finset.mem_filter, Formalism.HC.Der.Rd.mem_KK, H.mem_unitsOne hf]
  rw [h2, h3, h4] at h1
  have h5 := Formalism.HC.Der.Rd.card_KK hf
  rw [← h1] at h5
  have h6 := congrArg (Nat.cast : ℕ → ℝ) h5
  push_cast at h6
  have hN : (H.condN.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos H.condN)).ne'
  have hI : (Nat.card (H.imgOne f) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  congr 1
  rw [div_eq_div_iff hN hI, one_mul, ← h6]
  rw [mul_right_comm]
  congr!
