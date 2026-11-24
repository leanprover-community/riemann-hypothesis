module

public import Development.AutomorphicArithmetic.PrimitiveCosets.RecH
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

open UpperTheory.Comparison₂ Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost NumberField Ideal

theorem UpperTheory.GL.unram :
    ∀ {φ : Frame} (H : HostRaw φ) (p : ℕ) (hc : p.Coprime H.condN), p.Prime →
      (arith H).inertia p = ⊥ ∧ (arith H).frob p = (recH H (ZMod.unitOfCoprime p hc)).toAdd := by
  intro φ H p hc hp
  have hN : H.condN ≠ 0 := (Nat.mul_pos (Nat.mul_pos H.QS_pos H.hyp.1.pos) H.hyp.2.1.pos).ne'
  have hnd : ¬ p ∣ H.condN := fun h => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc h)
  obtain ⟨hloc, hfrob⟩ := Formalism.LFunctionChainParameters.LHost.unramified_spec H.condN p hN hp hnd
  constructor
  · show Subgroup.toAddSubgroup' (Subgroup.map (recH H) (Formalism.LFunctionChainParameters.LHost.localUnits H.condN p)) = ⊥
    rw [hloc, Subgroup.map_bot]
    exact Subgroup.toAddSubgroup'.map_bot
  · show (recH H (Formalism.LFunctionChainParameters.LHost.frobUnit H.condN p)).toAdd = _
    have he : Formalism.LFunctionChainParameters.LHost.frobUnit H.condN p = ZMod.unitOfCoprime p hc :=
      Units.ext (by rw [hfrob, ZMod.coe_unitOfCoprime])
    rw [he]
