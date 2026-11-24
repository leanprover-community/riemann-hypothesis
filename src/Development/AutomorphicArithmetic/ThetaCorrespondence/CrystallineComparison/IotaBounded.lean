module

public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero
public import GroundTheory.PAdicHodge.ACrisBdR
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

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

abbrev NC : Type := ↥(normInteger ℂ_[l])

def iotaF : ACris.ACris ℂ_[l] l →+* Reformulated.AutPerF.BdRPlus l (NC l) := ACris.iota ℂ_[l] l

theorem iota_bounded (n : ℕ) : ∃ N : ℕ, ∀ x : ACris.ACris ℂ_[l] l, ∃ a : Reformulated.AutPerF.Ainf l (NC l),
    Reformulated.AutPerF.BdRPlus.eval l (NC l) n (((l : ℕ) : Reformulated.AutPerF.BdRPlus l (NC l)) ^ N * iotaF l x) =
      Ideal.Quotient.mk _ (algebraMap (Reformulated.AutPerF.Ainf l (NC l)) (Reformulated.AutPerF.AinfInv l (NC l)) a) := by
  refine ⟨(n - 1).factorial.factorization l, fun x => ?_⟩
  obtain ⟨w, hw⟩ := ACris.pow_mul_mem_latticeQ n _ (ACris.embedding₂ ℂ_[l] l n x).2
  refine ⟨w, ?_⟩
  have h1 : Reformulated.AutPerF.BdRPlus.eval l (NC l) n (iotaF l x) =
      ((ACris.embedding₂ ℂ_[l] l n x : ACris.acrisQ ℂ_[l] l n) : Localization.Away ((l : ℕ) : AInf ℂ_[l] l) ⧸ ACris.kerAway ℂ_[l] l ^ n) := by
    have := ACris.evalₐ_iota (K := ℂ_[l]) (p := l) n x
    rw [ACris.iotaQ.eq_1] at this
    exact this
  rw [map_mul, map_pow, map_natCast, h1]
  exact hw.symm

end Formalism.BasicNotions.CmpTie.Incl
