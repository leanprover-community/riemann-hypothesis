module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqOfTwoOver
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section
namespace GlobalTheory.BotPairSmallTw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem modT_ne_bot (G : GridData L sc) (t : T) : modT G t ≠ ⊥ := by
  unfold modT
  exact mul_ne_zero (condE_ne_bot G.pl) (Finset.prod_ne_zero_iff.2 fun w _ => w.ne_bot)

theorem absNorm_modT (G : GridData L sc) (t : T) : Ideal.absNorm (modT G t) = levQ G.pl * Qn G t := by
  rw [modT, map_mul, map_prod, GlobalTheory.ModulusNorm.absNorm_condE, Qn]

theorem hatId_mono {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) : hatId D I ≤ hatId D J :=
  AddSubgroup.closure_mono fun _ ⟨b, hb, s, hs, e⟩ => ⟨b, h hb, s, hs, e⟩

theorem modT_mul_conj_le (G : GridData L sc) (t : T) :
    modT G t * D.host.conj • modT G t ≤ condE G.pl * D.host.conj • condE G.pl := by
  have h : modT G t ≤ condE G.pl := by
    show condE G.pl * _ ≤ _
    exact Ideal.mul_le_inf.trans inf_le_left
  exact Ideal.mul_mono h (Ideal.map_mono h)

end GlobalTheory.BotPairSmallTw

end
