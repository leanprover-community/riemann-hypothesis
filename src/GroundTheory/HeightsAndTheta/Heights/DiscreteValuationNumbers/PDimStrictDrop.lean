module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
public import Mathlib.Tactic.Continuity
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem DimStrictDrop.proof : DimStrictDrop.Statement.{u} := by
  intro A _ Q Q' _ _ hlt
  let q : PrimeSpectrum.zeroLocus (R := A) (Q : Set A) :=
    ⟨⟨Q, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl⟩
  have : Nonempty (PrimeSpectrum.zeroLocus (R := A) (Q' : Set A)) :=
    ⟨⟨⟨Q', inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl⟩⟩
  have : Nonempty (PrimeSpectrum.zeroLocus (R := A) (Q : Set A)) := ⟨q⟩
  let f : PrimeSpectrum.zeroLocus (R := A) (Q' : Set A) → PrimeSpectrum.zeroLocus (R := A) (Q : Set A) :=
    fun x => ⟨x.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr
      (le_trans (show (Q : Set A) ⊆ Q' from hlt.le) ((PrimeSpectrum.mem_zeroLocus _ _).mp x.2))⟩
  have hf : StrictMono f := fun a b h => h
  rw [ringKrullDim_quotient, ringKrullDim_quotient, Order.krullDim_eq_iSup_length,
    Order.krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add,
    ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]
  intro l
  have hq : q < f l.head := by
    show Q < (l.head.1.asIdeal)
    exact lt_of_lt_of_le hlt ((PrimeSpectrum.mem_zeroLocus _ _).mp l.head.2)
  refine le_trans ?_ (le_iSup _ ((l.map f hf).cons q hq))
  have hlen : ((l.map f hf).cons q hq).length = l.length + 1 := by
    simp [RelSeries.cons_length, LTSeries.map]
  rw [hlen]
  simp

end GroundTheory.Heights₂.Heights.NumbersDVR
