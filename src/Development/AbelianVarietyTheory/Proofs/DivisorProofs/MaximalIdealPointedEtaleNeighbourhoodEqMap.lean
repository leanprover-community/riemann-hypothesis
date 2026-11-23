module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Unramified.LocalRing

@[expose] public section

open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation.EtNbhd

instance isLocalHom_algebraMap_B {R : Type} [CommRing R] [IsLocalRing R] (i : EtNbhd R) :
    IsLocalHom (algebraMap R i.B) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hm : a ∈ maximalIdeal R := hna
  have hq : algebraMap R i.A a ∈ i.q := by
    show i.pt (algebraMap R i.A a) = 0
    rw [AlgHom.commutes]
    exact (residue_eq_zero_iff a).2 hm
  have : algebraMap R i.B a ∈ maximalIdeal i.B := by
    rw [IsScalarTower.algebraMap_apply R i.A i.B]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff i.B i.q _).2 hq
  exact this ha

theorem maximalIdeal_B_eq_map (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) :
    maximalIdeal i.B = (maximalIdeal R).map (algebraMap R i.B) :=
  Algebra.FormallyUnramified.map_maximalIdeal.symm

end GlobalTheory.Henselisation.EtNbhd
