module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivialIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialisationToStrictlyHenselian
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_specialisation_to_strictlyHenselian : ∀ (R S O : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing O]
    [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)] [Algebra R S] [Algebra R O]
    (Q y : Ideal R) [Q.IsPrime] [y.IsPrime], Q ≤ y →
    (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = y →
    (IsLocalRing.maximalIdeal O).comap (algebraMap R O) = Q →
    Module.Flat R S → GlobalTheory.LocAcyc.LocPiecesEtale R S → Nonempty (S →ₐ[R] O) := by
  first | exact @GlobalTheory.Specialise.specialisation_exists | exact GlobalTheory.Specialise.specialisation_exists | (intros; apply GlobalTheory.Specialise.specialisation_exists <;> assumption)
