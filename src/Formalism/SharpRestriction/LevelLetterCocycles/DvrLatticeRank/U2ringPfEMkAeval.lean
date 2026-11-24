module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.EigenRingInvariants
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.BlockProductRing
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Algebra.CharP.Lemmas

@[expose] public section

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

section U2E

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

local notation "mkI" y => Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y)

theorem u2ringPfE_mem_max (p : ℕ) [hp : Fact p.Prime] (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O)
    {x : O} (hroot : (1 + x) ^ p = 1) : x ∈ IsLocalRing.maximalIdeal O := by
  have : CharP (IsLocalRing.ResidueField O) p :=
    (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
      rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]; exact hpm)
  have h := congrArg (IsLocalRing.residue O) hroot
  rw [map_pow, map_add (f := _), map_one, add_pow_char, one_pow] at h
  have h2 : (IsLocalRing.residue O x) ^ p = 0 := by linear_combination h
  have h3 := (pow_eq_zero_iff hp.out.ne_zero).mp h2
  rwa [IsLocalRing.residue_eq_zero_iff] at h3

theorem u2ringPfE_val_unit {y c : O} (hy : y ∈ IsLocalRing.maximalIdeal O) {F : PowerSeries O}
    (hF : IsUnit (PowerSeries.constantCoeff F)) (hc : (mkI y) F = (mkI y) (PowerSeries.C c)) :
    IsUnit c := by
  obtain ⟨H, hH⟩ := DualFramesAlt.BlockProductRing.dvd_of_mk_eq hc
  have h0 := congrArg PowerSeries.constantCoeff hH
  simp only [map_sub, map_mul, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C, zero_sub] at h0
  by_contra hnu
  have hcm : c ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
  have hFm : PowerSeries.constantCoeff F ∈ IsLocalRing.maximalIdeal O := by
    have e0 : PowerSeries.constantCoeff F = c + -y * PowerSeries.constantCoeff H := by linear_combination h0
    rw [e0]
    exact Ideal.add_mem _ hcm (Ideal.mul_mem_right _ _ ((Ideal.neg_mem_iff _).2 hy))
  exact (mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hFm)) hF

theorem u2ringPfE_mk_aeval {x y : O} {P : PowerSeries O} (hP : (mkI x) P = (mkI x) (PowerSeries.C y))
    (E : Polynomial O) :
    (mkI x) (Polynomial.aeval P E) = (mkI x) (PowerSeries.C (E.eval y)) := by
  let q := Ideal.Quotient.mkₐ O (DualFramesAlt.eigenRingInvariants.Ia x)
  change q P = q (PowerSeries.C y) at hP
  change q (Polynomial.aeval P E) = q (PowerSeries.C (E.eval y))
  rw [← Polynomial.aeval_algHom_apply q, hP, Polynomial.aeval_algHom_apply q]
  exact congrArg q (Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval y E)

end U2E

end Formalism.MainNotions.N.Ln34
