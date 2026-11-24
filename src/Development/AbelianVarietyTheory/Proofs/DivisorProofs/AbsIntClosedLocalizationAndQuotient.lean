module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.GroupTheory.MonoidLocalization.Basic
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.OreLocalization.Ring
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.Integral

@[expose] public section

open IsLocalRing

namespace GlobalTheory

open Polynomial

theorem absIntClosed_localization_and_quotient : ∀ (T : Type) [CommRing T], (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∀ (M : Submonoid T), 0 ∉ M → (IsDomain (Localization M) ∧ ∀ f : Polynomial (Localization M), f.Monic → 0 < f.natDegree → ∃ x : (Localization M), f.eval x = 0)) ∧ (∀ (p : Ideal T), p.IsPrime → (IsDomain (T ⧸ p) ∧ ∀ f : Polynomial (T ⧸ p), f.Monic → 0 < f.natDegree → ∃ x : (T ⧸ p), f.eval x = 0)) := by
  intro T _ ⟨hdom, hroot⟩
  refine ⟨fun M hM => ?_, fun p hp => ?_⟩
  · have hle : M ≤ nonZeroDivisors T := le_nonZeroDivisors_of_noZeroDivisors hM
    haveI : IsDomain (Localization M) := IsLocalization.isDomain_localization hle
    refine ⟨inferInstance, fun f hf hdeg => ?_⟩
    have hl := IsLocalization.scaleRoots_commonDenom_mem_lifts M f
      (by rw [hf.leadingCoeff]; exact one_mem _)
    obtain ⟨g, hg, hgdeg, hgm⟩ :=
      lifts_and_natDegree_eq_and_monic hl ((monic_scaleRoots_iff _).2 hf)
    rw [natDegree_scaleRoots] at hgdeg
    obtain ⟨y, hy⟩ := hroot g hgm (hgdeg ▸ hdeg)
    set s : Localization M :=
      algebraMap T (Localization M) (IsLocalization.commonDenom M f.support f.coeff) with hs
    have hu : IsUnit s := IsLocalization.map_units _ _
    refine ⟨algebraMap T (Localization M) y * ↑hu.unit⁻¹, ?_⟩
    have key := scaleRoots_eval_mul f (algebraMap T (Localization M) y * ↑hu.unit⁻¹) s
    have hsr : s * (algebraMap T (Localization M) y * ↑hu.unit⁻¹) =
        algebraMap T (Localization M) y := by
      rw [mul_left_comm, IsUnit.mul_val_inv, mul_one]
    rw [hsr, ← hg, eval_map, eval₂_hom, hy, map_zero] at key
    exact ((hu.pow _).mul_right_eq_zero).1 key.symm
  · haveI := hp
    haveI : IsDomain (T ⧸ p) := Ideal.Quotient.isDomain p
    refine ⟨inferInstance, fun f hf hdeg => ?_⟩
    have hl : f ∈ lifts (Ideal.Quotient.mk p) :=
      (mem_lifts _).2 (map_surjective _ Ideal.Quotient.mk_surjective f)
    obtain ⟨g, hg, hgdeg, hgm⟩ := lifts_and_natDegree_eq_and_monic hl hf
    obtain ⟨y, hy⟩ := hroot g hgm (hgdeg ▸ hdeg)
    refine ⟨Ideal.Quotient.mk p y, ?_⟩
    rw [← hg, eval_map, eval₂_hom, hy, map_zero]

end GlobalTheory
