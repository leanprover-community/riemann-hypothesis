module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerBasisOfCharpolySeparable
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

@[expose] public section

namespace GlobalTheory.UnitLemma

open Polynomial

theorem InvAlg.isReduced_of_separable_P : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsReduced B.A := by
  intro K B h
  obtain ⟨e, he⟩ := exists_basis_pow_of_separable K B h
  have h2 : minpoly K.E (LinearMap.mulLeft K.E B.g) = minpoly K.E B.g :=
    minpoly.algHom_eq (Algebra.lmul K.E B.A) (Algebra.lmul_injective) B.g
  have hms : (minpoly K.E B.g).Separable :=
    h.of_dvd (h2 ▸ LinearMap.minpoly_dvd_charpoly (LinearMap.mulLeft K.E B.g))
  have hsurj : ∀ a : B.A, ∃ q : K.E[X], aeval B.g q = a := by
    intro a
    have hle : Submodule.span K.E (Set.range e) ≤
        Subalgebra.toSubmodule (Algebra.adjoin K.E ({B.g} : Set B.A)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [he]
      exact Subalgebra.pow_mem (Algebra.adjoin K.E ({B.g} : Set B.A))
        (Algebra.subset_adjoin (Set.mem_singleton B.g)) _
    have ha : a ∈ Algebra.adjoin K.E ({B.g} : Set B.A) := hle (e.span_eq ▸ Submodule.mem_top)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨q, hq⟩ := ha
    exact ⟨q, hq⟩
  refine ⟨fun n hn => ?_⟩
  obtain ⟨k, hk⟩ := hn
  obtain ⟨q, rfl⟩ := hsurj n
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0
    rw [pow_zero] at hk
    haveI := subsingleton_of_zero_eq_one hk.symm
    exact Subsingleton.elim _ _
  have hdk : minpoly K.E B.g ∣ q ^ k := minpoly.dvd _ _ (by rw [map_pow, hk])
  obtain ⟨r, hr⟩ := (hms.squarefree.dvd_pow_iff_dvd h0.ne').1 hdk
  rw [hr, map_mul, minpoly.aeval, zero_mul]

end GlobalTheory.UnitLemma
