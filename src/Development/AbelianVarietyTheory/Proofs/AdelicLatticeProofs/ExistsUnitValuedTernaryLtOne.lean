module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNonzeroIsotropic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad

namespace TernaryResidue


open MvPolynomial in
theorem exists_ne_zero_sum_eq_zero {k : Type*} [Field k] [Finite k] (a : Fin 3 → Fin 3 → k) :
    ∃ x : Fin 3 → k, x ≠ 0 ∧ ∑ i, ∑ j, a i j * x i * x j = 0 := by
  first
  | exact @_root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic
  | exact _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic
  | (apply _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroIsotropic.exists_nonzero_isotropic ..)

end TernaryResidue

theorem exists_unit_valued_ternary_lt_one (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (c : Fin 3 → Fin 3 → v.adicCompletion F)
    (hc : ∀ i j, Valued.v (c i j) ≤ 1) :
    ∃ x : Fin 3 → v.adicCompletion F, (∀ i, Valued.v (x i) ≤ 1) ∧ (∃ i, Valued.v (x i) = 1) ∧
      Valued.v (∑ i, ∑ j, c i j * x i * x j) < 1 := by
  classical
  choose r hr using fun i j => GlobalTheory.Idele.exists_valued_sub_le v (hc i j) 1
  let ι : 𝓞 F →+* v.adicCompletion F :=
    (algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)
  have hι : ∀ y : 𝓞 F, Valued.v (ι y) = v.valuation F (algebraMap (𝓞 F) F y) := fun y =>
    GlobalTheory.Idele.valued_algebraMap v _
  have hle : ∀ y : 𝓞 F, Valued.v (ι y) ≤ 1 := fun y => by
    rw [hι]; exact v.valuation_le_one y
  have hlt : ∀ y : 𝓞 F, Valued.v (ι y) < 1 ↔ y ∈ v.asIdeal := fun y => by
    rw [hι]; exact v.valuation_lt_one_iff_mem y
  have hr' : ∀ i j, Valued.v (c i j - ι (r i j)) < 1 := fun i j => by
    refine (hr i j).trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  obtain ⟨x, hx0, hx⟩ := TernaryResidue.exists_ne_zero_sum_eq_zero
    (k := 𝓞 F ⧸ v.asIdeal) fun i j => Ideal.Quotient.mk v.asIdeal (r i j)
  choose y hy using fun i => Ideal.Quotient.mk_surjective (x i)
  refine ⟨fun i => ι (y i), fun i => hle _, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx0
    refine ⟨i, le_antisymm (hle _) (not_lt.1 fun h => hi ?_)⟩
    rw [← hy i]
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hlt _).1 h)
  · have hmem : (∑ i, ∑ j, r i j * y i * y j) ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hx]

      simp only [map_sum, map_mul, hy]
    have hsplit : ∑ i, ∑ j, c i j * ι (y i) * ι (y j) =
        ι (∑ i, ∑ j, r i j * y i * y j) +
          ∑ i, ∑ j, (c i j - ι (r i j)) * ι (y i) * ι (y j) := by

      simp only [map_sum, map_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ((hlt _).2 hmem) ?_
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => Valuation.map_sum_lt _ one_ne_zero
      fun j _ => ?_
    rw [map_mul, map_mul]
    exact (mul_le_of_le_one_right' (hle _)).trans_lt
      ((mul_le_of_le_one_right' (hle _)).trans_lt (hr' i j))

end GlobalTheory.LocalQuad
