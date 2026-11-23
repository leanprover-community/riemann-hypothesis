module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem iwOps_red_un {l : ℕ} [Fact l.Prime] (b : ℕ) (hb : ¬ l ∣ b) (r : ℕ) :
    red l r (un b hb (r + 1)) = un b hb r := by
  ext
  simp only [un, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, ZMod.coe_unitOfCoprime, map_natCast]

private theorem iwOps_tr {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {A : ValuationSubring Ω} {Z : Sy Ω l} (h : IwI c A Z) (b : ℕ) (hb : ¬ l ∣ b) : IwI c A (tr b hb Z) := by
  refine ⟨fun r s hs x => h.int r s hs _, fun r s hs t ht x => ?_, fun r s hs x => ?_⟩
  · simp only [UpperTheory.Kd.C7.tr]
    rw [h.coc r s hs t ht, mul_right_comm]
  · simp only [UpperTheory.Kd.C7.tr]
    rw [h.nrm r s hs]
    symm
    refine Finset.sum_equiv (Equiv.mulRight (un b hb (r + 1))) (fun y => ?_) (fun y _ => rfl)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulRight]
    rw [map_mul, iwOps_red_un, mul_left_inj]

theorem UpperTheory.Kd.C7.pIwOps :
    UpperTheory.Kd.C7.SIwOps := by
  intro l _ _ Ω _ _ _ A _ c Z h b hb
  have h' := iwOps_tr h b hb
  refine ⟨h', fun r s hs x => ?_, fun r s hs t ht x => ?_, fun r s hs x => ?_⟩
  · exact c.O.sub_mem (h.int r s hs x) (c.O.mul_mem (natCast_mem c.O b) (h'.int r s hs x))
  · simp only [sharp]
    rw [h.coc r s hs t ht, h'.coc r s hs t ht]
    ring
  · simp only [sharp]
    rw [h.nrm r s hs, h'.nrm r s hs, Finset.sum_sub_distrib, Finset.mul_sum]
