module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.FrobStep
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

theorem delta_mem (l : ℕ) [Fact l.Prime] (dK : ℕ) (hd : dK.Prime) (hd4 : dK % 4 = 3) (hld : ¬ l ∣ dK)
    (ι : ℂ ≃+* ℂ_[l]) : ι (sq dK) ∈ MaximalUnramifiedExtension l := by
  haveI : Fact dK.Prime := ⟨hd⟩
  have hd2 : ringChar (ZMod dK) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hζ : IsPrimitiveRoot (ι (Complex.exp (2 * ↑Real.pi * Complex.I / ↑dK))) dK :=
    (Complex.isPrimitiveRoot_exp dK hd.ne_zero).map_of_injective ι.injective
  set χ := (quadraticChar (ZMod dK)).ringHomComp (Int.castRingHom ℂ_[l]) with hχ
  set ψ := AddChar.zmodChar dK hζ.pow_eq_one with hψdef
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root dK hζ
  have hχ1 : χ ≠ 1 := by
    obtain ⟨a, ha⟩ := MulChar.ne_one_iff.1 (quadraticChar_ne_one hd2)
    refine MulChar.ne_one_iff.2 ⟨a, fun h => ha ?_⟩
    rw [hχ, MulChar.ringHomComp_apply, eq_intCast] at h
    exact_mod_cast h
  have hG : gaussSum χ ψ ^ 2 = -(dK : ℂ_[l]) := by
    rw [gaussSum_sq hχ1 ((quadraticChar_isQuadratic (ZMod dK)).comp _) hψ, ZMod.card, hχ,
      MulChar.ringHomComp_apply, quadraticChar_neg_one hd2, ZMod.card, ZMod.χ₄_nat_three_mod_four hd4]
    simp
  have hx : ι (sq dK) ^ 2 = -(dK : ℂ_[l]) := by
    rw [← map_pow]
    have h2 : sq dK ^ 2 = -(dK : ℂ) := by
      unfold sq
      rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      push_cast
      ring
    rw [h2, map_neg, map_natCast]
  have hmem : gaussSum χ ψ ∈ MaximalUnramifiedExtension l := by
    unfold gaussSum
    refine Subfield.sum_mem _ (fun a _ => Subfield.mul_mem _ ?_ ?_)
    · rw [hχ, MulChar.ringHomComp_apply, eq_intCast]
      exact intCast_mem _ _
    · rw [hψdef, AddChar.zmodChar_apply]
      unfold MaximalUnramifiedExtension
      apply Subfield.le_topologicalClosure
      apply Subfield.subset_closure
      refine ⟨dK, hd.pos, hld, ?_⟩
      rw [← pow_mul, mul_comm a.val dK, pow_mul, hζ.pow_eq_one, one_pow]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx.trans hG.symm) with h | h
  · rw [h]
    exact hmem
  · rw [h]
    exact Subfield.neg_mem _ hmem

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
