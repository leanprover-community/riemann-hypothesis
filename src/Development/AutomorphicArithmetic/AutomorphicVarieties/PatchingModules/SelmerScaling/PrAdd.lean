module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerSpannedByKappaLaurent
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.prAdd :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), (∀ a, algebraMap S.Bh S.U.AA (S.pr0 a) + (S.pr1 a : S.U.AA) = a) ∧ (∀ (b : S.Bh) (y : S.U.N), S.pr0 (algebraMap S.Bh S.U.AA b + y) = b ∧ S.pr1 (algebraMap S.Bh S.U.AA b + y) = y) ∧ (∀ a a', S.pr0 (a + a') = S.pr0 a + S.pr0 a' ∧ S.pr1 (a + a') = S.pr1 a + S.pr1 a') ∧ (∀ (b : S.Bh) a, S.pr0 (b • a) = b * S.pr0 a ∧ S.pr1 (b • a) = b • S.pr1 a) ∧ (∀ a a', S.pr0 (a * a') - S.pr0 a * S.pr0 a' ∈ ired S.U.N ∧ S.pr1 (a * a') = S.pr0 a • S.pr1 a' + S.pr0 a' • S.pr1 a) ∧ ired S.U.N ≤ maximalIdeal S.Bh ∧ S.J2 ≤ maximalIdeal S.Bh := by
  intro l _ S
  have h1 : ∀ a, algebraMap S.Bh S.U.AA (S.pr0 a) + (S.pr1 a : S.U.AA) = a := by
    intro a
    simp [Ctx.pr1]
  have h2 : ∀ (b : S.Bh) (y : S.U.N), S.pr0 (algebraMap S.Bh S.U.AA b + y) = b ∧
      S.pr1 (algebraMap S.Bh S.U.AA b + y) = y := by
    intro b y
    have e := h1 (algebraMap S.Bh S.U.AA b + y)
    have hm : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b + y) - b) ∈ S.U.N := by
      have : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b + y) - b) =
          (y : S.U.AA) - (S.pr1 (algebraMap S.Bh S.U.AA b + y) : S.U.AA) := by
        rw [map_sub]; linear_combination e
      rw [this]
      exact S.U.N.sub_mem y.2 (S.pr1 _).2
    have hz : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA b + y) - b) = 0 :=
      Submodule.disjoint_def.1 S.U.compl.disjoint _ (Submodule.mem_one.2 ⟨_, rfl⟩) hm
    have hb : S.pr0 (algebraMap S.Bh S.U.AA b + y) = b :=
      sub_eq_zero.1 (S.U.inj (by rw [hz, map_zero]))
    refine ⟨hb, Subtype.ext ?_⟩
    rw [hb] at e
    exact add_left_cancel e
  have key : ∀ (a : S.U.AA) (b : S.Bh) (y : S.U.N), a = algebraMap S.Bh S.U.AA b + y →
      S.pr0 a = b ∧ S.pr1 a = y := by
    rintro a b y rfl
    exact h2 b y
  have hi : ired S.U.N ≤ maximalIdeal S.Bh := by
    refine Ideal.span_le.2 ?_
    rintro b ⟨x, hx, y, hy, e⟩
    obtain ⟨c, hc, e'⟩ := S.U.mul_mem x hx y hy
    have : b = c := S.U.inj (e.symm.trans e')
    rw [this]; exact hc
  refine ⟨h1, h2, fun a a' => key _ _ _ ?_, fun b a => key _ _ _ ?_, fun a a' => ?_, hi, ?_⟩
  · rw [map_add (f := _), Submodule.coe_add]
    linear_combination - h1 a - h1 a'
  · rw [map_mul, Submodule.coe_smul, Algebra.smul_def, Algebra.smul_def, ← mul_add, h1]
  · obtain ⟨c, -, e⟩ := S.U.mul_mem _ (S.pr1 a).2 _ (S.pr1 a').2
    have := key (a * a') (S.pr0 a * S.pr0 a' + c) (S.pr0 a • S.pr1 a' + S.pr0 a' • S.pr1 a) (by
      rw [map_add (f := _), map_mul, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, Algebra.smul_def,
        Algebra.smul_def, ← e]
      have e1 := h1 a
      have e2 := h1 a'
      linear_combination (- a') * e1 - (algebraMap S.Bh S.U.AA (S.pr0 a) + (S.pr1 a : S.U.AA)) * e2)
    refine ⟨?_, this.2⟩
    rw [this.1, add_sub_cancel_left]
    exact Ideal.subset_span ⟨_, (S.pr1 a).2, _, (S.pr1 a').2, e⟩
  · refine sup_le (sup_le ?_ (Ideal.pow_le_self two_ne_zero)) hi
    exact ((IsLocalRing.local_hom_tfae (algebraMap S.OO S.Bh)).out 1 3).1 (IsCO.isLocalHom (O := S.OO) (R := S.Bh))
