module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host
open GlobalTheory.PRep (fixed)

namespace UpperTheory.V.Cj.S

theorem hkSum : HkSum := by
  intro E _ _ w n V _ _ ρ ϖ hϖ hu _ j hj x hx
  classical
  have hr := satake_range_eq (n := n) w hϖ hu Final.TjCosets hj
  unfold heckeVec
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun i : SatakeIdx w hϖ (n := n) j =>
      ((satakeB w hϖ hu i : GL (Fin n) (w.adicCompletion E)) :
        GL (Fin n) (w.adicCompletion E) ⧸ KGL w (n := n)))) ?_]
  · rw [Finset.sum_image (fun i _ i' _ h => satakeB_inj w hϖ hu h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KGL w (n := n)) (satakeB w hϖ hu i)
    have hfix : ρ (k : GL (Fin n) (w.adicCompletion E)) x = x := GlobalTheory.LGrp.mem_fixed.1 hx _ k.2
    rw [hk, satake_Tj_eq, Set.indicator_of_mem (satake_Tset_right w (satakeB_mem w hϖ hu i) k.2),
      Pi.one_apply, one_smul, map_mul, Module.End.mul_apply, hfix]
  · intro y hy
    have hT : Tj ℂ n (Ov E w) ϖ j y.out ≠ 0 := fun h0 => hy (by simp only [h0, zero_smul])
    have hy' : y ∈ Set.range _ := hr.ge ((satake_Tj_ne_zero_iff w ℂ ϖ j _).1 hT)
    obtain ⟨i, rfl⟩ := hy'
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ i))

end UpperTheory.V.Cj.S
