module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.LocSmall
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
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace PI.StrongApproxE

open Formalism.MainNotions.S.Loc

theorem existsLatticeAutomorphismApprox : LocLin := by
  intro F E _ _ _ _ _ sig p L a e
  rw [Algebra.smul_def, map_mul, L.compat, Algebra.smul_def]

theorem local_span_holds : LocSpan := by
  intro F E _ _ _ _ _ sig p L n b hb x
  have hsub : Set.range L.ιE ⊆ Submodule.span L.Fp (Set.range (fun i => L.ιE (b i))) := by
    rintro _ ⟨e, rfl⟩
    obtain ⟨c, rfl⟩ := hb e

    rw [map_sum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [existsLatticeAutomorphismApprox F E sig p L]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have htop : Submodule.span L.Fp (Set.range (fun i => L.ιE (b i))) = ⊤ := by
    rw [eq_top_iff, ← L.span]
    exact Submodule.span_le.mpr hsub
  have hx : x ∈ Submodule.span L.Fp (Set.range (fun i => L.ιE (b i))) := htop ▸ Submodule.mem_top
  obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun L.Fp).mp hx
  exact ⟨α, hα.symm⟩

theorem intSpan' : IntSpan := by
  intro F E _ _ _ _ _
  classical
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let B := Module.finBasis F E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image (fun i => B i))
  refine ⟨Module.finrank F E, fun i => y • B i,
    fun i => hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)), fun e => ?_⟩
  refine ⟨fun i => B.repr e i / (y : F), ?_⟩
  conv_lhs => rw [← B.sum_repr e]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hyF : (y : F) ≠ 0 := Int.cast_ne_zero.mpr hy0
  rw [smul_comm, ← smul_assoc, zsmul_eq_mul, mul_div_cancel₀ _ hyF]

end PI.StrongApproxE
