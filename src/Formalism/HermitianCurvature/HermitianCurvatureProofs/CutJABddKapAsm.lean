module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddGen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jABddKapQQ_of_kapRealiser (hR : KapRealiser) : JABddKapQQ := by
  obtain ⟨K, hK, hR⟩ := hR
  refine ⟨K, hK, ?_⟩
  intro Cc Cb hCc hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b hb
  obtain ⟨κ, rfl⟩ := hb
  obtain ⟨c, ca, hadj, hc, hca, he, hea, hbc, hbca, hbig⟩ :=
    hR Cc Cb hCc hCb E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ κ
  refine ⟨SSn.orderZeroDifferentialOperator S v c ca hadj, SSn.order_zero_operator_order, ⟨?_, ?_⟩, ?_, fun J hJ => ⟨?_, ?_, ?_⟩⟩
  · intro Tm hTm
    simp only [SSn.orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    exact ⟨hc, hca⟩
  · intro p hp f' _ g hg
    rw [SSn.order_zero_operator_apply, SSn.order_zero_operator_apply]
    exact he p hp g hg.1 _
  · intro Tm hTm ε hε m
    simp only [SSn.orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    obtain ⟨C1, h1⟩ := hbc ε hε m
    obtain ⟨C2, h2⟩ := hbca ε hε m
    refine ⟨max C1 C2, fun u w hu hw hl g hg hG => ⟨?_, ?_⟩⟩
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h1 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h2 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)
  · rw [SSn.order_zero_operator_apply]; exact SSn.equivariant_coefficient_preserves_forms hc he hJ
  · rw [SSn.order_zero_operator_adjoint]; exact SSn.equivariant_coefficient_preserves_forms hca hea hJ
  · rw [SSn.order_zero_operator_apply]
    exact trJ_kap_of_bigCell S T v e κ c hbig J

theorem jABddKapQQ_of_typeProj (hB : DatumBd) (hG : SSn.SSnGeom) (hP : TypeProj) : JABddKapQQ :=
  jABddKapQQ_of_kapRealiser (kapRealiser_of_typeProj hB hG hP)

end

end Formalism.FourierDecayAlt.P.CutMP.JA
