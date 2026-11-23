module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.OfMap
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

theorem UpperTheory.V.Ws.Pp.nilPoly :
    ∀ {B S : Type} [CommRing B] [IsLocalRing B] [CommRing S] [IsLocalRing S] [Algebra B S] [Module.Finite B S] (v : S), v ∈ maximalIdeal S → ∃ p : B[X], Dist (maximalIdeal B) p ∧ aeval v p = 0 := by
  intro B S _ _ _ _ _ _ v hv
  have hrad : v ∈ ((maximalIdeal B).map (algebraMap B S)).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    intro J hJ'
    obtain ⟨hJ, hJp⟩ := hJ'
    have hle : maximalIdeal B ≤ Ideal.comap (algebraMap B S) J := by
      intro b hb
      exact hJ (Ideal.mem_map_of_mem _ hb)
    have hc : Ideal.comap (algebraMap B S) J = maximalIdeal B :=
      ((IsLocalRing.maximalIdeal.isMaximal B).eq_of_le (Ideal.comap_ne_top _ hJp.ne_top) hle).symm
    have hcm : (Ideal.comap (algebraMap B S) J).IsMaximal := by
      rw [hc]
      exact IsLocalRing.maximalIdeal.isMaximal B
    have hJm : J.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := B) J hcm
    rw [IsLocalRing.eq_maximalIdeal hJm]
    exact hv
  obtain ⟨n, hn⟩ := hrad
  have hN : v ^ (n + 1) ∈ (maximalIdeal B).map (algebraMap B S) := by
    rw [pow_succ]
    exact Ideal.mul_mem_right _ _ hn
  have hrange : LinearMap.range (Algebra.lmul B S (v ^ (n + 1))) ≤
      (maximalIdeal B) • (⊤ : Submodule B S) := by
    rintro _ ⟨s, rfl⟩
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    simpa using Ideal.mul_mem_right s _ hN
  obtain ⟨p, hpm, -, hpc, hpa⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
      (R := B) (M := S) (Algebra.lmul B S (v ^ (n + 1))) (maximalIdeal B) hrange
  refine ⟨expand B (n + 1) p, ⟨hpm.expand (Nat.succ_pos n), ?_⟩, ?_⟩
  · intro k hk
    rw [natDegree_expand] at hk
    rw [coeff_expand (Nat.succ_pos n)]
    split_ifs with hd
    · have hlt : k / (n + 1) < p.natDegree := by
        rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos n)]
        exact hk
      exact Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hlt) (hpc _)
    · exact zero_mem _
  · rw [expand_aeval]
    rw [Polynomial.aeval_algHom_apply] at hpa
    have h1 := LinearMap.congr_fun hpa 1
    simpa using h1
