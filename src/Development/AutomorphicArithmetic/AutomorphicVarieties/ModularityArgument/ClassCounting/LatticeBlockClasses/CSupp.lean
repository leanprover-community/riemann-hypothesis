module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cSupp :
    UpperTheory.V.ZK.Cl.CSupp := by
  intro L F _ _ _ _ _ 𝔡 b₀ hb₀
  refine ⟨b₀ * ∏ P ∈ 𝔡.support, ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L), ?_, dvd_mul_right _ _, ?_⟩
  · refine mul_ne_zero hb₀ (Finset.prod_ne_zero_iff.mpr fun P _ => ?_)
    have h : Ideal.absNorm P.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
    exact_mod_cast h
  · intro P hP
    rw [map_mul, map_prod]
    apply Ideal.mul_mem_left
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem
      (fun Q : HeightOneSpectrum (𝓞 F) =>
        algebraMap (𝓞 L) (𝓞 F) ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 L))
      (Finsupp.mem_support_iff.mpr hP)
    rw [hc]
    apply Ideal.mul_mem_right
    rw [map_natCast]
    exact Ideal.absNorm_mem P.asIdeal
