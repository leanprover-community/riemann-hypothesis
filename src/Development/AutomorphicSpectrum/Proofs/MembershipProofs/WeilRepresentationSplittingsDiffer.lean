module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import GroundTheory.GlobalFields.Adele.Compact
public import GroundTheory.GlobalFields.Adele.IntegersLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import GroundTheory.GlobalFields.Adele.Approximation
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.SplitRatio

variable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]


open GroundTheory.Global in
theorem exists_schA_compact : ∃ Φ ∈ schA F κ, Continuous Φ ∧ HasCompactSupport Φ ∧ Φ 0 ≠ 0 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := default
  have hb : HasCompactSupport fun v => (b v : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hb' : ContDiff ℝ (⊤ : ℕ∞) fun v => (b v : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  let f : 𝓢(κ → mixedEmbedding.mixedSpace F, ℂ) := hb.toSchwartzMap hb'
  have hf : ∀ v, f v = (b v : ℂ) := fun _ => rfl
  set O := Set.univ.pi fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) with hO
  set g := O.indicator fun _ => (1 : ℂ) with hgd
  have hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    have hc : IsCompact O := isCompact_univ_pi fun _ => GroundTheory.Global.isCompact_integralFiniteAdeles F
    have ho : IsOpen O := isOpen_set_pi Set.finite_univ fun _ _ => GroundTheory.Global.isOpen_integralFiniteAdeles
    have hcl : IsClosed O := isClosed_set_pi fun _ _ =>
      AddSubgroup.isClosed_of_isOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).toAddSubgroup GroundTheory.Global.isOpen_integralFiniteAdeles
    refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ O
    · exact ⟨_, ho, hx, fun y hy => by rw [hgd, Set.indicator_of_mem hx, Set.indicator_of_mem hy]⟩
    · exact ⟨_, hcl.isOpen_compl, hx, fun y hy => by rw [hgd, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]⟩
  refine ⟨pureA F f g, Submodule.subset_span ⟨f, _, hg, rfl⟩, ?_, ?_, ?_⟩
  · refine (f.continuous.comp (continuous_pi fun i => ?_)).mul (hg.1.continuous.comp (continuous_pi fun i => ?_))
    · exact (GroundTheory.Global.homeomorphMixedSpace F).continuous.comp (continuous_fst.comp (continuous_apply i))
    · exact continuous_snd.comp (continuous_apply i)
  · let m : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F) :=
      fun p i => ((GroundTheory.Global.homeomorphMixedSpace F).symm (p.1 i), p.2 i)
    have hm : Continuous m := continuous_pi fun i =>
      ((GroundTheory.Global.homeomorphMixedSpace F).symm.continuous.comp ((continuous_apply i).comp continuous_fst)).prodMk
        ((continuous_apply i).comp continuous_snd)
    refine HasCompactSupport.intro ((hb.isCompact.prod hg.2.isCompact).image hm) fun x hx => ?_
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
    refine hx ⟨(_, _), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, funext fun i => ?_⟩
    exact Prod.ext ((GroundTheory.Global.homeomorphMixedSpace F).symm_apply_apply (x i).1) rfl
  · have h0 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) ∈ O := fun i _ => Subring.zero_mem _
    have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 :=
      funext fun i => map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    rw [pureA, h1, hf, hgd, Set.indicator_of_mem h0,
      b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    simp

end GlobalTheory.CompanionTheory.SplitRatio
