module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

theorem UpperTheory.V.Lit.Geo.Cs.compSz :
    CompSz := by
  intro V W F _ _ _ _ _ _ k c
  have hD1 : (1 : ℝ) ≤ max 1 c := le_max_left _ _
  have hD0 : (0 : ℝ) ≤ max 1 c := zero_le_one.trans hD1
  refine ⟨(k.factorial : ℝ) * (max 1 c) ^ k, by positivity, ?_⟩
  intro g f x b hf hg hc hb i hi
  have hb0 : 0 ≤ b := hb.nonneg
  have hk : ((k : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hne : ((k : ℕ) : WithTop ℕ∞) ≠ ∞ := by exact_mod_cast ENat.coe_ne_top k
  have hf' := (hf.of_le hk).eventually hne
  have hg' := (hg.of_le hk).eventually hne
  obtain ⟨t, ht, hto, hxt⟩ := eventually_nhds_iff.1 hg'
  have hpre : ∀ᶠ y in 𝓝 x, f y ∈ t := hf.continuousAt.preimage_mem_nhds (hto.mem_nhds hxt)
  obtain ⟨s, hs, hso, hxs⟩ := eventually_nhds_iff.1 (hf'.and hpre)
  have hgt : ContDiffOn ℝ k g t := fun y hy => (ht y hy).contDiffWithinAt
  have hfs : ContDiffOn ℝ k f s := fun y hy => (hs y hy).1.contDiffWithinAt
  have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := i) (C := b) (D := max 1 c) hgt hfs
    (by exact_mod_cast hi) hto.uniqueDiffOn hso.uniqueDiffOn (fun y hy => (hs y hy).2) hxs
    (fun j hj => by
      rw [iteratedFDerivWithin_of_isOpen j hto hxt]
      exact hb j (hj.trans hi))
    (fun j hj1 hj => by
      rw [iteratedFDerivWithin_of_isOpen j hso hxs]
      exact ((hc j hj1 (hj.trans hi)).trans (le_max_right 1 c)).trans
        (le_self_pow₀ hD1 (by omega)))
  rw [iteratedFDerivWithin_of_isOpen i hso hxs] at key
  refine key.trans ?_
  have h1 : (i.factorial : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hi
  have h2 : (max 1 c) ^ i ≤ (max 1 c) ^ k := pow_le_pow_right₀ hD1 hi
  calc (i.factorial : ℝ) * b * (max 1 c) ^ i = ((i.factorial : ℝ) * (max 1 c) ^ i) * b := by ring
    _ ≤ _ := by gcongr
