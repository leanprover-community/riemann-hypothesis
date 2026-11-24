module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.perturb :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : Y → E →L[ℝ] ℝ}, LocFin q → ∀ h ∈ poly q, ∀ k : E, (∀ y, q y h = 1 → q y k = 0) → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s| ≤ ε → h + s • k ∈ poly q := by
  intro E Y _ _ q hq h hh k hk
  have hh' : ∀ y, 1 ≤ q y h := hh
  obtain ⟨S, hS, hU⟩ := hq h hh
  have hc : Continuous fun s : ℝ => h + s • k :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hT : Filter.Tendsto (fun s : ℝ => h + s • k) (nhds 0) (nhds h) := by
    have := hc.tendsto 0
    simpa using this
  have A : ∀ᶠ s in nhds (0:ℝ), ∀ y ∉ S, 1 < q y (h + s • k) := hT.eventually hU
  have B : ∀ᶠ s in nhds (0:ℝ), ∀ y ∈ S, 1 ≤ q y (h + s • k) := by
    refine (Filter.eventually_all_finite hS).2 fun y _ => ?_
    by_cases hy : q y h = 1
    · refine Filter.Eventually.of_forall fun s => ?_
      simp [hy, hk y hy]
    · have hlt : 1 < q y h := lt_of_le_of_ne (hh' y) (Ne.symm hy)
      have hcy : Continuous fun s : ℝ => q y (h + s • k) := (q y).continuous.comp hc
      have ht := hcy.tendsto 0
      simp only [zero_smul, add_zero] at ht
      exact (ht.eventually (lt_mem_nhds hlt)).mono fun s hs => hs.le
  obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.1 (A.and B)
  refine ⟨δ / 2, half_pos hδ, fun s hs => ?_⟩
  have hd : dist s 0 < δ := by
    rw [Real.dist_eq, sub_zero]
    linarith
  obtain ⟨h1, h2⟩ := hP hd
  show ∀ y, 1 ≤ q y (h + s • k)
  intro y
  by_cases hyS : y ∈ S
  · exact h2 y hyS
  · exact (h1 y hyS).le
