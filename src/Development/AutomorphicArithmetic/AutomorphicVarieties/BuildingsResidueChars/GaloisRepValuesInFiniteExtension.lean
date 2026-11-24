module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

theorem UpperTheory.galois_rep_values_in_finite_extension :
    UpperTheory.V.Af.Wd.FinVal := by
  intro F Ω C _ _ _ _ M hM χ hχ
  classical
  have hpos : 0 < M := by omega
  have hR : {ζ : Ω | ζ ^ M = 1}.Finite := by
    refine (Multiset.toFinset (Polynomial.nthRoots M (1 : Ω))).finite_toSet.subset ?_
    intro ζ hζ
    simpa [Polynomial.mem_nthRoots hpos] using hζ
  haveI : Finite {ζ : Ω | ζ ^ M = 1} := hR.to_subtype
  let π : (Ω ≃ₐ[F] Ω) → ({ζ : Ω | ζ ^ M = 1} → {ζ : Ω | ζ ^ M = 1}) := fun s ζ =>
    ⟨s ζ, by
      show (s ζ) ^ M = 1
      rw [← map_pow, show (ζ : Ω) ^ M = 1 from ζ.2, map_one]⟩
  have hfac : ∀ s t, π s = π t → χ s = χ t := by
    intro s t hst
    have h1 : χ (t⁻¹ * s) = 1 := by
      refine hχ _ (fun ζ hζ => ?_)
      have h := congrArg (fun f => (f ⟨ζ, hζ⟩ : Ω)) hst
      simp only [π] at h
      rw [AlgEquiv.mul_apply, h, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  refine (Set.finite_range (fun x : Set.range π => χ x.2.choose)).subset ?_
  rintro _ ⟨s, rfl⟩
  exact ⟨⟨π s, s, rfl⟩, hfac _ _ (⟨s, rfl⟩ : π s ∈ Set.range π).choose_spec⟩
