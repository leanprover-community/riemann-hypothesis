module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.EmbedQZ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.QzEnd
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.dualGen :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [AddCommGroup D] [Module ℤ_[l] D] (r : ℕ), (∀ x : D, ∃ k : ℕ, (l : ℤ_[l]) ^ k • x = 0) → CardLe (Submodule.torsionBy ℤ_[l] D (l : ℤ_[l])) (l ^ r) →
      Tower.GenLE ℤ_[l] (D →ₗ[ℤ_[l]] QZ l) r := by
  intro l _ D _ _ r htors hcard
  classical
  obtain ⟨f, hf⟩ := embedQZ l D r htors hcard
  haveI := PropA.qzInj l
  refine ⟨Fintype.linearCombination ℤ_[l] (fun i => (LinearMap.proj i).comp f), ?_⟩
  intro φ
  obtain ⟨ψ, hψ⟩ := Module.Injective.out (R := ℤ_[l]) (Q := QZ l) f hf φ
  choose c hc using fun i => qzEnd l (ψ.comp (LinearMap.single ℤ_[l] (fun _ : Fin r => QZ l) i))
  refine ⟨c, ?_⟩
  ext d
  rw [Fintype.linearCombination_apply, ← hψ d]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  conv_rhs => rw [← Finset.univ_sum_single (f d)]

  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 := hc i (f d i)
  simp only [LinearMap.comp_apply, LinearMap.single_apply] at h1
  exact h1.symm
