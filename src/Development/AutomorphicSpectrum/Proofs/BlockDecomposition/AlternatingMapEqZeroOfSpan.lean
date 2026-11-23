module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.Tactic.Continuity
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KSumApply

@[expose] public section

open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.AltSpan

theorem alternatingMap_eq_zero_of_span :
    ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℝ M]
      {β : Type} (b : β → P), Submodule.span ℝ (Set.range b) = ⊤ →
      ∀ {m : ℕ} (f : P [⋀^Fin m]→ₗ[ℝ] M), (∀ I : Fin m → β, f (b ∘ I) = 0) → f = 0 := by
  intro P _ _ M _ _ β b hb m f hf
  classical
  have key : ∀ (S : Finset (Fin m)) (v : Fin m → P), (∀ i ∉ S, v i ∈ Set.range b) → f v = 0 := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro v hv
      choose I hI using fun i => hv i (by simp)
      have hvI : v = b ∘ I := funext fun i => (hI i).symm
      rw [hvI]
      exact hf I
    · intro j S _ ih v hv
      have hlin : f.toMultilinearMap.toLinearMap v j = 0 := by
        apply LinearMap.ext_on_range hb
        intro c
        simp only [MultilinearMap.toLinearMap_apply, LinearMap.zero_apply, AlternatingMap.coe_multilinearMap]
        apply ih
        intro i hi
        by_cases hij : i = j
        · rw [hij]
          simp
        · rw [Function.update_of_ne hij]
          exact hv i (by simp [hij, hi])
      have h1 := LinearMap.congr_fun hlin (v j)
      simpa [MultilinearMap.toLinearMap_apply] using h1
  ext v
  simpa using key Finset.univ v (by simp)

end GlobalTheory.CompanionTheory.AltSpan
