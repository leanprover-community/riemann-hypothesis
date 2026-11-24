module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsModelFibreFinite
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

theorem ModelFibreFinite.proof : ModelFibreFinite.Statement := by
  intro K _ ι _ P e M Ψ hP hΨ y
  classical
  obtain ⟨k0⟩ := hP.1
  have hH : IsMultiHomogIdeal P := hP.2.1.2.1
  let f : M.Xc → (((k : K) → ι k) → ℂ) := fun x =>
    (Ψ (segre (modelLift M x x)) 0)⁻¹ • segre (modelLift M x x)
  refine Set.Finite.of_finite_image (f := f) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_) ?_
  · rintro _ ⟨x, ⟨hxy, hx0⟩, rfl⟩
    have hq : modelQ M Ψ x = y := hxy
    have hl := (modelLift_spec M x).1 x (mem_modelU M x)
    have hlam : Ψ (segre (modelLift M x x)) 0 ≠ 0 := fun h => hx0 (Or.inl h)
    refine ⟨fun p => Function.update (1 : K → ℂ) k0 (Ψ (segre (modelLift M x x)) 0)⁻¹ p.1 *
      modelLift M x x p, mcPts_smul hH _ ?_ hl.1, ?_, ?_⟩
    · intro k
      by_cases hk : k = k0
      · subst hk
        simp [hlam]
      · simp [Function.update_of_ne hk]
    · rw [segre_smul, Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp [f]
    · show Ψ ((Ψ (segre (modelLift M x x)) 0)⁻¹ • segre (modelLift M x x)) = Fin.cons 1 y
      rw [map_smul]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [hlam]
      · rw [← hq]
        simp [modelQ, div_eq_inv_mul]
  · rintro x1 ⟨_, h1⟩ x2 ⟨_, h2⟩ heq
    have l1 := (modelLift_spec M x1).1 x1 (mem_modelU M x1)
    have l2 := (modelLift_spec M x2).1 x2 (mem_modelU M x2)
    have hlam1 : Ψ (segre (modelLift M x1 x1)) 0 ≠ 0 := fun h => h1 (Or.inl h)
    have hlam2 : Ψ (segre (modelLift M x2 x2)) 0 ≠ 0 := fun h => h2 (Or.inl h)
    have hseg : segre (modelLift M x1 x1) =
        (Ψ (segre (modelLift M x1 x1)) 0 / Ψ (segre (modelLift M x2 x2)) 0) •
          segre (modelLift M x2 x2) := by
      have := congrArg (fun w => Ψ (segre (modelLift M x1 x1)) 0 • w) heq
      simp only [f, smul_smul, mul_inv_cancel₀ hlam1, one_smul] at this
      rw [div_eq_mul_inv]
      exact this
    obtain ⟨c, hc, hcz⟩ := sameOrbit_of_segre l2.1.1 _ (div_ne_zero hlam1 hlam2) hseg
    rw [← l1.2, ← l2.2]
    exact ((M.fibre _ l2.1 _ l1.1).2 ⟨c, hc, hcz⟩).symm

end GroundTheory.Heights₂.Heights.LowerBoundFree
