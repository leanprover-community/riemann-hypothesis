module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqZeroOfNotPrimaryStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteMonicNatDegree
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsUnitIffCharpolyCoeffZeroNe
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem ipGL_rootSum_eq_sum_torus : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ) (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V → ∀ l : ℕ, ipGL φ (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) = ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ Module.finrank F V - 1) = 1}, ((Module.finrank F V / (minpoly F α).natDegree : ℕ) : ℂ) * mass φ (minpoly F α ^ (Module.finrank F V / (minpoly F α).natDegree)) * star (θ α ^ l) := by
  intro F _ _ V _ _ _ θ φ hcl hprim hpos l
  rw [ipGL_charpoly_eq_finsum_mass F V φ (rootSum θ l)]
  refine sum_poly_eq_sum_torus F θ (Module.finrank F V) hpos (mass φ) l ?_

  intro P _ _ hP
  unfold mass
  rw [finsum_mem_def]
  refine finsum_eq_zero_of_forall_eq_zero fun g => ?_
  by_cases hg : LinearMap.charpoly g = P
  · rw [Set.indicator_of_mem (show g ∈ {g : Module.End F V | LinearMap.charpoly g = P} from hg)]
    exact GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow F V φ hcl hprim hpos g (hg ▸ hP)
  · exact Set.indicator_of_notMem (show g ∉ {g : Module.End F V | LinearMap.charpoly g = P} from hg) _

end GlobalTheory.CuspGL
