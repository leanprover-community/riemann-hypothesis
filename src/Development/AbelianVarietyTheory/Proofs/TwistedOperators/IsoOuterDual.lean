module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
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

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

theorem iso_outer_dual (ι G : Type) [Fintype ι] [Group G] (V : ι → Type) [∀ τ, AddCommGroup (V τ)]
    [∀ τ, Module ℂ (V τ)] [∀ τ, FiniteDimensional ℂ (V τ)] (ρ : ∀ τ, Representation ℂ G (V τ)) :
    Iso (outer ρ).dual (outer fun τ => (ρ τ).dual) := by
  classical
  refine Iso.symm ⟨PiTensorProduct.dualDistribEquiv, fun g t => ?_⟩
  have hD : ∀ s, (PiTensorProduct.dualDistribEquiv (R := ℂ) (M := V)) s = PiTensorProduct.dualDistrib s :=
    fun _ => rfl
  rw [hD, hD]

  suffices h : PiTensorProduct.dualDistrib ∘ₗ (outer fun τ => (ρ τ).dual) g =
      (outer ρ).dual g ∘ₗ (PiTensorProduct.dualDistrib (R := ℂ) (M := V)) by
    exact LinearMap.congr_fun h t
  refine PiTensorProduct.ext (MultilinearMap.ext fun f => ?_)
  refine PiTensorProduct.ext (MultilinearMap.ext fun m => ?_)
  simp [outer_apply, Representation.dual_apply, PiTensorProduct.map_tprod, Pi.inv_apply,
    Module.Dual.transpose_apply, LinearMap.comp_apply]

end GlobalTheory.OneFunctional
