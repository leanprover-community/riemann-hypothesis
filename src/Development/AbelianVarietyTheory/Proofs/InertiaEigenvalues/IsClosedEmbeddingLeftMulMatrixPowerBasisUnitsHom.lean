module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LinDesc

theorem tm_isClosedEmbedding : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p), Topology.IsClosedEmbedding (LinDesc.tm A hG) := by
  intro F E _ _ _ _ hU A r τ p hG
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let e : A.K ≃ₗ[F] (Fin r → F) := (bas A hG).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he' : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let eh : A.K ≃ₜ (Fin r → F) :=
    { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  let g : (Fin r → F) →ₗ[F] Matrix (Fin r) (Fin r) F :=
    (Algebra.leftMulMatrix (bas A hG)).toLinearMap ∘ₗ e.symm.toLinearMap
  have hg : IsClosedEmbedding g := by
    refine LinearMap.isClosedEmbedding_of_injective ?_
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    have h1 := Algebra.leftMulMatrix_injective (bas A hG) hxy
    exact e.symm.injective h1
  let f : A.K → Matrix (Fin r) (Fin r) F := fun x => Algebra.leftMulMatrix (bas A hG) x
  have hf : IsClosedEmbedding f := by
    have : f = g ∘ eh := by
      funext x; simp [f, g, eh, e]
    rw [this]; exact hg.comp eh.isClosedEmbedding
  haveI : T2Space A.K := eh.isEmbedding.t2Space
  have hfo : IsClosedEmbedding (fun x : A.Kᵐᵒᵖ => MulOpposite.op (f (MulOpposite.unop x))) :=
    MulOpposite.opHomeomorph.isClosedEmbedding.comp (hf.comp MulOpposite.opHomeomorph.symm.isClosedEmbedding)
  have hP : IsClosedEmbedding (Prod.map f (fun x : A.Kᵐᵒᵖ => MulOpposite.op (f (MulOpposite.unop x)))) :=
    hf.prodMap hfo
  have hK : IsClosedEmbedding (Units.embedProduct A.K) := Units.isClosedEmbedding_embedProduct
  have hM : IsClosedEmbedding (Units.embedProduct (Matrix (Fin r) (Fin r) F)) := Units.isClosedEmbedding_embedProduct
  have hcomp : (Units.embedProduct (Matrix (Fin r) (Fin r) F)) ∘ (LinDesc.tm A hG) =
      (Prod.map f (fun x : A.Kᵐᵒᵖ => MulOpposite.op (f (MulOpposite.unop x)))) ∘ Units.embedProduct A.K := by
    funext t
    simp only [Function.comp_apply, Units.embedProduct_apply, Prod.map_apply, MulOpposite.unop_op]
    refine Prod.ext ?_ ?_
    · exact tm_coe A hG t
    · simp only
      rw [tm_inv_coe]
  have hc : IsClosedEmbedding ((Units.embedProduct (Matrix (Fin r) (Fin r) F)) ∘ (LinDesc.tm A hG)) := by
    rw [hcomp]; exact hP.comp hK
  have hcont : Continuous (LinDesc.tm A hG) := by
    rw [hM.isInducing.continuous_iff]; exact hc.continuous
  refine ⟨⟨Topology.IsInducing.of_comp hcont hM.continuous hc.isInducing, ?_⟩, ?_⟩
  · intro x y hxy
    exact hc.injective (by simp [Function.comp_apply, hxy])
  · have : Set.range (LinDesc.tm A hG) = (Units.embedProduct (Matrix (Fin r) (Fin r) F)) ⁻¹' Set.range ((Units.embedProduct (Matrix (Fin r) (Fin r) F)) ∘ (LinDesc.tm A hG)) := by
      ext x; constructor
      · rintro ⟨t, rfl⟩; exact ⟨t, rfl⟩
      · rintro ⟨t, ht⟩; exact ⟨t, hM.injective ht⟩
    rw [this]; exact hc.isClosed_range.preimage hM.continuous

end GlobalTheory.JR.LinDesc
