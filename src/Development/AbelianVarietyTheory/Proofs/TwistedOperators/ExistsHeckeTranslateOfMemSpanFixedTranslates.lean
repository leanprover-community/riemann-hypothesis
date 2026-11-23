module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeActsByScalarCommutative
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalThetaInertPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe

@[expose] public section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta.AvgHecke

open GlobalTheory.PRep

theorem exists_hecke_of_mem_span : ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (s w : M), (∀ k ∈ K, ρ k s = s) → (∀ k ∈ K, ρ k w = w) → w ∈ Submodule.span ℂ (Set.range fun g => ρ g s) → ∃ h ∈ Hecke ℂ K, heckeVec ρ K h s = w := by
  classical
  intro G _ K hK M _ _ ρ s w hs hw hspan
  have hx : s ∈ fixed ρ K := GlobalTheory.LGrp.mem_fixed.2 hs
  have hy : w ∈ fixed ρ K := GlobalTheory.LGrp.mem_fixed.2 hw
  have hr : w ∈ LinearMap.range (GlobalTheory.LFun.HeckeScalar.orbitMap ρ K s) := by
    refine Submodule.span_le.2 ?_ hspan
    rintro _ ⟨g, rfl⟩
    exact ⟨Finsupp.single (g : G ⧸ K) 1, by rw [GlobalTheory.LFun.HeckeScalar.orbitMap_single hx, one_smul]⟩
  obtain ⟨φ, rfl⟩ := hr
  obtain ⟨ψ, hψ, e⟩ := GlobalTheory.LFun.HeckeScalar.exists_fixed_preimage _ (GlobalTheory.LFun.HeckeScalar.orbitMap_permRep hx)
    (GlobalTheory.LFun.HeckeScalar.mem_finOrbit hK φ) hy
  refine ⟨fun g => ψ g, ⟨fun a b g => ?_, ψ.support.image Quotient.out, fun g hg => ?_⟩, ?_⟩
  · have := GlobalTheory.LFun.HeckeScalar.permRep_apply (a : G) ψ (g : G ⧸ K)
    rw [GlobalTheory.LGrp.mem_fixed.1 hψ _ a.2] at this
    simpa using this
  · obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul K g
    exact ⟨_, Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.2 hg), 1, j⁻¹, by simp [hj]⟩
  · rw [← e, heckeVec, GlobalTheory.LFun.HeckeScalar.orbitMap, Finsupp.linearCombination_apply, Finsupp.sum,
      finsum_eq_sum_of_support_subset (s := ψ.support)]
    · simp
    · intro c hc
      by_contra h
      exact hc (by simp [Finsupp.notMem_support_iff.1 h])

end GlobalTheory.SphTheta.AvgHecke

end
