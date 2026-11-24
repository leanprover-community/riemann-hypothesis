module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Properties
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem exists_isOpen_common_generization {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] (p : Y) :
    ∃ V : Set Y, IsOpen V ∧ p ∈ V ∧ ∀ q ∈ V, ∃ z : Y, z ⤳ p ∧ z ⤳ q := by
  have hF : (irreducibleComponents Y).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  refine ⟨⋂ Z ∈ {Z ∈ irreducibleComponents Y | p ∉ Z}, Zᶜ, ?_, ?_, ?_⟩
  · refine (hF.subset (Set.sep_subset _ _)).isOpen_biInter fun Z hZ => ?_
    exact (isClosed_of_mem_irreducibleComponents Z hZ.1).isOpen_compl
  · simp only [Set.mem_iInter]
    exact fun Z hZ => hZ.2
  · intro q hq
    have hmem := irreducibleComponent_mem_irreducibleComponents q
    have hpZ : p ∈ irreducibleComponent q := by
      by_contra hp
      exact (Set.mem_iInter₂.1 hq _ ⟨hmem, hp⟩) mem_irreducibleComponent
    obtain ⟨z, hz⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := q))
      isClosed_irreducibleComponent
    exact ⟨z, hz.specializes hpZ, hz.specializes mem_irreducibleComponent⟩

theorem genPt_specializes_of_specializes {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) {p z : X}
    (hp : genPt ξ ⤳ p) (hz : z ⤳ p) : genPt ξ ⤳ z := by
  apply GlobalTheory.CompanionTheory.Ar.Flat.genPt_specializes_of_specializes <;> assumption

theorem isClopen_setOf_genPt_specializes (X : Scheme.{0}) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (h : IsCptGen ξ) :
    IsClopen {q : X | genPt ξ ⤳ q} := by
  refine ⟨?_, ?_⟩
  · have : {q : X | genPt ξ ⤳ q} = closure {genPt ξ} := by
      ext q; exact specializes_iff_mem_closure
    rw [this]; exact isClosed_closure
  · rw [isOpen_iff_mem_nhds]
    intro p hp
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := p) trivial
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    obtain ⟨V, hV, hpV, hVq⟩ := @exists_isOpen_common_generization U _
      (noetherianSpace_of_isAffineOpen U hU) U.isOpen.isOpenEmbedding_subtypeVal.quasiSober
      ⟨p, hpU⟩
    have hopen : IsOpen (Subtype.val '' V : Set X) := U.isOpen.isOpenMap_subtype_val V hV
    refine Filter.mem_of_superset (hopen.mem_nhds ⟨_, hpV, rfl⟩) ?_
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨z, hzp, hzq⟩ := hVq q hq
    exact (genPt_specializes_of_specializes ξ h (p := p) hp
      (hzp.map continuous_subtype_val)).trans (hzq.map continuous_subtype_val)

end GlobalTheory.CompanionTheory.Ar
