module

public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
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

@[expose] public section

noncomputable section

open ValuativeRel

namespace DiscreteGroups.sglob.LConv

theorem countable_quotient_of_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace.SeparableSpace G] (K : Subgroup G) (hK : IsOpen (K : Set G)) : Countable (G ⧸ K) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense G
  have : Countable D := hDc.to_subtype
  refine Function.Surjective.countable (f := fun d : D => ((d : G) : G ⧸ K)) fun q => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have ho : IsOpen ((fun x => x⁻¹ * g) ⁻¹' (K : Set G)) := hK.preimage (continuous_inv.mul continuous_const)
  obtain ⟨d, hd, hdD⟩ := hDd.inter_open_nonempty _ ho ⟨g, by simp⟩
  exact ⟨⟨d, hdD⟩, QuotientGroup.eq.2 hd⟩

theorem separableSpace_GL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m : ℕ) : TopologicalSpace.SeparableSpace (GL (Fin m) k) := by
  have : SecondCountableTopology (GL (Fin m) k) := inferInstance
  infer_instance

theorem unitOfUnif : UnitOfUnif := by
  intro hAlt hFin hUnif k _ _ _ _ m K hKo hKc H _ _ _ π hπ hcomm
  have := separableSpace_GL k m
  obtain ⟨N, hN⟩ := hUnif k m K hKo
  let F : Submodule ℂ H :=
    { carrier := {x | ∀ κ ∈ K, π κ x = x}
      add_mem' := fun {a b} ha hb κ hκ => by rw [map_add (f := _), ha κ hκ, hb κ hκ]
      zero_mem' := fun κ _ => map_zero _
      smul_mem' := fun c x hx κ hκ => by rw [map_smul, hx κ hκ] }
  have hF : IsClosed (F : Set H) := by
    have : (F : Set H) = ⋂ κ ∈ K, {x | π κ x = x} := by
      ext x
      simp only [Set.mem_iInter]
      rfl
    rw [this]
    exact isClosed_biInter fun κ _ => isClosed_eq (π κ).continuous continuous_id
  have : CompleteSpace F := hF.completeSpace_coe
  have h1 : ∀ x, F.starProjection x ∈ F := fun x => F.starProjection_apply_mem x
  have h2 : ∀ x ∈ F, F.starProjection x = x := fun x hx => Submodule.starProjection_eq_self_iff.2 hx
  obtain ⟨s, hs⟩ := hFin _ H π hπ hcomm F.starProjection (by ext x; exact h2 _ (h1 x)) (N ^ 2 + 1)
    (hAlt _ K hKo hKc (countable_quotient_of_isOpen K hKo) N hN H π hπ F.starProjection
      (isSelfAdjoint_starProjection F) h1 h2 _ (Nat.lt_succ_self _))
  exact ⟨s, fun x hx => h2 x hx ▸ hs x⟩

end DiscreteGroups.sglob.LConv

end
