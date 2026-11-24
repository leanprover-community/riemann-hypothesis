module

public import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.SetTheory.ZFC.PSet
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def LCompInt : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p →
  ConnectedSpace X → IsIntegral X

theorem noeth_components {α : Type*} [TopologicalSpace α] [TopologicalSpace.NoetherianSpace α] :
    Finite (_root_.ConnectedComponents α) ∧ ∀ x : α, IsOpen (connectedComponent x) := by
  classical
  obtain ⟨S, hSf, hSc, hSi, hSu⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_univ (X := α))
  have hin : ∀ x : α, ∃ t ∈ S, x ∈ t := fun x => by
    have : x ∈ ⋃₀ S := hSu ▸ Set.mem_univ x
    simpa using this
  have hsub : ∀ t ∈ S, ∀ z ∈ t, t ⊆ connectedComponent z := fun t ht z hz =>
    (IsIrreducible.isConnected (hSi t ht)).isPreconnected.subset_connectedComponent hz
  refine ⟨?_, fun x => ?_⟩
  · have : Finite S := hSf.to_subtype
    refine Finite.of_surjective (fun t : S => (((IsIrreducible.nonempty (hSi t.1 t.2)).some : α) : _root_.ConnectedComponents α)) ?_
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨t, ht, hxt⟩ := hin x
    refine ⟨⟨t, ht⟩, ConnectedComponents.coe_eq_coe.mpr ?_⟩
    exact connectedComponent_eq (hsub t ht _ (IsIrreducible.nonempty (hSi t ht)).some_mem hxt)
  · have hc : (connectedComponent x)ᶜ = ⋃₀ {t ∈ S | Disjoint t (connectedComponent x)} := by
      ext z
      simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_setOf_eq]
      constructor
      · intro hz
        obtain ⟨t, ht, hzt⟩ := hin z
        refine ⟨t, ⟨ht, Set.disjoint_left.mpr fun w hwt hwx => hz ?_⟩, hzt⟩
        rw [connectedComponent_eq hwx]; exact hsub t ht w hwt hzt
      · rintro ⟨t, ⟨_, hd⟩, hzt⟩ hzx
        exact Set.disjoint_left.mp hd hzt hzx
    rw [← isClosed_compl_iff, hc]
    have hfin : ({t ∈ S | Disjoint t (connectedComponent x)}).Finite := hSf.subset (Set.sep_subset _ _)
    rw [Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion fun t ht => hSc t ht.1

theorem comp_fin {k : Type} [Field k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) :
    Finite (_root_.ConnectedComponents X) ∧ ∀ x : X, IsOpen (connectedComponent x) := by
  have := hp.1; have := hp.2
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsNoetherian X := {}
  exact noeth_components

theorem clopen_smoothProper_projective {k : Type} [Field k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (hX : IsProj p)
    (U : X.Opens) (hU : IsClosed (U : Set X)) : SP d (U.ι ≫ p) ∧ IsProj (U.ι ≫ p) := by
  have : IsClosedImmersion U.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hU)
  have := hp.1
  have := hp.2
  have hs := smoothOfRelativeDimension_comp (n := 0) (m := d) U.ι p
  rw [Nat.zero_add] at hs
  refine ⟨⟨inferInstance, hs⟩, ?_⟩
  obtain ⟨N, ι, hι, hιp⟩ := hX
  exact ⟨N, U.ι ≫ ι, inferInstance, by rw [Category.assoc, hιp]⟩

end LateralTheory.EtaleTrace
