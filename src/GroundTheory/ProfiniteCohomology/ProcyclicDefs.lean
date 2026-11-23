module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Topology.LocallyConstant.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

variable {G : Type*} [Group G] [TopologicalSpace G]

def IsTopologicalGenerator (σ : G) : Prop :=
  Dense (Subgroup.zpowers σ : Set G)

theorem _root_.IsLocallyConstant.eq_of_eqOn_dense {X Y : Type*} [TopologicalSpace X] {f g : X → Y}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) {s : Set X} (hs : Dense s)
    (h : Set.EqOn f g s) : f = g := by
  let _ : TopologicalSpace Y := ⊥
  have : DiscreteTopology Y := ⟨rfl⟩
  exact Continuous.ext_on hs hf.continuous hg.continuous h

namespace IsTopologicalGenerator

variable {σ : G}

theorem eq_of_forall_zpow (hσ : IsTopologicalGenerator σ) {Y : Type*} {f g : G → Y}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) (h : ∀ n : ℤ, f (σ ^ n) = g (σ ^ n)) :
    f = g :=
  hf.eq_of_eqOn_dense hg hσ fun _ ⟨n, hn⟩ => hn ▸ h n

theorem eq_of_forall_zpow_pi (hσ : IsTopologicalGenerator σ) {n : ℕ} {Y : Type*}
    {f g : (Fin n → G) → Y} (hf : IsLocallyConstant f) (hg : IsLocallyConstant g)
    (h : ∀ m : Fin n → ℤ, f (fun i => σ ^ m i) = g (fun i => σ ^ m i)) : f = g := by
  refine hf.eq_of_eqOn_dense hg (s := Set.univ.pi fun _ => (Subgroup.zpowers σ : Set G))
    (dense_pi Set.univ fun _ _ => hσ) fun x hx => ?_
  choose m hm using fun i => hx i (Set.mem_univ i)
  have hx' : x = fun i => σ ^ m i := funext fun i => (hm i).symm
  rw [hx']
  exact h m

end IsTopologicalGenerator

end GroundTheory.ProfCoh
