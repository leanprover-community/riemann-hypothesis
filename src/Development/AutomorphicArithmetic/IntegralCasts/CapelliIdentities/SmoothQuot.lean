module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

namespace UpperTheory.Reformulated.B.Gwb5

noncomputable def IsSmooth {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [TopologicalSpace G] (ρ : Representation k G V) : Prop :=
  ∀ v : V, IsOpen {g : G | ρ g v = v}

theorem smooth_quot {G : Type} [Group G] {U : Type} [AddCommGroup U] [Module ℂ U]
    [TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G U} (h : IsSmooth ρ)
    (T : Submodule ℂ U) (hst : ∀ g : G, T ≤ Submodule.comap (ρ g) T) :
    IsSmooth (ρ.quotient T hst) := by
  intro v
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective T v
  let H : Subgroup G :=
    { carrier := {g : G | ρ.quotient T hst g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u}
      one_mem' := by
        show ρ.quotient T hst 1 _ = _
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ.quotient T hst a (Submodule.Quotient.mk u) = Submodule.Quotient.mk u := ha
        have hb' : ρ.quotient T hst b (Submodule.Quotient.mk u) = Submodule.Quotient.mk u := hb
        show ρ.quotient T hst (a * b) _ = _
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ.quotient T hst a (Submodule.Quotient.mk u) = Submodule.Quotient.mk u := ha
        show ρ.quotient T hst a⁻¹ _ = _
        conv_lhs => rw [← ha']
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl }
  refine H.isOpen_of_mem_nhds (g := 1) ?_
  have h1 : {g : G | ρ g u = u} ∈ nhds (1 : G) :=
    (h u).mem_nhds (by
      show ρ 1 u = u
      rw [map_one]
      rfl)
  refine Filter.mem_of_superset h1 ?_
  intro g hg
  have hg' : ρ g u = u := hg
  show ρ.quotient T hst g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u
  have e : ρ.quotient T hst g (Submodule.Quotient.mk u) = Submodule.Quotient.mk (ρ g u) := rfl
  rw [e, hg']

end UpperTheory.Reformulated.B.Gwb5
