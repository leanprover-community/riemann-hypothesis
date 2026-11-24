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

namespace GlobalTheory.CompanionTheory.Smooth

def linearFormStabiliser {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) : Subgroup G where
  carrier := {g : G | l ∘ₗ ρ g = l}
  mul_mem' := by
    intro a b ha hb
    have ha' : l ∘ₗ ρ a = l := ha
    have hb' : l ∘ₗ ρ b = l := hb
    show l ∘ₗ ρ (a * b) = l
    rw [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ha', hb']
  one_mem' := by
    show l ∘ₗ ρ 1 = l
    rw [map_one]
    rfl
  inv_mem' := by
    intro a ha
    have ha' : l ∘ₗ ρ a = l := ha
    show l ∘ₗ ρ a⁻¹ = l
    conv_lhs => rw [← ha']
    rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]
    rfl

theorem isOpen_linearForm_stabiliser {G V : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (hK : IsOpen (K : Set G)) (l : Module.Dual ℂ V)
    (hl : ∀ x ∈ K, l ∘ₗ ρ x = l) : IsOpen {g : G | l ∘ₗ ρ g = l} :=
  Subgroup.isOpen_mono (H₁ := K) (H₂ := linearFormStabiliser ρ l) (fun x hx => hl x hx) hK

end GlobalTheory.CompanionTheory.Smooth
