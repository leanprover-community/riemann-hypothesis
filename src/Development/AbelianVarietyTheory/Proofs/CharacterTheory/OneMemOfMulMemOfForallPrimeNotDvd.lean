module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

@[expose] public section

namespace GlobalTheory

theorem one_mem_of_mul_mem_of_forall_prime_not_dvd (X : Type) [Finite X]
    (S : AddSubgroup (X → ℤ)) (hmul : ∀ f ∈ S, ∀ g ∈ S, f * g ∈ S)
    (hp : ∀ (x : X) (p : ℕ), p.Prime → ∃ f ∈ S, ¬ (p : ℤ) ∣ f x) : (1 : X → ℤ) ∈ S := by
  classical
  have h1 : ∀ x : X, ∃ f ∈ S, f x = 1 := by
    intro x
    obtain ⟨d, hd⟩ := Int.subgroup_cyclic (S.map (Pi.evalAddMonoidHom (fun _ : X => ℤ) x))
    have hd1 : (d : ℤ).natAbs = 1 := by
      rw [Nat.eq_one_iff_not_exists_prime_dvd]
      intro p pp hpd
      obtain ⟨f, hf, hnd⟩ := hp x p pp
      apply hnd
      have hmem : f x ∈ AddSubgroup.zmultiples (d : ℤ) := by
        obtain ⟨z, hz⟩ := hd ⟨f x, ⟨f, hf, rfl⟩⟩
        rw [Int.mem_zmultiples_iff]
        refine ⟨z, ?_⟩
        simpa [zsmul_eq_mul, mul_comm] using (congrArg Subtype.val hz).symm
      exact (Int.natCast_dvd.mpr hpd).trans (Int.mem_zmultiples_iff.mp hmem)
    have : (1 : ℤ) ∈ AddSubgroup.zmultiples (d : ℤ) := by
      rw [Int.mem_zmultiples_iff]
      exact isUnit_iff_dvd_one.mp (Int.isUnit_iff_natAbs_eq.mpr hd1)
    have hmap : (1 : ℤ) ∈ S.map (Pi.evalAddMonoidHom (fun _ : X => ℤ) x) := by
      obtain ⟨z, hz⟩ := Int.mem_zmultiples_iff.mp this
      have hzmem : z • (d : ℤ) ∈ S.map (Pi.evalAddMonoidHom (fun _ : X => ℤ) x) :=
        AddSubgroup.zsmul_mem _ d.property z
      simpa [hz, mul_comm] using hzmem
    obtain ⟨f, hf, hfx⟩ := hmap
    exact ⟨f, hf, hfx⟩
  choose f hfS hf1 using h1
  have key : ∀ s : Finset X, 1 - ∏ x ∈ s, (1 - f x) ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have e : 1 - (1 - f a) * ∏ x ∈ s, (1 - f x)
          = f a + (1 - ∏ x ∈ s, (1 - f x)) - f a * (1 - ∏ x ∈ s, (1 - f x)) := by ring
      rw [e]
      exact S.sub_mem (S.add_mem (hfS a) ih) (hmul _ (hfS a) _ ih)
  haveI := Fintype.ofFinite X
  have h0 : ∏ x : X, (1 - f x) = 0 := by
    funext y
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ y) (by simp [hf1])
  simpa [h0] using key Finset.univ

end GlobalTheory
