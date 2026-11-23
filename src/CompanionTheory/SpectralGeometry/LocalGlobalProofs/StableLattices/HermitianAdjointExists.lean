module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori

theorem exists_adjoint_herm : ∀ {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] (s : L →+* L), IsInv s → ∀ h : V → V → L, IsHerm s h →
    ∀ g : Module.End L V, ∃ g' : Module.End L V, ∀ x y, h (g x) y = h x (g' y) := by
  intro L V _ _ _ _ s hs h hh g
  obtain ⟨hadd2, hsmul2, hsymm, hnd⟩ := hh
  have hss := hs.1
  have hadd1 : ∀ x x' y, h (x + x') y = h x y + h x' y := by
    intro x x' y
    rw [hsymm y (x + x'), hadd2, map_add (f := _), ← hsymm, ← hsymm]
  have hsmul1 : ∀ (a : L) x y, h (a • x) y = s a * h x y := by
    intro a x y
    rw [hsymm y (a • x), hsmul2, map_mul, ← hsymm]

  let ψ₀ : V → Module.Dual L V := fun x =>
    { toFun := h x
      map_add' := hadd2 x
      map_smul' := fun a y => by simpa using hsmul2 a x y }
  have ψ₀_apply : ∀ x y, ψ₀ x y = h x y := fun _ _ => rfl
  let ψ : V →+ Module.Dual L V := AddMonoidHom.mk' ψ₀ (fun x x' => by
    ext y
    simp [ψ₀_apply, hadd1])
  have ψ_apply : ∀ x y, ψ x y = h x y := fun _ _ => rfl
  have ψ_smul : ∀ (a : L) x, ψ (a • x) = s a • ψ x := by
    intro a x
    ext y
    simp [ψ_apply, hsmul1]
  have ψ_inj : ∀ x, ψ x = 0 → x = 0 := by
    intro x hx
    exact hnd x (fun y => by rw [← ψ_apply, hx]; rfl)
  have ψ_inj' : ∀ x x', ψ x = ψ x' → x = x' := by
    intro x x' hxx
    exact sub_eq_zero.mp (ψ_inj _ (by rw [map_sub, hxx, sub_self]))

  let b := Module.finBasis L V
  have hli : LinearIndependent L (fun i => ψ (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h0 : ψ (∑ j, s (c j) • b j) = 0 := by

      rw [map_sum, ← hc]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [ψ_smul, hss]
    have h1 := ψ_inj _ h0
    have h2 := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h1 i
    have h3 := congrArg s h2
    rwa [hss, map_zero] at h3
  have hspan : Submodule.span L (Set.range fun i => ψ (b i)) = ⊤ := by
    refine hli.span_eq_top_of_card_eq_finrank' ?_
    rw [Subspace.dual_finrank_eq]
    simp
  have ψ_surj : ∀ f : Module.Dual L V, ∃ z, ψ z = f := by
    intro f
    have hf : f ∈ Submodule.span L (Set.range fun i => ψ (b i)) := by
      rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hf
    refine ⟨∑ j, s (c j) • b j, ?_⟩

    rw [map_sum, ← hc]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ψ_smul, hss]
  choose z hz using fun y => ψ_surj ((ψ y).comp g)
  have hz' : ∀ y x, h (z y) x = h y (g x) := by
    intro y x
    rw [← ψ_apply, hz]
    rfl
  refine ⟨{ toFun := z, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro y y'
    apply ψ_inj'
    rw [hz, map_add (f := _), map_add (f := _), hz, hz]
    rfl
  · intro a y
    apply ψ_inj'
    rw [hz, RingHom.id_apply, ψ_smul, ψ_smul, hz]
    rfl
  · intro x y
    show h (g x) y = h x (z y)
    rw [hsymm (z y) x, hz', ← hsymm]

end GlobalTheory.CompanionTheory.Iwahori
