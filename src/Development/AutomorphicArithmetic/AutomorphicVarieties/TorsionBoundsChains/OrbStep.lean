module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory UpperTheory.V.KH

private theorem UpperTheory.V.KH.stabLe_sub {G X : Type} [Group G] [MulAction G X] {s : ℕ}
    (h : StabLe G X s) (U : SubMulAction G X) : StabLe G U s := by
  intro u
  rw [SubMulAction.stabilizer_of_subMul]
  exact h u

theorem UpperTheory.V.KH.orbStep :
    ∀ (G X : Type) [Group G] [MulAction G X] (A s : ℕ) (x : X), OrbLe G X (A + 1) → StabLe G X s →
      ∃ U V : SubMulAction G X, (∀ y, y ∈ V ↔ y ∉ U) ∧ Nonempty U ∧ MulAction.IsPretransitive G U ∧
        StabLe G U s ∧ StabLe G V s ∧ OrbLe G V A := by
  intro G X _ _ A s x hO hS
  let U : SubMulAction G X :=
    { carrier := MulAction.orbit G x
      smul_mem' := by
        rintro g y ⟨h, rfl⟩
        exact ⟨g * h, mul_smul _ _ _⟩ }
  have hxU : x ∈ U := MulAction.mem_orbit_self x
  refine ⟨U, Uᶜ, fun y => Iff.rfl, ⟨⟨x, hxU⟩⟩, ?_, stabLe_sub hS U, stabLe_sub hS Uᶜ, ?_⟩
  · refine ⟨fun a b => ?_⟩
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨g, rfl⟩ := ha
    obtain ⟨h, rfl⟩ := hb
    refine ⟨h * g⁻¹, Subtype.ext ?_⟩
    change (h * g⁻¹) • g • x = h • x
    rw [smul_smul, inv_mul_cancel_right]
  · have hrel : ∀ a b : (Uᶜ : SubMulAction G X),
        (MulAction.orbitRel G (Uᶜ : SubMulAction G X)) a b ↔ (MulAction.orbitRel G X) a b := by
      intro a b
      rw [SubMulAction.orbitRel_of_subMul]
      rfl
    let f : MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X) → MulAction.orbitRel.Quotient G X :=
      Quotient.map (fun a => (a : X)) (fun a b hab => (hrel a b).1 hab)
    let F : Option (MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X)) →
        MulAction.orbitRel.Quotient G X := fun o => o.elim (Quotient.mk _ x) f
    have hF : Function.Injective F := by
      have hne : ∀ a : (Uᶜ : SubMulAction G X),
          (Quotient.mk _ (a : X) : MulAction.orbitRel.Quotient G X) ≠ Quotient.mk _ x := by
        intro a hax
        have h1 : (MulAction.orbitRel G X) (a : X) x := Quotient.exact hax
        exact a.2 h1
      rintro (_ | p) (_ | q) hpq
      · rfl
      · induction q using Quotient.inductionOn with
        | h b => exact absurd hpq.symm (hne b)
      · induction p using Quotient.inductionOn with
        | h a => exact absurd hpq (hne a)
      · induction p using Quotient.inductionOn with
        | h a =>
          induction q using Quotient.inductionOn with
          | h b =>
            congr 1
            exact Quotient.sound ((hrel a b).2 (Quotient.exact hpq))
    haveI : Finite (MulAction.orbitRel.Quotient G X) := hO.1
    haveI : Finite (Option (MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X))) :=
      Finite.of_injective F hF
    haveI : Finite (MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X)) :=
      Finite.of_injective some (Option.some_injective _)
    refine ⟨inferInstance, ?_⟩
    have h2 := Nat.card_le_card_of_injective F hF
    rw [Finite.card_option] at h2
    have h3 := hO.2
    omega
