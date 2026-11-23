module

public import Formalism.WachLatticeTwists.SplitLocalLifts.Cocycles1MapOfEquivariant
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
import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

theorem liftCoc : StatLiftCoc := by
  intro O D M₁ M₂ _ _ _ _ _ _ ρ₁ ρ₂ p hp hs Hf₁ Hf₂ ℓ e hL κ hκ
  obtain ⟨x, hx, hxe⟩ := hL _ hκ
  obtain ⟨K₀, rfl⟩ := Submodule.mkQ_surjective _ x
  have h1 : (Submodule.Quotient.mk (cocycles1MapOfEquivariant ρ₁ ρ₂ p hp K₀ - ((ℓ : O) ^ e) • κ) : H1z ρ₂) = 0 := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, sub_eq_zero]
    exact hxe
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h1
  obtain ⟨v, hv⟩ := h1
  obtain ⟨w, rfl⟩ := hs v
  let cb : coZ1s ρ₁ := ⟨fun g => ρ₁ g w - w, fun g h => by
    simp only [map_mul, Module.End.mul_apply, map_sub]
    abel⟩
  refine ⟨K₀ - cb, ?_, fun g => ?_⟩
  · have hcb : Submodule.mkQ _ cb = (0 : H1z ρ₁) := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact ⟨w, by funext g; rfl⟩
    rw [map_sub, hcb, sub_zero]
    exact hx
  · have h2 : ρ₂ g (p w) - p w = p ((K₀ : D → M₁) g) - ((ℓ : O) ^ e) • (κ : D → M₂) g :=
      congrFun hv g
    show p ((K₀ : D → M₁) g - (ρ₁ g w - w)) = _
    rw [map_sub, map_sub, hp, h2]
    abel

theorem colK : StatColK := by
  intro O A T' G _ _ _ _ _ P _ _ _ _ L _ _ _ _ r χ Dl inc v₁ ev hev hs Hf₁ Hf₂ ℓ e' j κ κz hκ hκf hL
  have key := fun a => liftCoc O Dl P L _ _ ev (ev_equiv r χ Dl inc v₁ ev hev) hs Hf₁ Hf₂ ℓ e' hL
    (κz a) (hκf a)
  choose Kz hKz1 hKz2 using key
  refine ⟨fun a g => if h : g ∈ Dl then inc ((Kz a : Dl → P) ⟨g, h⟩) else 0, Kz, ?_, hKz1, ?_⟩
  · intro a g
    dsimp only
    rw [dite_eq_left g.2]
  · intro a g hg
    dsimp only
    rw [dite_eq_left hg, ← hev, hKz2 a ⟨g, hg⟩, hκ a ⟨g, hg⟩]

theorem colk : StatColk := by
  intro O A T' G _ _ _ _ _ P _ _ _ _ M _ _ _ r χ E δO Dl inc ev hE hM hev hs Hf₁ Hf₂ ℓ e' u uz huz hmem hL
  obtain ⟨kz, hk1, hk2⟩ := liftCoc O Dl P _ _ _ ev (ev_equiv_triv r χ Dl ev hev) hs Hf₁ Hf₂ ℓ e' hL
    uz hmem
  refine ⟨fun g => if h : g ∈ Dl then inc ((kz : Dl → P) ⟨g, h⟩) else 0, kz, ?_, hk1, ?_, ?_⟩
  · intro g
    dsimp only
    rw [dite_eq_left g.2]
  · intro g
    dsimp only
    split_ifs with h
    · exact hE _
    · exact ⟨0, (zero_mul E).symm⟩
  · intro g hg m
    dsimp only
    rw [dite_eq_left hg, hM, hk2 ⟨g, hg⟩, Submodule.coe_smul, huz ⟨g, hg⟩, smul_eq_mul, mul_assoc]

theorem colFun : StatColFun := by
  intro O A T' G _ _ _ _ _ P _ _ _ _ V _ _ r χ Dl inc Hf₁ Lf H K Kz hK hKz s
  have h := H ((LinearMap.toSpanSingleton A V s).comp inc) Kz hKz
  have e : (fun g : Dl => K g • s) =
      fun g : Dl => ((LinearMap.toSpanSingleton A V s).comp inc) ((Kz : Dl → P) g) := by
    funext g
    rw [hK g]
    rfl
  rw [e]
  exact h

end Formalism.RepresentationBoundsCohomology.JL
