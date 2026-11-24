module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RepresentationTheory.Maschke
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions

@[expose] public section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.IsotypicMap

open Representation

variable {H V V' W : Type} [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W]

theorem exists_comp_ne_zero {τ : Representation ℂ H V} {τ' : Representation ℂ H V'} {ρ : Representation ℂ H W}
    (h : IsIsotypicOf τ ρ) (T : IntertwiningMap τ τ') (hT : T ≠ 0) :
    ∃ f : IntertwiningMap ρ τ, T.comp f ≠ 0 := by
  by_contra hc
  push Not at hc
  apply hT
  apply IntertwiningMap.ext
  rw [IntertwiningMap.zero_toLinearMap, ← LinearMap.ker_eq_top, ← top_le_iff, ← (show _ = _ from h)]
  refine iSup_le fun f => ?_
  rintro _ ⟨w, rfl⟩
  exact congrArg (fun g : IntertwiningMap ρ τ' => g w) (hc f)

theorem exists_leftInverse [Finite H] {τ : Representation ℂ H V} {ρ : Representation ℂ H W}
    (f : IntertwiningMap ρ τ) (hf : Function.Injective f) :
    ∃ s : IntertwiningMap τ ρ, ∀ w, s (f w) = w := by
  have : NeZero (Nat.card H : ℂ) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
  obtain ⟨g, hg⟩ := MonoidAlgebra.exists_leftInverse_of_injective
    (IntertwiningMap.equivLinearMapAsModule ρ τ f) (LinearMap.ker_eq_bot.2 hf)
  exact ⟨(IntertwiningMap.equivLinearMapAsModule τ ρ).symm g, fun w => LinearMap.congr_fun hg w⟩

theorem equiv_of_isotypic_map : ∀ (H : Type) [Group H] [Finite H] (V V' W W' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (τ : Representation ℂ H V) (τ' : Representation ℂ H V') (ρ : Representation ℂ H W) (ρ' : Representation ℂ H W'), ρ.IsIrreducible → ρ'.IsIrreducible → IsIsotypicOf τ ρ → IsIsotypicOf τ' ρ' → ∀ T : Representation.IntertwiningMap τ τ', T ≠ 0 → Nonempty (Representation.Equiv ρ ρ') := by
  intro H _ _ V V' W W' _ _ _ _ _ _ _ _ τ τ' ρ ρ' hρ hρ' h h' T hT
  obtain ⟨f, hf⟩ := exists_comp_ne_zero h T hT
  have hi := (Representation.IsIrreducible.injective_or_eq_zero (T.comp f)).resolve_right hf
  obtain ⟨s, hs⟩ := exists_leftInverse (T.comp f) hi
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hf
    apply IntertwiningMap.ext
    ext w
    have hw : w = 0 := (hs w).symm
    subst hw
    simp
  obtain ⟨f', hf'⟩ := exists_comp_ne_zero h' s hs0
  have hb := (Representation.IsIrreducible.bijective_or_eq_zero (s.comp f')).resolve_right hf'
  exact ⟨(IntertwiningMap.ofBijective _ hb).symm⟩

end GlobalTheory.IsotypicMap
