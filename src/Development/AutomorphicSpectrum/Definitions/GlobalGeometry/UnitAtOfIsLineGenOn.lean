module

import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HodgeComponentFlagDegree
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
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
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InjectiveOfIsCptGen

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GenModel

open AlgebraicGeometry CategoryTheory

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X}

private theorem iota_multi_mem_span_of_mem_span {R : Subring Ω} {r : ℕ} {e : Fin r → E} (b : Fin r → E)
    (hb : ∀ i, b i ∈ Submodule.span R (Set.range e)) :
    exteriorPower.ιMulti Ω r b ∈ Submodule.span R {exteriorPower.ιMulti Ω r e} := by
  suffices H : ∀ s : Finset (Fin r), ∀ b : Fin r → E, (∀ i, b i ∈ Submodule.span R (Set.range e)) →
      (∀ i, i ∉ s → b i ∈ Set.range e) →
      exteriorPower.ιMulti Ω r b ∈ Submodule.span R {exteriorPower.ιMulti Ω r e} from
    H Finset.univ b hb (fun i hi => absurd (Finset.mem_univ i) hi)
  intro s
  refine Finset.induction_on s ?_ ?_
  · intro b _ hb'
    choose g hg using fun i => hb' i (Finset.notMem_empty i)
    have hbg : b = e ∘ g := funext fun i => (hg i).symm
    subst hbg
    by_cases hinj : Function.Injective g
    · have hσ := Finite.injective_iff_bijective.1 hinj
      have he : e ∘ g = e ∘ ⇑(Equiv.ofBijective g hσ) := rfl
      rw [he, AlternatingMap.map_perm, Units.smul_def]
      exact zsmul_mem (Submodule.mem_span_singleton_self _) _
    · rw [AlternatingMap.map_eq_zero_of_not_injective _ _ (fun h => hinj h.of_comp)]
      exact Submodule.zero_mem _
  · intro a s ha ih b hb hb'
    have key : ∀ y ∈ Submodule.span R (Set.range e),
        exteriorPower.ιMulti Ω r (Function.update b a y) ∈
          Submodule.span R {exteriorPower.ιMulti Ω r e} := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        apply ih
        · intro i
          rcases eq_or_ne i a with rfl | hi
          · simpa using Submodule.subset_span hy
          · rw [Function.update_of_ne hi]
            exact hb i
        · intro i hi
          rcases eq_or_ne i a with rfl | hia
          · simpa using hy
          · rw [Function.update_of_ne hia]
            exact hb' i (by simp [hia, hi])
      | zero =>
        rw [AlternatingMap.map_update_zero]
        exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        rw [AlternatingMap.map_update_add]
        exact Submodule.add_mem _ hx hy
      | smul c x _ hx =>
        rw [Subring.smul_def, AlternatingMap.map_update_smul, ← Subring.smul_def]
        exact Submodule.smul_mem _ c hx
    have hk := key (b a) (hb a)
    rwa [Function.update_eq_self] at hk

theorem wedge_of_frame {L : Lat ξ E} {r : ℕ} {e : Fin r → E} {x : Cpt ξ} (h : L.IsFrameAt e x) :
    L.wedge r x = Submodule.span (regAt ξ x) {exteriorPower.ιMulti Ω r e} := by
  obtain ⟨-, hL⟩ := h
  change Submodule.span (regAt ξ x)
    {w | ∃ b : Fin r → E, (∀ i, b i ∈ L x) ∧ w = exteriorPower.ιMulti Ω r b} = _
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w ⟨b, hb, rfl⟩
    rw [hL] at hb
    exact iota_multi_mem_span_of_mem_span b hb
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine Submodule.subset_span ⟨e, fun i => ?_, rfl⟩
    rw [hL]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem ιMulti_ne_zero {r : ℕ} {e : Fin r → E} (h : LinearIndependent Ω e) :
    exteriorPower.ιMulti Ω r e ≠ 0 := by
  apply PositivityTheory.Xgn.ComponentDegreeAlt.wedge_ne_zero <;> assumption

end General

section Int

open CptModel

end Int

end GlobalTheory.CompanionTheory.Ar.Flat.GenModel
