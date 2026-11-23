module

public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.RatioOneKilled
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.Reduce
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.DefsForms
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.MainCoind
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_devis

theorem ratioOne_of_killed_l (ℓ : ℕ) [Fact ℓ.Prime] (P : FiniteSubfield → Prop) (h : RatioOneKilled ℓ P) :
    RatioOne ℓ P := by
  intro K S hS hSl hP ιr M _ _ hM
  obtain ⟨r, hr⟩ := hM
  have : Finite S := hS
  induction r generalizing M with
  | zero =>
    have : Subsingleton M := ⟨fun a b => by
      have ha := hr a
      have hb := hr b
      simp only [pow_zero, one_smul] at ha hb
      rw [ha, hb]⟩
    exact gsEulerRatio_eq_one_of_subsingleton S M ιr
  | succ r ih =>
    letI : Module (ULift.{0} ℤ) M := M.hV2
    let T : Module.End (ULift.{0} ℤ) M := (ℓ : Module.End (ULift.{0} ℤ) M)
    have hTx : ∀ x : M, T x = ℓ • x := fun x => Module.End.natCast_apply ℓ x
    have hT : ∀ g, Commute T (M.ρ g) := fun g => Nat.cast_commute ℓ _
    have hD : ∀ g, (⊤ : Submodule _ _) ≤ Submodule.comap (M.ρ g) ⊤ := fun _ => le_top
    have hSE := rangeStepComplex_shortExact T hT ⊤ hD
    have : Finite (Rep.subrepresentation M ⊤ hD) :=
      Finite.of_injective (fun x : Rep.subrepresentation M ⊤ hD => (x.1 : M)) fun _ _ h => Subtype.ext h
    have : Finite (Rep.subrepresentation M _ (inf_ker_le_comap T hT ⊤ hD)) :=
      Finite.of_injective (fun x : Rep.subrepresentation M _ (inf_ker_le_comap T hT ⊤ hD) => (x.1 : M))
        fun _ _ h => Subtype.ext h
    have : Finite (Rep.subrepresentation M _ (map_le_comap T hT ⊤ hD)) :=
      Finite.of_injective (fun x : Rep.subrepresentation M _ (map_le_comap T hT ⊤ hD) => (x.1 : M))
        fun _ _ h => Subtype.ext h
    have hl : ∃ r : ℕ, ∀ m : (rangeStepComplex T hT ⊤ hD).X₂, (ℓ ^ r) • m = 0 :=
      ⟨r + 1, fun m => Subtype.ext (hr m.1)⟩
    have hmul := ratio_shortExact_l ℓ K S hS hSl ιr _ hSE hl
    have h1 : gsEulerRatio S (rangeStepComplex T hT ⊤ hD).X₁ ιr = 1 := by
      refine h K S hS hSl hP ιr _ fun m => Subtype.ext ?_
      have h' : T m.1 = 0 := m.2.2
      rw [hTx] at h'
      exact h'
    have h3 : gsEulerRatio S (rangeStepComplex T hT ⊤ hD).X₃ ιr = 1 := by
      refine ih _ fun m => Subtype.ext ?_
      obtain ⟨x, -, hx⟩ := m.2
      change (ℓ ^ r) • m.1 = 0
      rw [← hx, hTx, smul_smul, ← pow_succ]
      exact hr x
    have htop : gsEulerRatio S M ιr = gsEulerRatio S (rangeStepComplex T hT ⊤ hD).X₂ ιr :=
      (gsEulerRatio_eq_of_iso S (M.subrepresentation ⊤ hD) ιr (subrepresentationTopIso M hD)).symm
    rw [htop, hmul, h1, h3, mul_one]

end PositivityTheory.Lit1.GEN.W_devis
