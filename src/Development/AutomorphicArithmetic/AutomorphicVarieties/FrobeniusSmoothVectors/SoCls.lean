module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem so_cls {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime] (s : G ℚ Ω) :
    Chr.cls ℚ Ω (l ^ 1) s = cycMod ℚ Ω l 1 s := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  refine (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.1 s _ (fun ζ hζ => ?_)
  exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ hζ

theorem UpperTheory.V.Fr.sc_om :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l], Af.KillsMu l (omO Ω l O) ∧ ∀ σ : G ℚ Ω, IsCC σ → omO Ω l O σ = -1 := by
  intro Ω _ _ _ l _ O _ _ _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact (Fact.out : l.Prime).one_lt⟩
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 : cycMod ℚ Ω l 1 s = 1 := by
      rw [← so_cls]
      refine (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.1 s 1 (fun ζ hζ => ?_)
      rw [pow_one] at hζ
      rw [hs ζ hζ, Units.val_one, ZMod.val_one, pow_one]
    simp only [omO, GC.cycF, MonoidHom.comp_apply, h1, map_one]
  · have h1 : cycMod ℚ Ω l 1 σ = -1 := by
      rw [← so_cls]
      exact (Chr.clsFacts ℚ Ω (l ^ 1)).2.2.2.1 σ hσ
    simp only [omO, GC.cycF, MonoidHom.comp_apply, h1]
    ext
    simp
