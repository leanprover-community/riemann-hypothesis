module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSurjectiveSectionOfSHStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCoverStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem heightFunctionalStatement_of_pairingProperties (hA5 : A5)
    (hsect : ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of A)),
      Etale f → Surjective f → ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _) : B2 := by
  intro R _ A _ hA F n hn
  have key : ∀ x : H R (sp A) F n, x = 0 := by
    intro x
    obtain ⟨Y, f, hf, hs, hx⟩ := hA5 R (Spec (CommRingCat.of A)) F n hn x
    obtain ⟨s, hsf⟩ := hsect A hA Y f hf hs
    calc x = pull R (𝟙 (sp A)) F n x := (pull_id R _ F n x).symm
      _ = pull R (sch.map (s ≫ f)) F n x := by rw [hsf, CategoryTheory.Functor.map_id]
      _ = pull R (sch.map s) F n (pull R (sch.map f) F n x) := by
          rw [CategoryTheory.Functor.map_comp, pull_comp]
      _ = 0 := by rw [hx, map_zero]
  exact ⟨fun x y => by rw [key x, key y]⟩

theorem b2 : B2 := heightFunctionalStatement_of_pairingProperties GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover GlobalTheory.T.exists_section_of_etale_surjective_of_SH

end GlobalTheory.EtC
