module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EtC.MVLeft

theorem mono_freePresheaf_map (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) [Mono f] : Mono ((freeP R).map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [ModuleCat.mono_iff_injective]
  have hf : Function.Injective (f.app U) := (mono_iff_injective (f.app U)).1 inferInstance
  have hu : Function.Injective (uliftFunctor.{1}.map (f.app U)) := by
    intro a b h; cases a; cases b; exact congrArg ULift.up (hf (congrArg ULift.down h))
  exact Finsupp.mapDomain_injective hu

theorem free_mono (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) [Mono f] : Mono ((free R).map f) := by
  haveI := mono_freePresheaf_map R f
  exact (presheafToSheaf _ _).map_mono ((freeP R).map f)

theorem left_mono : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), Mono (biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))))) := by
  intro R _ A A' _ _ _ f
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))))
  haveI : Mono (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))) :=
    yoneda.map_mono _
  haveI := free_mono R (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))))
  exact mono_of_mono_fac (biprod.lift_snd _ _)

end GlobalTheory.EtC.MVLeft
