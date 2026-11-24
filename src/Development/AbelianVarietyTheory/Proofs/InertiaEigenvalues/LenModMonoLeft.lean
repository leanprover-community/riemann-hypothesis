module

public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition



namespace GlobalTheory

theorem lenMod_mono_left : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S S' H : Submodule O M), S ≤ S' → BlochKatoDuality.lenMod S H ≤ BlochKatoDuality.lenMod S' H := by
  intro O M _ _ _ S S' H hS

  have hle : S ⊔ H ≤ S' ⊔ H := sup_le_sup_right hS H
  let f := Submodule.mapQ (H.comap (S ⊔ H).subtype) (H.comap (S' ⊔ H).subtype)
    (Submodule.inclusion hle) (fun x hx => by simpa using hx)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    simpa using hx
  exact Module.length_le_of_injective f hf

end GlobalTheory
