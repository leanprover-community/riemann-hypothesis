module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

noncomputable section

namespace GlobalTheory.LenModAgree

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem lenMod_eq {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (S H : Submodule O M) :
    BlochKatoDuality.lenMod S H = lenModN S H := by
  unfold BlochKatoDuality.lenMod lenModN
  have h := (LinearMap.quotientInfEquivSupQuotient S H).length_eq
  rw [← h]
  have e : Submodule.comap S.subtype S ⊓ Submodule.comap S.subtype H = Submodule.comap S.subtype H := by simp
  exact (Submodule.quotEquivOfEq _ _ e).length_eq

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem main : (∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (A H : Submodule O M), lenModN A H = BlochKatoDuality.lenMod A H) ∧ ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (e : ℕ), LocBoundP i w hw r Xs M e ↔ LocBound i w hw r Xs M e := by
  refine ⟨fun O M _ _ _ A H => (lenMod_eq A H).symm, ?_⟩
  intro D i w hw r Xs k M e
  unfold LocBoundP LocBound
  rw [lenMod_eq]

end GlobalTheory.LenModAgree
