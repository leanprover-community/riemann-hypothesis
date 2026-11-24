module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
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
public import Mathlib.RingTheory.AdicCompletion.RingHom
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

@[expose] public section

namespace PositivityTheory.HtPt.Mi

theorem algHom_of_system : ∀ (R A B : Type) [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Module.Finite R A] (I : Ideal R) [IsAdicComplete I R] (f : ∀ e : ℕ, B →ₐ[R] A ⧸ (I ^ (e + 1)).map (algebraMap R A)), (∀ e (b : B) (a : A), Ideal.Quotient.mk _ a = f (e + 1) b → Ideal.Quotient.mk _ a = f e b) → ∃! g : B →ₐ[R] A, ∀ e b, Ideal.Quotient.mk _ (g b) = f e b := by
  intro R A B _ _ _ _ _ _ _ I _ f hf
  have := GlobalTheory.isAdicComplete_map_of_finite I A
  let J := I.map (algebraMap R A)
  have hJ : ∀ e, (I ^ e).map (algebraMap R A) = J ^ e := fun e => Ideal.map_pow _ _ _
  have ha : StrictMono fun e : ℕ => e + 1 := fun _ _ h => Nat.succ_lt_succ h
  let f' : ∀ e : ℕ, B →+* A ⧸ J ^ (e + 1) := fun e => (Ideal.quotEquivOfEq (hJ (e + 1))).toRingHom.comp (f e).toRingHom
  have key : ∀ e (a : A) (b : B), Ideal.Quotient.mk _ a = f' e b ↔ Ideal.Quotient.mk _ a = f e b := fun e a b => by
    rw [← (Ideal.quotEquivOfEq (hJ (e + 1))).injective.eq_iff, Ideal.quotEquivOfEq_mk]
    rfl
  have hf' : ∀ {m}, (Ideal.Quotient.factorPow J (ha.monotone m.le_succ)).comp (f' (m + 1)) = f' m := fun {m} => by
    ext b
    obtain ⟨a, hb⟩ := Ideal.Quotient.mk_surjective (f' (m + 1) b)
    rw [RingHom.comp_apply, ← hb, ← (key m a b).2 (hf m b a ((key _ a b).1 hb))]
    rfl
  let g := IsAdicComplete.StrictMono.liftRingHom J ha f' hf'
  have hg : ∀ e b, Ideal.Quotient.mk _ (g b) = f' e b := fun e b =>
    IsAdicComplete.StrictMono.mk_liftRingHom J ha f' hf' b
  have ext : ∀ a a' : A, (∀ e, Ideal.Quotient.mk (J ^ (e + 1)) a = Ideal.Quotient.mk (J ^ (e + 1)) a') → a = a' :=
    fun a a' h => congrFun (IsHausdorff.StrictMono.funext' J ha (f := fun _ : Unit => a) (g := fun _ => a')
      fun e _ => h e) ()
  refine ⟨{ g with commutes' := fun r => ext _ _ fun e => ?_ }, fun e b => (key e _ b).1 (hg e b),
    fun g' hg' => AlgHom.ext fun b => ext _ _ fun e => ?_⟩
  · refine (hg e _).trans ((key e _ _).2 ?_).symm
    rw [AlgHom.commutes]; rfl
  · exact ((key e _ b).2 (hg' e b)).trans (hg e b).symm

end PositivityTheory.HtPt.Mi
