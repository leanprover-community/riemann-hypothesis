module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

namespace Frame

section Of

variable {A' : Type} [AddCommGroup A'] (e : ℕ) {n : ℕ} (ε : Idx n ≃ A') (h' : A' →+ Additive (HGrp e))
  (hs : Function.Surjective h') (a' : A') (hk : ∀ k : ℤ, h' (k • a') = 0 → k • a' = 0)

def ofEquiv : Frame :=
  letI : AddCommGroup (Idx n) := ε.addCommGroup
  { e := e
    ord := n
    grp := ε.addCommGroup
    h0 := h'.comp ε.addEquiv.toAddMonoidHom
    projection_surjective_field := hs.comp ε.surjective
    gen0 := ε.symm a'
    zsmul_generator_eq_zero_of_projection := fun k hk0 => by
      have h1 : ε.addEquiv (k • ε.symm a') = k • a' := by
        rw [map_zsmul]
        exact congrArg (fun x => k • x) (ε.apply_symm_apply a')
      apply ε.addEquiv.injective
      rw [h1, map_zero]
      apply hk
      rw [← h1]
      exact hk0 }

def ofEquivIso : (ofEquiv e ε h' hs a' hk).A ≃+ A' :=
  letI : AddCommGroup (Idx n) := ε.addCommGroup
  ε.addEquiv

theorem ofEquiv_generator : ofEquivIso e ε h' hs a' hk (ofEquiv e ε h' hs a' hk).a0 = a' :=
  ε.apply_symm_apply a'

theorem ofEquiv_order : (ofEquiv e ε h' hs a' hk).n0 = addOrderOf a' := by
  show addOrderOf (ofEquiv e ε h' hs a' hk).a0 = _
  conv_rhs => rw [← ofEquiv_generator e ε h' hs a' hk]
  exact (addOrderOf_injective (ofEquivIso e ε h' hs a' hk).toAddMonoidHom
    (ofEquivIso e ε h' hs a' hk).injective _).symm

variable [Fintype A']

def ofGroup : Frame := ofEquiv e (n := Fintype.card A') (Fintype.equivFin A').symm h' hs a' hk

def ofGroupIso : (ofGroup e h' hs a' hk).A ≃+ A' :=
  ofEquivIso e (n := Fintype.card A') (Fintype.equivFin A').symm h' hs a' hk

theorem ofGroup_ord : (ofGroup e h' hs a' hk).ord = Fintype.card A' := rfl

theorem ofGroup_generator : ofGroupIso e h' hs a' hk (ofGroup e h' hs a' hk).a0 = a' :=
  ofEquiv_generator e (n := Fintype.card A') (Fintype.equivFin A').symm h' hs a' hk

theorem ofGroup_order : (ofGroup e h' hs a' hk).n0 = addOrderOf a' :=
  ofEquiv_order e (n := Fintype.card A') (Fintype.equivFin A').symm h' hs a' hk

end Of

end Frame

def cycIso (e : ℕ) : Multiplicative (ZMod (2 ^ e)) ≃* HGrp e :=
  Classical.choose (hostGroup e).2.2.2.2.2.2.2.2

def cycHom (e : ℕ) : ZMod (2 ^ e) →+ Additive (HGrp e) :=
  AddMonoidHom.mk' (fun i => Additive.ofMul (cycIso e (Multiplicative.ofAdd i))) (fun i j => by
    rw [ofAdd_add, map_mul, ofMul_mul])

theorem cycHom_bijective (e : ℕ) : Function.Bijective (cycHom e) := by
  show Function.Bijective (fun i => Additive.ofMul (cycIso e (Multiplicative.ofAdd i)))
  exact Additive.ofMul.bijective.comp ((cycIso e).bijective.comp Multiplicative.ofAdd.bijective)

def idxZMod (n : ℕ) [NeZero n] : Idx n ≃ ZMod n := (ZMod.finEquiv n).toEquiv

theorem cycHom_ker (e : ℕ) (a' : ZMod (2 ^ e)) (k : ℤ) (hk : cycHom e (k • a') = 0) : k • a' = 0 :=
  (cycHom_bijective e).1 (by rw [hk, map_zero])

def frameCyc (e : ℕ) (a' : ZMod (2 ^ e)) : Frame :=
  Frame.ofEquiv e (idxZMod (2 ^ e)) (cycHom e) (cycHom_bijective e).2 a' (cycHom_ker e a')

def frameCycIso (e : ℕ) (a' : ZMod (2 ^ e)) : (frameCyc e a').A ≃+ ZMod (2 ^ e) :=
  Frame.ofEquivIso e (idxZMod (2 ^ e)) (cycHom e) (cycHom_bijective e).2 a' (cycHom_ker e a')

section Cyc

variable (e : ℕ) (a' : ZMod (2 ^ e))

theorem frameCyc_h_injective : Function.Injective (frameCyc e a').h := by
  intro x y hxy
  have h1 : ∀ t, (frameCyc e a').h t = cycHom e (frameCycIso e a' t) := fun t => rfl
  rw [h1, h1] at hxy
  exact (frameCycIso e a').injective ((cycHom_bijective e).1 hxy)

theorem frameCyclic_order : (frameCyc e a').n0 = addOrderOf a' :=
  Frame.ofEquiv_order e (idxZMod (2 ^ e)) (cycHom e) (cycHom_bijective e).2 a' (cycHom_ker e a')

end Cyc

def cyclicFrame (e : ℕ) : Frame := frameCyc e 1

end Formalism.HC

end
