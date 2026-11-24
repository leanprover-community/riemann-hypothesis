module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
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

@[expose] public section

noncomputable section

namespace GlobalTheory.InvAlg

theorem factorPow_evalₐ {A : Type} [CommRing A] (I : Ideal A) {k n : ℕ} (hle : k ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I k x := by
  obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective I A x
  simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq]
  have h := x.2 hle
  rw [SModEq.sub_mem] at h
  have hI : (I ^ k • ⊤ : Submodule A A) = I ^ k := by ext; simp
  rw [← neg_sub]
  exact neg_mem (hI ▸ h)

theorem pow_le_comap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {I : Ideal A} {J : Ideal B}
    (h : I.map f ≤ J) (n : ℕ) : I ^ n ≤ (J ^ n).comap f :=
  Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_pow]; exact Ideal.pow_right_mono h n)

def adicCompletionMapToQuotientPow {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) (n : ℕ) : AdicCompletion I A →+* B ⧸ J ^ n :=
  (Ideal.quotientMap (J ^ n) f (pow_le_comap f h n)).comp (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)

theorem factorPow_comp_adicCompletionMapToQuotientPow {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) {k n : ℕ} (hle : k ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (adicCompletionMapToQuotientPow f I J h n) = adicCompletionMapToQuotientPow f I J h k := by
  ext x
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  have hk : AdicCompletion.evalₐ I k x = Ideal.Quotient.mk (I ^ k) r := by
    rw [← factorPow_evalₐ I hle, ← hr]
    rfl
  simp only [adicCompletionMapToQuotientPow, RingHom.comp_apply, RingHom.coe_coe]
  rw [← hr, hk, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
  rfl

def cmap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) : AdicCompletion I A →+* AdicCompletion J B :=
  AdicCompletion.liftRingHom J (adicCompletionMapToQuotientPow f I J h) (factorPow_comp_adicCompletionMapToQuotientPow f I J h)

theorem evalₐ_cmap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) (n : ℕ) (x : AdicCompletion I A) :
    AdicCompletion.evalₐ J n (cmap f I J h x) =
      Ideal.quotientMap (J ^ n) f (pow_le_comap f h n) (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom J _ (factorPow_comp_adicCompletionMapToQuotientPow f I J h) n x

theorem cmap_of {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) (a : A) : cmap f I J h (AdicCompletion.of I A a) = AdicCompletion.of J B (f a) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_cmap, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]

theorem map_algebraMap_le {A B B' : Type} [CommRing A] [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B']
    (g : B →ₐ[A] B') (J : Ideal A) : (J.map (algebraMap A B)).map (g : B →+* B') ≤ J.map (algebraMap A B') := by
  rw [Ideal.map_map, g.comp_algebraMap]

def galAlg {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (σ : GlobalTheory.Mum.Gal (algebraMap R R')) :
    R' →ₐ[R] R' :=
  { σ.1.toRingHom with commutes' := σ.2 }

def galTensor {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (O : Type) [CommRing O] [Algebra R O]
    (σ : GlobalTheory.Mum.Gal (algebraMap R R')) : TensorProduct R O R' →ₐ[O] TensorProduct R O R' :=
  Algebra.TensorProduct.map (AlgHom.id O O) (galAlg σ)

@[simp] theorem galTensor_tmul {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (O : Type) [CommRing O]
    [Algebra R O] (σ : GlobalTheory.Mum.Gal (algebraMap R R')) (x : O) (y : R') :
    galTensor O σ (x ⊗ₜ[R] y) = x ⊗ₜ[R] σ.1 y := rfl

end GlobalTheory.InvAlg
