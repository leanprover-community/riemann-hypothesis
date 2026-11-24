module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
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

open NumberField IsDedekindDomain UpperTheory.V.Kum

namespace UpperTheory.V.Stick

section Act

variable (K : Type) [Field K] [NumberField K]

theorem clMap_refl (c : ClassGroup (𝓞 K)) : clMap (RingEquiv.refl K) c = c := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [class_map_mk0]
  congr 1
  exact Subtype.ext (Ideal.map_id I.1)

theorem clMap_trans {K K' K'' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K'']
    (τ : K ≃+* K') (τ' : K' ≃+* K'') (c : ClassGroup (𝓞 K)) : clMap (τ.trans τ') c = clMap τ' (clMap τ c) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [class_map_mk0, class_map_mk0, class_map_mk0]
  congr 1
  exact Subtype.ext (Ideal.map_map (I := I.1) (RingOfIntegers.mapRingEquiv τ).toRingHom
    (RingOfIntegers.mapRingEquiv τ').toRingHom).symm

def clRep : Representation ℤ Gal(K/ℚ) (Additive (ClassGroup (𝓞 K))) where
  toFun σ := (MonoidHom.toAdditive (clMap σ.toRingEquiv)).toIntLinearMap
  map_one' := LinearMap.ext fun c => congrArg Additive.ofMul (clMap_refl K c.toMul)
  map_mul' σ τ := LinearMap.ext fun c => congrArg Additive.ofMul (clMap_trans τ.toRingEquiv σ.toRingEquiv c.toMul)

theorem clRep_apply (σ : Gal(K/ℚ)) (c : ClassGroup (𝓞 K)) :
    clRep K σ (Additive.ofMul c) = Additive.ofMul (clMap σ.toRingEquiv c) := rfl

end Act

variable (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K]

def sg : (ZMod M)ˣ ≃* Gal(K/ℚ) := (IsCyclotomicExtension.Rat.galEquivZMod M K).symm

theorem sg_apply (b : (ZMod M)ˣ) {x : K} (hx : x ^ M = 1) : sg M K b x = x ^ (b : ZMod M).val := by
  rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq M K _ hx, sg, MulEquiv.apply_symm_apply]

def sgO (b : (ZMod M)ˣ) : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv (sg M K b).toRingEquiv

theorem sgO_apply (b : (ZMod M)ˣ) {x : 𝓞 K} (hx : x ^ M = 1) : sgO M K b x = x ^ (b : ZMod M).val := by
  apply Subtype.ext
  exact sg_apply M K b (x := x.1) (congrArg Subtype.val hx)

def conjI (P : Ideal (𝓞 K)) (b : (ZMod M)ˣ) : Ideal (𝓞 K) := P.comap (sgO M K b)

theorem mem_conjI (P : Ideal (𝓞 K)) (b : (ZMod M)ˣ) (x : 𝓞 K) : x ∈ conjI M K P b ↔ sgO M K b x ∈ P := Iff.rfl

theorem idMap_inv (I : nonZeroDivisors (Ideal (𝓞 K))) (b : (ZMod M)ˣ) :
    (idMap (sg M K b)⁻¹.toRingEquiv I).1 = conjI M K I.1 b :=
  Ideal.map_symm (sgO M K b)


omit [NeZero M] in
def carry (a b : ZMod M) : ℕ := if M ≤ a.val + b.val then 1 else 0

end UpperTheory.V.Stick

end
