module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapIntegralClosureTensorEq
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing



namespace GlobalTheory

theorem integralClosure_tensor_localization_injective : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    Function.Injective
      (@algebraMap (Localization.AtPrime (Q.under (integralClosure S L))) (Localization.AtPrime Q)
        _ _ (Localization.AtPrime.algebraOfLiesOver (Q.under (integralClosure S L)) Q)) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ _ _ _ _ _ Q _
  set P := Q.under (integralClosure S L) with hP
  letI := Localization.AtPrime.algebraOfLiesOver P Q
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl z
  have h1 : algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)
      (algebraMap (integralClosure S L) (Localization.AtPrime P) x) = 0 := by
    rw [← IsLocalization.mk'_spec (Localization.AtPrime P) x s, map_mul, hz, zero_mul]
  have h2 : algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
      (algebraMap (integralClosure S L) (integralClosure D (TensorProduct S D L)) x) = 0 := by
    rw [← h1]
    exact (Localization.localRingHom_to_map _ _ _ _ x).symm
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl (Localization.AtPrime Q) _).1 h2
  have hx : x = 0 := by
    by_contra hx0
    have hxL : (x : L) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have ht' : ((t : integralClosure D (TensorProduct S D L)) : TensorProduct S D L) *
        ((1 : D) ⊗ₜ[S] (x : L)) = 0 := by
      have := congrArg (fun y : integralClosure D (TensorProduct S D L) => (y : TensorProduct S D L)) ht
      simpa [algebraMap_integralClosure_tensor_eq] using this
    have hu : ((1 : D) ⊗ₜ[S] (x : L)) * ((1 : D) ⊗ₜ[S] ((x : L)⁻¹)) = 1 := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hxL]
      rfl
    have ht0 : ((t : integralClosure D (TensorProduct S D L)) : TensorProduct S D L) = 0 := by
      have := congrArg (· * ((1 : D) ⊗ₜ[S] ((x : L)⁻¹))) ht'
      simpa [mul_assoc, hu] using this
    have : (t : integralClosure D (TensorProduct S D L)) = 0 := Subtype.ext ht0
    exact t.2 (this ▸ Q.zero_mem)
  subst hx
  exact IsLocalization.mk'_zero _

end GlobalTheory
