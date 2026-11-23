module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLocalizationAtPrimeFactorsThroughAwayStatement
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem flat_of_algHom_atPrime (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.Etale R A] [Algebra.Etale R B] (p : Ideal B) [p.IsPrime] (φ : A →ₐ[R] Localization.AtPrime p) :
    φ.toRingHom.Flat := by
  obtain ⟨g, hg, ψ, hψ⟩ := GlobalTheory.T.algHom_localizationAtPrime_factors_through_away R A B p φ
  set h := Localization.awayLift (algebraMap B (Localization.AtPrime p)) g
    (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl)) with hh
  have e : φ.toRingHom = h.comp ψ.toRingHom := by ext a; exact (hψ a).symm
  rw [e]
  refine RingHom.Flat.comp ?_ ?_
  · letI : Algebra A (Localization.Away g) := ψ.toRingHom.toAlgebra
    haveI : IsScalarTower R A (Localization.Away g) :=
      IsScalarTower.of_algebraMap_eq (fun r => (ψ.commutes r).symm)
    haveI : Algebra.Etale A (Localization.Away g) := Algebra.Etale.of_restrictScalars R A _
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · letI : Algebra (Localization.Away g) (Localization.AtPrime p) := h.toAlgebra
    haveI : IsScalarTower B (Localization.Away g) (Localization.AtPrime p) :=
      IsScalarTower.of_algebraMap_eq (fun b => by
        change _ = h _
        simp [hh, Localization.awayLift, IsLocalization.Away.lift])
    have : Module.Flat (Localization.Away g) (Localization.AtPrime p) :=
      (Module.flat_iff_of_isLocalization (Localization.Away g) (Submonoid.powers g)
        (Localization.AtPrime p)).mpr inferInstance
    exact RingHom.flat_algebraMap_iff.mpr this

theorem flat_of_essEtale : ∀ (R L₁ L₂ : Type) [CommRing R] [CommRing L₁] [CommRing L₂] [Algebra R L₁] [Algebra R L₂] [Algebra L₁ L₂] [IsScalarTower R L₁ L₂], (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] L₁)) → (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] L₂)) → Module.Flat L₁ L₂ := by
  intro R L₁ L₂ _ _ _ _ _ _ _ ⟨A, _, _, _, q, _, ⟨e₁⟩⟩ ⟨A', _, _, _, q', _, ⟨e₂⟩⟩
  let φ : A →ₐ[R] Localization.AtPrime q' :=
    (e₂.symm.toAlgHom.comp (IsScalarTower.toAlgHom R L₁ L₂)).comp
      (e₁.toAlgHom.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q)))
  have hφ := flat_of_algHom_atPrime R A A' q' φ
  let f : A →+* L₁ := e₁.toRingHom.comp (algebraMap A (Localization.AtPrime q))
  letI : Algebra A L₁ := f.toAlgebra
  letI : Algebra A L₂ := ((algebraMap L₁ L₂).comp f).toAlgebra
  haveI : IsScalarTower A L₁ L₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e₁' : Localization.AtPrime q ≃ₐ[A] L₁ := { e₁ with commutes' := fun _ => rfl }
  haveI : IsLocalization q.primeCompl L₁ := IsLocalization.isLocalization_of_algEquiv q.primeCompl e₁'
  have hflat : Module.Flat A L₂ := by
    rw [← RingHom.flat_algebraMap_iff]
    have : algebraMap A L₂ = e₂.toRingHom.comp φ.toRingHom := by
      ext a; simp [φ, f, RingHom.algebraMap_toAlgebra]
    rw [this]
    exact RingHom.Flat.comp hφ (RingHom.Flat.of_bijective e₂.bijective)
  exact (Module.flat_iff_of_isLocalization L₁ q.primeCompl L₂).mpr hflat

end GlobalTheory
