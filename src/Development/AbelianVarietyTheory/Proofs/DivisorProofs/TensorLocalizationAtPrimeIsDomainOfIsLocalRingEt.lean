module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeIsDomainIsIntegrallyClos
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

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_localization_atPrime_isDomain_of_isLocalRing_etale :
    ∀ (P R E : Type) [CommRing P] [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra P R]
      [CommRing E] [Algebra P E] [Algebra.Etale P E] (Q : Ideal E) [Q.IsPrime],
      IsLocalRing (TensorProduct P R (Localization.AtPrime Q)) →
        IsDomain (TensorProduct P R (Localization.AtPrime Q)) := by
  intro P R E _ _ _ _ _ _ _ _ Q _ hloc
  letI : Algebra (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q) :=
    (Algebra.TensorProduct.map (AlgHom.id P R)
      (IsScalarTower.toAlgHom P E (Localization.AtPrime Q))).toAlgebra
  haveI : IsScalarTower R (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q) :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  haveI hl := IsLocalization.tensorProduct_tensorProduct_right P R Q.primeCompl
    (Localization.AtPrime Q) (by ext; simp [RingHom.algebraMap_toAlgebra])
  let 𝔭 : Ideal (R ⊗[P] E) :=
    (maximalIdeal (R ⊗[P] Localization.AtPrime Q)).comap
      (algebraMap (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q))
  haveI : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  have hle : Q.primeCompl.map (Algebra.TensorProduct.includeRight (R := P) (A := R)) ≤
      𝔭.primeCompl := by
    intro x hx
    have hu := IsLocalization.map_units (R ⊗[P] Localization.AtPrime Q)
      (⟨x, hx⟩ : Q.primeCompl.map (Algebra.TensorProduct.includeRight (R := P) (A := R)))
    intro h
    exact ((mem_maximalIdeal _).mp (Ideal.mem_comap.mp h)) hu
  haveI : IsLocalization 𝔭.primeCompl (R ⊗[P] Localization.AtPrime Q) :=
    IsLocalization.of_le _ _ hle (fun r hr => by
      by_contra hu
      exact hr (Ideal.mem_comap.mpr ((mem_maximalIdeal _).mpr hu)))
  obtain ⟨hd, -⟩ := etale_localization_atPrime_isDomain_isIntegrallyClosed R (R ⊗[P] E) 𝔭
  let e : Localization.AtPrime 𝔭 ≃ₐ[R ⊗[P] E] (R ⊗[P] Localization.AtPrime Q) :=
    IsLocalization.algEquiv 𝔭.primeCompl _ _
  exact e.symm.injective.isDomain _

end GlobalTheory
