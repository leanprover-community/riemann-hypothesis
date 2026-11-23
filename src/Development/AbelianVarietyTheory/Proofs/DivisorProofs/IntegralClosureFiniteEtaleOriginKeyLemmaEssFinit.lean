module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatAlgHomEtaleHeightOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtaleOfGaloisDescentHartogsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreBaseFlatNoetherianIntClosedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHartogsPropertyHeightOnePrimesOfFlatStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureZmodTorsorGenericFibreDataStatement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem GlobalTheory.GoodEtale.closure_finiteEtale : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (ρ : Localization.AtPrime QA →+* A), ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A →
      RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X} →
    ∀ (q : ℕ), 0 < q → IsUnit (q : A) →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
      GlobalTheory.KeyOriginNoeth.Good A (Localization.AtPrime QA) DA ρ →
      GlobalTheory.KeyOriginNoeth.ClosureFiniteEtale A (Localization.AtPrime QA) DA := by
  intro A _ _ _ _ _ _ EA _ _ _ _ _ QA _ hQA ρ hρ hker q hq hqu DA _ _ actA htor hgood
  haveI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨hflat, hnoeth, ht, hic⟩ := GlobalTheory.T.genericFibreBase_flat_noetherian_intClosed A EA QA hQA ρ hρ hker
  haveI := hflat
  haveI := hnoeth
  have hHR := GlobalTheory.T.hasHartogsPropertyHeightOnePrimes_of_flat A (Localization.AtPrime QA)
  obtain ⟨act', T, hT, ⟨a, ha, n, x, y, hxy⟩, htf, hHC, hint, hnt⟩ :=
    GlobalTheory.T.integralClosure_zmodTorsor_genericFibre_data A (Localization.AtPrime QA) hHR hic q DA actA htor
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A (Localization.AtPrime QA) DA
  obtain ⟨hEt, s, hs⟩ := hgood
  obtain ⟨O, _, _, hO, hσ⟩ := GlobalTheory.T.exists_faithfullyFlat_algHom_etale_height_one A (Localization.AtPrime QA) (GlobalTheory.KeyOriginNoeth.closure A _ DA)
    ρ hρ _ hker ht hint (fun P _ h => hEt P h) ⟨s, hs⟩
  obtain ⟨hfin, het⟩ := GlobalTheory.T.finiteEtale_of_galois_descent_hartogs A (Localization.AtPrime QA) (GlobalTheory.KeyOriginNoeth.closure A _ DA) O
    (Multiplicative (ZMod q)) act' T hT a ha n x y hxy htf hHC (fun P _ h => hEt P h) hσ
  exact ⟨hfin, het, hnt⟩
