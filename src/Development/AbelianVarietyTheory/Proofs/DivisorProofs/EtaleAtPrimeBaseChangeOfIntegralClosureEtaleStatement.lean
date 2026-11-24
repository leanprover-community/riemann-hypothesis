module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIffEtaleAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAtPrimeBaseChangeOfIntegralClosureEtale
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct
open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC

theorem _root_.GlobalTheory.T.etale_atPrime_baseChange_of_integralClosureEtale : ∀ (A R R₁ DA : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing R₁]
    [CommRing DA] [Algebra (GenFib A R) DA] (κ : R →+* R₁) (P₁ : Ideal R₁) [P₁.IsPrime],
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A R DA (P₁.comap κ) →
    letI := closureAlg A R DA
    letI : Algebra R (Localization.AtPrime P₁) :=
      ((algebraMap R₁ (Localization.AtPrime P₁)).comp κ).toAlgebra
    Algebra.Etale (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R] closure A R DA) :=
  @GlobalTheory.KeyOriginEnlarge.closureEtaleAt_comap_baseChange_atPrime
