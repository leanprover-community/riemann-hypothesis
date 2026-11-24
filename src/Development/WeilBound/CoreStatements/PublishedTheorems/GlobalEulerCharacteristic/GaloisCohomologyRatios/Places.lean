module

public import GroundTheory.GlobalFields.HerbrandQuotients.SUnitsPerm
public import GroundTheory.GlobalFields.IdeleClassGroup.InvariantsGalois
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.AdditiveDefs
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.MaxUnramifiedOutside
public import Mathlib.GroupTheory.Nilpotent
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.StabilizersFinite
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

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]

theorem placesOver_stable : ∀ (τ : L.1 ≃ₐ[K.1] L.1), ∀ w ∈ (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))),
    τ • w ∈ (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) :=
  fun τ _ hw => galSmul_mem_placesOver (S := S) τ hw

noncomputable def dPlaces [Finite S] (d : AdditiveFunction.{0} ℓ (L.1 ≃ₐ[K.1] L.1)) : ℤ :=
  letI := stableMulAction (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) (placesOver_stable (S := S) (K := K) (L := L))
  haveI : Finite (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) := finite_placesOver (L := L.1) (S := S)
  d.toFun (↥(placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) → ZMod ℓ)
    (funPermRep (ZMod ℓ) (L.1 ≃ₐ[K.1] L.1) (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))))

noncomputable def dInf (d : AdditiveFunction.{0} ℓ (L.1 ≃ₐ[K.1] L.1)) : ℤ :=
  d.toFun (InfinitePlace L.1 → ZMod ℓ) (funPermRep (ZMod ℓ) (L.1 ≃ₐ[K.1] L.1) (InfinitePlace L.1))

end PositivityTheory.Lit1.GEN.X
