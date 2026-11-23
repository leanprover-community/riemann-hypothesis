module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExponentsThetaSystemBigOddPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddPrimeIsUnitOfCompleteNormalCharZeroBaseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelAfterFiniteExtensionBaseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemSpreadOfLevelFractionFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTupleThetaConstantRatiosGenerateFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedCoverPullbackSemiAbelianModelStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinNormalProjectiveModelExistsProof
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_uCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))), (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (C : UCover R₁) (a : C.A.A.left ⟶ A.A.left), FinExt ρ ∧ IsFib ρ A C.A a := by
  intro R _ _ _ hR A hA
  obtain ⟨n, hn, hno, hnu⟩ := GlobalTheory.T.exists_odd_prime_isUnit_of_completeNormalCharZeroBase R hR
  obtain ⟨k, j, hk, hj, hbig⟩ := GlobalTheory.T.exists_exponents_thetaSystem_big_odd_prime A.g n hn hno
  have hmu : IsUnit (((n ^ j * (n ^ k) ^ 2) ^ 2 : ℕ) : R) := by
    push_cast; exact ((hnu.pow _).mul ((hnu.pow _).pow _)).pow _
  obtain ⟨R₁, _, _, _, ρ, A₁, a, ζ, lev, hfin, hfib, hg, hS⟩ :=
    GlobalTheory.T.exists_symplecticLevel_after_finiteExtension_base R hR A hA _ (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hn.ne_zero) (pow_ne_zero _ (pow_ne_zero _ hn.ne_zero))))) hmu
  haveI : CharZero R₁ := ⟨fun x y h => by
    have := hR.2
    exact Nat.cast_injective (hfin.2.1 (by simpa using h))⟩
  have hnu₁ : IsUnit (n : R₁) := by simpa using hnu.map ρ
  obtain ⟨o, Ω, _, _, _, _, S, ρS, b, e, φ, hSg, hSN, hSr, hb, hcart, hlb⟩ :=
    GlobalTheory.T.exists_thetaSystem_spread_of_level_fractionField R₁ A₁ hS n k j hn hno hk hj hnu₁ ζ lev
  have hB : S.Big := hbig o Ω S (hSg.trans hg) hSN hSr
  obtain ⟨J₀, _, t₀, ht₀, hfin'⟩ := GlobalTheory.T.exists_tuple_thetaConstant_ratios_generate_field o Ω S
  obtain ⟨M, U₀, EE, hO, -, -, ⟨Z⟩⟩ := GlobalTheory.zhSt_holds o Ω S ρS hB J₀ t₀ ht₀ hfin'
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_uniformised_cover_pullback_semiAbelian_model R₁ o Ω S ρS M U₀ EE hO Z b e hb A₁ φ hcart hlb
  subst hC
  exact ⟨R₁, _, _, _, ρ, C, a, hfin, hfib⟩

end GlobalTheory.Mum
