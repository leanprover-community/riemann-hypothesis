module

public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.NormalFixingSubgroupGaloisClosure
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeDefs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.Kummer
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
import Mathlib.Tactic.Basify
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
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.StabilizersDefs

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

local instance oddOrTcBaseScalarTower {K L : FiniteSubfield} [Fact (K ≤ L)] :
    IsScalarTower K.1 L.1 ℚ̄ :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]

theorem odd_or_tc_base_pf
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    (hK : ℓ ≠ 2 ∨ IsTotallyComplex L.1) : Odd ℓ ∨ IsTotallyComplex K.1 := by
  have hℓ : ℓ.Prime := Fact.out
  by_cases h2 : ℓ = 2
  · right
    subst h2
    have hTC : IsTotallyComplex L.1 := hK.resolve_left (by simp)
    have : IsGalois K.1 L.1 := ⟨⟩
    refine ⟨fun v => ?_⟩
    by_contra hv
    rw [InfinitePlace.not_isComplex_iff_isReal] at hv
    obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (k := K.1) (K := L.1) v
    have hw : w.IsComplex := hTC.isComplex w
    have hram : ¬ InfinitePlace.IsUnramified K.1 w :=
      InfinitePlace.not_isUnramified_iff.2 ⟨hw, hv⟩
    have hcard := InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two.1 hram
    have hdvd : 2 ∣ Nat.card (L.1 ≃ₐ[K.1] L.1) :=
      hcard ▸ Subgroup.card_subgroup_dvd_card (MulAction.stabilizer (L.1 ≃ₐ[K.1] L.1) w)
    have hidx : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index =
        Nat.card (L.1 ≃ₐ[K.1] L.1) := by
      rw [Subgroup.index]
      exact Nat.card_congr (gsQuotientGalEquiv hL).toEquiv
    rw [hidx] at hcop
    have := Nat.Coprime.coprime_dvd_left hdvd hcop
    norm_num at this
  · left
    exact hℓ.odd_of_ne_two h2

end PositivityTheory.Lit1.GEN.X
