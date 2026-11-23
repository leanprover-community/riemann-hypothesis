module

public import Development.EtaleCohomology.EtaleSheaves.LeafExtendCut
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineSpaceSmoothNormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimSmoothSurjectiveTotal
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafStalkValuationPf

theorem valuationRing_of_dimLE (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    [IsIntegrallyClosed R] (hd : ringKrullDim R ≤ 1) : ValuationRing R := by
  have h1 : Ring.KrullDimLE 1 R := (Ring.krullDimLE_iff).2 (by exact_mod_cast hd)
  have key : ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal R := by
    intro P hP hPp
    rcases (Ring.krullDimLE_one_iff.mp h1) P hPp with hmin | hmax
    · exfalso; apply hP
      have hb : (⊥ : Ideal R).IsPrime := Ideal.isPrime_bot
      exact le_antisymm (hmin.2 ⟨hb, bot_le⟩ bot_le) bot_le
    · exact IsLocalRing.eq_maximalIdeal hmax
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (R := R)).out 4 2).mp
    (⟨inferInstance, key⟩ : IsIntegrallyClosed R ∧ ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal R)

theorem stalk_facts (Ω : Type) [Field Ω] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp Ω)
    (hc : IsCurve c) (y : C) :
    IsNoetherianRing (C.presheaf.stalk y) ∧ IsIntegrallyClosed (C.presheaf.stalk y) ∧
      ringKrullDim (C.presheaf.stalk y) ≤ 1 := by
  obtain ⟨-, hp, hs⟩ := hc
  have : Smooth c := SmoothOfRelativeDimension.smooth (n := 1) c
  have : LocallyOfFiniteType c := inferInstance
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian c
  refine ⟨inferInstance, ?_, ?_⟩
  · have := GlobalTheory.isIntegrallyClosed_stalk_spec_field Ω (c y)
    exact (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_of_smooth c y).2
  · exact_mod_cast GlobalTheory.SmoothDimTotal.ringKrullDim_stalk_le_of_smooth Ω C c 1 hs y

theorem LeafStalkValuation_of : LateralTheory.E.LeafExtendCut.LeafStalkValuation := by
  intro Ω _ C _ c x y hx hc _
  obtain ⟨h1, h2, h3⟩ := stalk_facts Ω c hc y
  refine ⟨valuationRing_of_dimLE _ h3, ?_⟩
  obtain rfl : x = genericPoint C := hx.eq (genericPoint_spec C)
  exact (inferInstance : IsFractionRing (C.presheaf.stalk y) C.functionField)

end LateralTheory.E.LeafStalkValuationPf
