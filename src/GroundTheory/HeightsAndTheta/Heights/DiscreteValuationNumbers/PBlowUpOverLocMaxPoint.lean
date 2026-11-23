module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocMaxPointCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocMaxCut
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem prime_eq_of_isLocalization_atPrime' {F : Type*} [Field F] {B R : Subring F} (h : B ≤ R)
    (𝔭₁ 𝔭₂ : Ideal B) [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (hl₁ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₁)
    (hl₂ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₂) : 𝔭₁ = 𝔭₂ := by
  let _ := (Subring.inclusion h).toAlgebra
  have := hl₁
  have := hl₂
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R 𝔭₁
  rw [← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₁ inferInstance,
    ← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₂ inferInstance]

theorem BlowUpOverLocMaxPoint.proof (h₁ : BlowUpOverLocMaxCentre.Statement.{u})
    (h₂ : BlowUpOverLocFibreMinimal.Statement.{u}) (h₃ : BlowUpOverLocPointDeg.Statement.{u}) :
    BlowUpOverLocMaxPoint.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have := hP.multiProj.isPrime
  intro 𝔫 h𝔫
  obtain ⟨W', hW'p, hW'h, hW'r, hW'le, hW'c, h, hl⟩ :=
    h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel 𝔫 h𝔫
  have hmin := h₂ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel W' hW'p hW'h hW'r hW'le hW'c
  obtain ⟨h', 𝔫', h𝔫', hl', hdeg⟩ :=
    h₃ O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel W' hmin hW'r hW'c
  have := h𝔫.isPrime
  have := h𝔫'.isPrime
  have heq : 𝔫 = 𝔫' := prime_eq_of_isLocalization_atPrime' h 𝔫 𝔫' hl hl'
  subst heq
  exact ⟨W', ⟨hmin, hW'r, hW'c⟩, ⟨h, hl⟩, hdeg⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
