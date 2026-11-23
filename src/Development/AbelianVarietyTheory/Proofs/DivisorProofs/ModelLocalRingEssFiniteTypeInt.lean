module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc

namespace GlobalTheory.Izumi

theorem essFiniteType_int_O : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω)
    (x : M.Z), Algebra.EssFiniteType ℤ (M.O x) := by
  intro o Ω _ _ _ hA M x
  haveI : LocallyOfFiniteType M.s := M.lft
  let y : PrimeSpectrum o := M.s x
  letI A : Algebra o ((Sp o).presheaf.stalk (M.s x)) := StructureSheaf.stalkAlgebra _ y
  haveI : @IsLocalization.AtPrime o _ ((Sp o).presheaf.stalk (M.s x)) _ A y.asIdeal _ :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := @algebraMap o ((Sp o).presheaf.stalk (M.s x)) _ _ A
  have h₁ : (M.s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap M.s x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  haveI : Algebra.FiniteType ℤ o := hA.ft
  have h₀ : (algebraMap ℤ o).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h₃ : (M.stalkEquiv x).toRingHom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _ (M.stalkEquiv x).surjective).essFiniteType
  have h := ((h₀.comp h₂).comp h₁)
  have h' := h.comp h₃
  rw [← RingHom.essFiniteType_algebraMap]
  convert h'
  exact RingHom.ext_int _ _

end GlobalTheory.Izumi
