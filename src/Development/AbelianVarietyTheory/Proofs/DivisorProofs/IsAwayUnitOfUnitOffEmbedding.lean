module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

theorem GlobalTheory.Square.isAwayUnit_of_unitOff_embedding : ∀ {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (x : K) (q m : ℕ), 0 < q → q ∣ m →
    GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff q (σ x) → GlobalTheory.Square.IsAwayUnit m x := by
  intro K _ _ σ x q m hq hqm h
  obtain ⟨hx0, n, h1, h2⟩ := h
  have hx : x ≠ 0 := fun h0 => hx0 (by rw [h0, map_zero])
  have hinj : Function.Injective σ.toIntAlgHom := σ.injective
  have i1 : (q : K) ^ n * x ∈ integralClosure ℤ K := by
    rw [mem_integralClosure_iff, ← isIntegral_algHom_iff σ.toIntAlgHom hinj]
    simpa using h1
  have i2 : (q : K) ^ n * x⁻¹ ∈ integralClosure ℤ K := by
    rw [mem_integralClosure_iff, ← isIntegral_algHom_iff σ.toIntAlgHom hinj]
    simpa using h2
  set a : 𝓞 K := ⟨_, i1⟩ with ha_def
  set b : 𝓞 K := ⟨_, i2⟩ with hb_def
  have ha : algebraMap (𝓞 K) K a = (q : K) ^ n * x := rfl
  have hb : algebraMap (𝓞 K) K b = (q : K) ^ n * x⁻¹ := rfl
  obtain ⟨d, rfl⟩ := hqm
  refine GlobalTheory.Square.AwayClosure.of_integral (k := n) (l := n) (a := a * (d : 𝓞 K) ^ n)
    (b := b * (d : 𝓞 K) ^ n) hx ?_ ?_
  · rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_natCast, ha]
    push_cast
    ring
  · rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_natCast, hb]
    push_cast
    ring
