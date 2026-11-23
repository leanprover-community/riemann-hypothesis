module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

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

noncomputable section

namespace GlobalTheory.GaussUnr

open ValuativeRel GlobalTheory.SplitFlip GlobalTheory.GaussNonvanish

theorem gauss_mul_unram : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {v : HeightOneSpectrum (𝓞 F)}
    (ν₀ ξ : (Fv F v)ˣ →* ℂˣ), (∀ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F →
      ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F → ξ x = 1) →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (ν₀ * ξ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀ ∧
      ∃ y : (Fv F v)ˣ, gauss ψ (ν₀ * ξ) = (((ξ y)⁻¹ : ℂˣ) : ℂ) * gauss ψ ν₀ := by
  intro F _ _ ψ v ν₀ ξ hξ
  have hϖ : IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have hunit : ∀ x : (Fv F v)ˣ, valuation (Fv F v) (x : Fv F v) = 1 → ξ x = 1 := fun x hx => by
    apply hξ x
    · exact (val_le_one_iff v _).1 hx.le
    · apply (val_le_one_iff v _).1
      rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  have hce : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (ν₀ * ξ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀ := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp
    congr 1
    ext c
    simp only [Set.mem_setOf_eq, CondLE]
    refine forall₂_congr fun x hx => ?_
    rw [MonoidHom.mul_apply, hunit x hx.1, mul_one]
  refine ⟨hce, ?_⟩
  unfold gauss
  rw [hce]
  generalize GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀ = c
  rcases Nat.eq_zero_or_pos c with h0 | hc1
  · subst h0
    have hsu : ∀ a b : (Res (Fv F v) 0)ˣ, a = b := fun a b =>
      Units.ext ((Ideal.Quotient.subsingleton_iff.2 (by simp)).elim _ _)
    classical
    rw [Fintype.sum_eq_single 1 (fun y hy => (hy (hsu y 1)).elim), Fintype.sum_eq_single 1 (fun y hy => (hy (hsu y 1)).elim)]
    by_cases h : ((Quotient.out (1 : (Res (Fv F v) 0)ˣ).1 : (ValuativeRel.valuation (Fv F v)).integer) : Fv F v) = 0
    · refine ⟨1, ?_⟩
      rw [dite_eq_left h, dite_eq_left h, mul_zero]
    · refine ⟨Units.mk0 _ h, ?_⟩
      rw [dite_eq_right h, dite_eq_right h, MonoidHom.mul_apply, mul_inv, Units.val_mul, mul_comm (((ν₀ _)⁻¹ : ℂˣ) : ℂ),
        mul_assoc]
  · refine ⟨1, ?_⟩
    rw [map_one, inv_one, Units.val_one, one_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : ((Quotient.out y.1 : (ValuativeRel.valuation (Fv F v)).integer) : Fv F v) = 0
    · rw [dite_eq_left h, dite_eq_left h]
    · rw [dite_eq_right h, dite_eq_right h, MonoidHom.mul_apply, hunit _ (val_rep_unit hϖ hc1 y), mul_one]

end GlobalTheory.GaussUnr
