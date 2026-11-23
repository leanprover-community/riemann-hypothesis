module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.ResidueChar

@[reducible] def unitsDivC : DivisibleBy (Additive ℂˣ) ℤ where
  div a n := if n = 0 then 0 else
    Additive.ofMul (Units.mk0 (Complex.exp (Complex.log ((Additive.toMul a : ℂˣ) : ℂ) / n)) (Complex.exp_ne_zero _))
  div_zero a := if_pos rfl
  div_cancel {n} a hn := by
    rw [if_neg hn]
    apply Additive.toMul.injective
    rw [toMul_zsmul, toMul_ofMul]
    ext
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← Complex.exp_int_mul,
      mul_div_cancel₀ _ (Int.cast_ne_zero.mpr hn), Complex.exp_log (Units.ne_zero _)]

def charUnitC {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (x : A) : ℂˣ :=
  ⟨ψ x, ψ (-x), by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one],
    by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]⟩

theorem addChar_extend_subring {K : Type} [Ring K] (S : Subring K) (ψ : AddChar S ℂ) :
    ∃ ψ₀ : AddChar K ℂ, ∀ x : S, ψ₀ x = ψ x := by
  let _ := unitsDivC
  let g : S →ₗ[ℤ] Additive ℂˣ := AddMonoidHom.toIntLinearMap
    { toFun := fun x => Additive.ofMul (charUnitC ψ x)
      map_zero' := by
        apply Additive.toMul.injective
        ext
        simp [charUnitC, AddChar.map_zero_eq_one]
      map_add' := fun x y => by
        apply Additive.toMul.injective
        ext
        simp [charUnitC, AddChar.map_add_eq_mul] }
  let f : S →ₗ[ℤ] K := (S.subtype : S →+* K).toAddMonoidHom.toIntLinearMap
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property f Subtype.val_injective g
  refine ⟨{ toFun := fun x => ((Additive.toMul (h x) : ℂˣ) : ℂ)
            map_zero_eq_one' := by simp
            map_add_eq_mul' := fun x y => by simp [map_add (f := _)] }, fun x => ?_⟩
  have e := congrArg (fun φ => ((Additive.toMul (φ x) : ℂˣ) : ℂ)) hh
  simpa [f, g, charUnitC] using e

theorem red_eq_zero_of_lt_one {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime]
    (red : v.adicCompletionIntegers K →+* ZMod p) (y : v.adicCompletionIntegers K)
    (hy : Valued.v (y : v.adicCompletion K) < 1) : red y = 0 := by
  by_contra h
  set n : ℕ := (-(red y)⁻¹ : ZMod p).val with hn
  have hnc : ((n : ℕ) : ZMod p) = -(red y)⁻¹ := ZMod.natCast_zmod_val _
  set z : v.adicCompletionIntegers K := 1 + y * (n : v.adicCompletionIntegers K) with hz
  have hred : red z = 0 := by
    rw [hz, map_add (f := _), map_one, map_mul, map_natCast, hnc, mul_neg, mul_inv_cancel₀ h, add_neg_cancel]
  have hlt : Valued.v ((y * (n : v.adicCompletionIntegers K) : v.adicCompletionIntegers K) : v.adicCompletion K) < 1 := by
    have hn1 : Valued.v (((n : v.adicCompletionIntegers K)) : v.adicCompletion K) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (n : v.adicCompletionIntegers K).2
    rw [Subring.coe_mul, map_mul]
    calc Valued.v (y : v.adicCompletion K) * Valued.v (((n : v.adicCompletionIntegers K)) : v.adicCompletion K)
        ≤ Valued.v (y : v.adicCompletion K) * 1 := by gcongr
      _ = Valued.v (y : v.adicCompletion K) := mul_one _
      _ < 1 := hy
  have hz1 : Valued.v ((z : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 := by
    rw [hz, Subring.coe_add, Subring.coe_one]
    rw [Valuation.map_add_eq_of_lt_left]
    · exact map_one _
    · rw [map_one]; exact hlt
  have hu : IsUnit z := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).2 hz1
  have hu' : IsUnit (red z) := hu.map red
  rw [hred] at hu'
  exact not_isUnit_zero hu'

theorem exists_addChar_completion_lift_residue : ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime]
    (red : v.adicCompletionIntegers K →+* ZMod p) (ψ' : AddChar (ZMod p) ℂ), ψ' ≠ 1 →
    ∃ ψ₀ : AddChar (v.adicCompletion K) ℂ, (∀ x, Valued.v x < 1 → ψ₀ x = 1) ∧ (∃ x, Valued.v x ≤ 1 ∧ ψ₀ x ≠ 1) ∧
      ∀ y : v.adicCompletionIntegers K, ψ₀ (y : v.adicCompletion K) = ψ' (red y) := by
  intro K _ _ v p _ red ψ' hne
  obtain ⟨ψ₀, h⟩ := addChar_extend_subring (v.adicCompletionIntegers K).toSubring
    (ψ'.compAddMonoidHom red.toAddMonoidHom)
  refine ⟨ψ₀, fun x hx => ?_, ?_, fun x => h x⟩
  · have hx1 : x ∈ v.adicCompletionIntegers K :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx.le
    have e1 := h ⟨x, hx1⟩
    have e2 : red ⟨x, hx1⟩ = 0 := red_eq_zero_of_lt_one v p red ⟨x, hx1⟩ hx
    rw [show ψ₀ x = ψ₀ ((⟨x, hx1⟩ : (v.adicCompletionIntegers K).toSubring) : v.adicCompletion K) from rfl, e1]
    show ψ' (red ⟨x, hx1⟩) = 1
    rw [e2, AddChar.map_zero_eq_one]
  · obtain ⟨y, hy⟩ : ∃ y, ψ' y ≠ 1 := by
      by_contra hc
      push_neg at hc
      apply hne
      ext y
      rw [hc y, AddChar.one_apply]
    have hy' : ((y.val : ℕ) : ZMod p) = y := ZMod.natCast_zmod_val y
    let x : v.adicCompletionIntegers K := (y.val : v.adicCompletionIntegers K)
    refine ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2, ?_⟩
    have e1 := h x
    rw [show ψ₀ (x : v.adicCompletion K) = ψ₀ ((x : (v.adicCompletionIntegers K).toSubring) : v.adicCompletion K) from rfl, e1]
    show ψ' (red x) ≠ 1
    rw [show red x = y by simp only [x, map_natCast, hy']]
    exact hy

end GlobalTheory.ResidueChar

end
