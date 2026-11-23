module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.CharOfZeta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ApartAllEmpty
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DivisionOfDeterminantCharacter
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.InsideRefl

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.charOfZeta_of :
    CharOfZeta := by
  intro E _ _ _ a U hU ζ hζ hcen hrat hsc
  choose c hc using hsc
  obtain ⟨φ₀, h₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  obtain ⟨g₀, hg₀⟩ : ∃ g, φ₀ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hval : ∀ z, φ₀ (g₀ * ζ z) = c z * φ₀ g₀ := fun z => by
    have := congrFun (hc z φ₀ h₀) g₀
    rwa [GlobalTheory.DefU.RU_apply, Pi.smul_apply, smul_eq_mul] at this
  have hcz : ∀ z, c z = φ₀ (g₀ * ζ z) / φ₀ g₀ := fun z => by
    rw [hval z, mul_div_cancel_right₀ _ hg₀]
  have hcont : Continuous c := by
    have h1 : Continuous fun z => φ₀ (g₀ * ζ z) :=
      (hU.aut φ₀ h₀).cont.comp (continuous_const.mul hζ)
    have h2 : c = fun z => φ₀ (g₀ * ζ z) / φ₀ g₀ := funext hcz
    rw [h2]
    exact h1.div_const _
  have hone : c 1 = 1 := by
    rw [hcz, map_one, mul_one, div_self hg₀]
  have hmul : ∀ z z', c (z * z') = c z * c z' := fun z z' => by
    have h1 : RU E a (ζ (z * z')) φ₀ = (c z * c z') • φ₀ := by
      rw [map_mul, map_mul, Module.End.mul_apply, hc z' φ₀ h₀, map_smul, hc z φ₀ h₀, smul_smul, mul_comm]
    rw [hc _ φ₀ h₀] at h1
    exact smul_left_injective ℂ hne h1
  let f : Ideles E →* ℂ := { toFun := c, map_one' := hone, map_mul' := hmul }
  have hinvc : Continuous fun z => (c z)⁻¹ := by
    refine hcont.inv₀ fun z => ?_
    intro h0
    have := hmul z z⁻¹
    rw [mul_inv_cancel, hone, h0, zero_mul] at this
    exact one_ne_zero this
  refine ⟨⟨f.toHomUnits, ?_, fun k => ?_⟩, fun z φ hφ => ?_⟩
  · refine Units.continuous_iff.2 ⟨hcont, ?_⟩
    have : (fun z => (((f.toHomUnits z)⁻¹ : ℂˣ) : ℂ)) = fun z => (c z)⁻¹ := by
      funext z
      rw [Units.val_inv_eq_inv_val]
      rfl
    exact this ▸ hinvc
  · refine Units.ext ?_
    change c (diagUnits E k) = 1
    rw [hcz, ← hcen, (hU.aut φ₀ h₀).left _ (hrat k), div_self hg₀]
  · exact hc z φ hφ
