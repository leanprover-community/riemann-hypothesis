module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory

theorem integral_normSq_coef_ne_zero : ∀ (D : D7) (V : HSp D), V.SigOK → V.IsPosDef → ∀ (c : CoefA V), c.Is → ∀ w : c.W, w ≠ 0 → ∀ mR : Measure (GinfC V), mR.IsHaarMeasure → ∫ b : GinfC V, ‖⟪w, c.ρ (b : GA D V) w⟫_ℂ‖ ^ 2 ∂mR ≠ 0 := by
  intro D V hS hp c hc w hw mR hR
  have : CompactSpace (GinfC V) :=
    isCompact_iff_compactSpace.1 (Formalism.IndefR.Eqv.isCompact_GinfC hS fun τ => Or.inl (hp τ))
  set f : GinfC V → ℝ := fun b => ‖⟪w, c.ρ (b : GA D V) w⟫_ℂ‖ ^ 2 with hfdef
  have hcont : Continuous f := by
    have h1 : Continuous fun b : GinfC V => c.ρ (b : GA D V) w := (hc.2.2.1 w).comp continuous_subtype_val
    exact ((continuous_const.inner h1).norm).pow 2
  have hnn : 0 ≤ f := fun b => by positivity
  have hint : Integrable f mR := hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have h1 : f 1 ≠ 0 := by
    simp only [hfdef, OneMemClass.coe_one, map_one, Module.End.one_apply]
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (inner_self_ne_zero.2 hw))
  have hpos : 0 < ∫ b, f b ∂mR := by
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    exact hcont.isOpen_support.measure_pos mR ⟨1, h1⟩
  exact hpos.ne'

end GlobalTheory
