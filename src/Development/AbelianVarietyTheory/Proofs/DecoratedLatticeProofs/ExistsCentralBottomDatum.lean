module

public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulVecSingleAt
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.QuotientMetricDivisors.Statement

@[expose] public section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem GlobalTheory.MiTop.levChi_mul_lev {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {k k' : GA D V}
    (hk : k ∈ Lev.levG V β L) (hk' : k' ∈ Lev.levG V β L) :
    Lev.levChi V β L (k * k') = Lev.levChi V β L k * Lev.levChi V β L k' := by
  unfold Lev.levChi
  rw [map_mul, ← Units.val_mul]
  exact congrArg _ ((Formalism.L2.DIV.levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩)

theorem GlobalTheory.MiTop.conj_in_level {G : Type} [Group G] (J : Subgroup G) (χ : G → ℂ)
    (hm : ∀ a ∈ J, ∀ b ∈ J, χ (a * b) = χ a * χ b) (h0 : ∀ a, χ a ≠ 0) {k : G} (hk : k ∈ J) (j : G) :
    (j ∈ J ↔ k * j * k⁻¹ ∈ J) ∧ (j ∈ J → χ (k * j * k⁻¹) = χ j) := by
  refine ⟨⟨fun hj => J.mul_mem (J.mul_mem hk hj) (J.inv_mem hk), fun hj => ?_⟩, fun hj => ?_⟩
  · have := J.mul_mem (J.mul_mem (J.inv_mem hk) hj) hk
    rwa [show k⁻¹ * (k * j * k⁻¹) * k = j by group] at this
  · have e := hm _ (J.mul_mem (J.mul_mem hk hj) (J.inv_mem hk)) _ hk
    rw [show k * j * k⁻¹ * k = k * j by group, hm _ hk _ hj, mul_comm (χ k)] at e
    exact (mul_right_cancel₀ (h0 k) e).symm
