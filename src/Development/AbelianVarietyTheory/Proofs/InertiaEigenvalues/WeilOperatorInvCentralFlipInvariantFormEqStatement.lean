module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilOperatorInvCentralFlipInvariantFormEq
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.weilOperator_inv_centralFlip_invariantForm_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (m : ℕ) (g : GA D V) (x : (AE D)ˣ) (ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ), Formalism.L2.NTheta.IsIdemAt e P → m ≠ 0 → Formalism.L2.Theta.mt V g = flipElt e m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V e m x → (∀ y : WO V W, IsHalf (cA D e) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ) → ∃ r : ℝ, 0 < r ∧ ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ℓ (om (g⁻¹, 1) f) = (r : ℂ) * ((χW x : Circle) : ℂ)⁻¹ * ℓ f := by
  first | exact @GlobalTheory.LevelSeries.FlipScalStep.om_inv_flip_eq | exact GlobalTheory.LevelSeries.FlipScalStep.om_inv_flip_eq | (intros; apply GlobalTheory.LevelSeries.FlipScalStep.om_inv_flip_eq <;> assumption)
