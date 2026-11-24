module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTransportGroupsCuspFormsWeilDataIsometry
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_transport_groups_cuspForms_weilData_isometry : ∀ (D : D7) (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V), HSpace.IsIsomEmb V V' e.toLinearMap → ∃ κ : GA D V ≃* GA D V', Continuous κ ∧ Continuous κ.symm ∧ (∀ g, κ g ∈ GQ V' ↔ g ∈ GQ V) ∧ (∀ θ : InfF D, IsInfFam θ → ∀ F, IsCuspForm θ V F → IsCuspForm θ V' fun h => F (κ.symm h)) ∧ ∀ (ψ : AddChar (AF D.host.F) ℂ) (S : HSp D) (χ χ' : IdC D) om, IsWeilDatumO ψ S V χ χ' om → ∃ om', IsWeilDatumO ψ S V' χ χ' om' ∧ ∀ f, IsThetaFunO ψ S V f → ∃ f', IsThetaFunO ψ S V' f' ∧ (f ≠ 0 → f' ≠ 0) ∧ ∀ g h, thetaKO om' g (κ h) f' = thetaKO om g h f := by
  first | exact @GlobalTheory.Mem.Isom.exists_isom_transport | exact GlobalTheory.Mem.Isom.exists_isom_transport | (intros; apply GlobalTheory.Mem.Isom.exists_isom_transport <;> assumption)
