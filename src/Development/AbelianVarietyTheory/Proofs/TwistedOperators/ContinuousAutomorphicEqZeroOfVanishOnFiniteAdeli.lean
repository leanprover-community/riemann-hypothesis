module

public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

namespace EqZeroOfFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.CompanionTheory.FiniteVanish

end GlobalTheory.CompanionTheory.FiniteVanish

end

end EqZeroOfFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
theorem _root_.GlobalTheory.Adopt.continuous_automorphic_eq_zero_of_vanish_on_finiteAdelic : ∀ (D : D7) (V : HSp D) (φ : GA D V → ℂ), (∀ τ, (gramAt D V τ).PosDef) → Continuous φ → (∀ γ ∈ GQ V, ∀ h, φ (γ * h) = φ h) → (∀ h ∈ GfC V, φ h = 0) → ∀ h, φ h = 0 := by
  intro D V φ _ hcont hleft hzero g
  haveI := GlobalTheory.AutFunCounterexample.topGroup_GA D V
  obtain ⟨u, hu, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 g

  set ψ : GA D V → ℂ := fun x => φ (x * f) with hψ
  have hψc : Continuous ψ := hcont.comp (continuous_mul_const f)
  have hvan : ∀ γ ∈ GQ V, ∀ k ∈ GfC V, ψ (γ * k) = 0 := fun γ hγ k hk => by
    simp only [hψ, mul_assoc, hleft γ hγ]
    exact hzero _ ((GfC V).mul_mem hk hf)
  show ψ u = 0
  by_contra hne
  obtain ⟨γ, hγ, k, hk, hin, -⟩ :=
    GlobalTheory.RealApprox.weak_approx_real V u hu {x | ψ x ≠ 0} (isOpen_ne_fun hψc continuous_const) hne
  exact hin (hvan γ hγ k hk)

end
