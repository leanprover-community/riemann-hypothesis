module

public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanEigenformsAdelicFormsIffClassPresentation
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.span_eigenforms_adelic_forms_iff_class_presentation : ∀ {G Γ W K G0 : Type} [Group G] [Group Γ] (ι : Γ →* G) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) [Group G0] [Fintype G0] (Q : Subgroup G) (ch : Q →* ℂˣ) (act : Representation K G0 S.Forms) (P : Bridge.ClassPres ι S σ ρ J χ) (Tt : Bridge.ActTie ι P Q ch act), P.ExtBij → ∀ (U : Subgroup G0) (ψ : U →* Kˣ) (Φ : G → W), Φ ∈ Submodule.span ℂ (P.extL '' {f | ∀ u : U, act (u : G0) f = ((ψ u : Kˣ) : K) • f}) ↔ (Φ ∈ Bridge.AdForms ι ρ J χ ∧ ∀ (κ : Q) (hu : Tt.red κ ∈ U) (h : G), Φ (h * κ) = ((ch κ : ℂˣ) : ℂ) • σ ((ψ ⟨_, hu⟩ : Kˣ) : K) • Φ h) := by
  first | exact @GlobalTheory.LiftSpanEig.eigen_span_iff | exact GlobalTheory.LiftSpanEig.eigen_span_iff | (intros; apply GlobalTheory.LiftSpanEig.eigen_span_iff <;> assumption)
