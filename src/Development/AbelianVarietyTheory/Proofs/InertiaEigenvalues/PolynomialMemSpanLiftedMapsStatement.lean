module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialMemSpanLiftedMaps
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.polynomial_mem_span_lifted_maps : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∀ (P : PolF D (Wc D i).rank (Vc D i).rank), ∃ Q ∈ Submodule.span ℂ {Q : PolF D (Wc D i).rank (Vc D i).rank | ∃ (φ : (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (w : (R.cV i).W), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) ∧ Q = φ w}, ∃ E : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank), FiniteDimensional ℂ E ∧ (∀ u ∈ GinfC (Vc D i), ∀ P₁ ∈ E, ∀ P₂ : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P₂ = R.ωP i t (u, 1) (R.ptP i t P₁) → P₂ ∈ E) ∧ (∀ φ : PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ, (∀ u ∈ GinfC (Vc D i), ∀ P₁ ∈ E, ∀ P₂ : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P₂ = R.ωP i t (u, 1) (R.ptP i t P₁) → ∀ l, φ P₂ l = φ P₁ (l ∘ₗ (R.cV i).ρ u)) → ∀ P₁ ∈ E, φ P₁ = 0) ∧ P - Q ∈ E := by
  first | exact @GlobalTheory.FockIsotypic.decomp | exact GlobalTheory.FockIsotypic.decomp | (intros; apply GlobalTheory.FockIsotypic.decomp <;> assumption)
