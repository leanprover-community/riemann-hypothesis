module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsScalarLevelCoverAnalyticFibre
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarOfIntertwinesUpToScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing

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
open CategoryTheory


theorem _root_.GlobalTheory.T.exists_scalar_levelCover_analyticFibre : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (C : Cover T j σ), C.d.IsLev → C.σ₂.comp C.inc = σ → ∀ (y : FrPt (T.Q.Xo j) T.Q.c (CAt σ)) (y₂ : FrPt C.d.Xo₂ C.d.c₂ (CAt C.σ₂)), (y₂.x : Sp ℂ ⟶ C.d.Xo₂.X) ≫ C.d.r = (y.x : Sp ℂ ⟶ (T.Q.Xo j).X) → (∀ τ i, (y₂.u τ i : Sp (DualNumber ℂ) ⟶ C.d.Xo₂.univ.t.G.left) ≫ C.d.m.φ = (y.u τ i : Sp (DualNumber ℂ) ⟶ (T.Q.Xo j).univ.t.G.left)) → ∃ t : ℂ, t ≠ 0 ∧ (∀ (n : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ : Rul C.d.Xo₂ C.d.c₂, C.IsPull f f₂ → toC (evR C.d.Xo₂ C.d.c₂ f₂ y₂) = t ^ n * toC (evR (T.Q.Xo j) T.Q.c f y)) ∧ ∀ (r g : ℕ) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 (T.Q.Dw j)) (x : Frame X.Ψ r) (L : Lt D.host.E r) (mk : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ ϑ : (Fin g → ℂ) → ℂ, (letI : Algebra T.Q.c.F ℂ := σ.toAlgebra; ∃ A : AnFib X bas idx e x L y, A.Marked mk ∧ A.Reads 1 y.s ϑ) → (letI : Algebra C.d.c₂.F ℂ := C.σ₂.toAlgebra; ∃ A₂ : AnFib X bas idx e x L y₂, A₂.Reads 1 y₂.s (fun z => t * ϑ z)) := by
  first | exact @GlobalTheory.CoverFibScalar.exists_scalar_fib | exact GlobalTheory.CoverFibScalar.exists_scalar_fib | (intros; apply GlobalTheory.CoverFibScalar.exists_scalar_fib <;> assumption)
