module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KernelInverseFibreProductLattices
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

theorem _root_.GlobalTheory.T.kernel_inverse_fibreProduct_lattices : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [TopologicalSpace LL] {k : Type} [Field k] [Algebra O k] (lam : O), algebraMap O LL lam ≠ 0 → algebraMap O k lam = 0 → (∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q → ∃ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), ∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x) ∧ (∀ (T T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), Function.Injective f.f → (∀ x ∈ T.L.T, ∃ y ∈ T'.L.T, f.f y = lam • x) → ∃ h : LatHom T.L T'.L, ∀ x, f.f (h.f x) = algebraMap O LL lam • x) ∧ ∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (T' : LocLat G Qp LL O) (A' : Ob k G) (q' : ↥T'.L.T →ₗ[O] (Fin A'.m → k)) (g : (Fin A.m → k) →ₗ[k] (Fin A'.m → k)), Onto T A q → Onto T' A' q' → IsHom A A' g → ∃ (T'' : LocLat G Qp LL O) (f : LatHom T''.L T.L) (f' : LatHom T''.L T'.L), (∀ x ∈ T.L.T, ∃ z ∈ T''.L.T, f.f z = x) ∧ ∀ z : ↥T''.L.T, q' (GlobalTheory.EtaleExact.latMap f' z) = g (q (GlobalTheory.EtaleExact.latMap f z)) := by
  first | exact @GlobalTheory.RedFun.SubLat.ker_inv_fibre | exact GlobalTheory.RedFun.SubLat.ker_inv_fibre | (intros; apply GlobalTheory.RedFun.SubLat.ker_inv_fibre <;> assumption)
