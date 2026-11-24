module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedCoordinatesOfPrismCover
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.stratifiedCoordinates_of_prismCover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C), Cover h → ∀ (P : Type) [AddCommGroup P] [Module B.A P] (u : P →ₛₗ[h.f] (Fin d → C.A)), (∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → ∀ x, (fun i => p.f (u x i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (u x i)) → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q), ∃ v : P →ₛₗ[a.f] (Fin d → Q.A), ∀ (Q' : Obj l ↥(OL K)) (h' : Hom Q Q') (a' : Hom C Q'), a'.comp h = h'.comp a → ∀ x, (fun i => h'.f (v x i)) = (S.ε (h'.comp g) (a'.comp f)).mulVec fun i => a'.f (u x i) := by
  first | exact @GlobalTheory.BSP.SiteCoord.coords_of_cover | exact GlobalTheory.BSP.SiteCoord.coords_of_cover | (intros; apply GlobalTheory.BSP.SiteCoord.coords_of_cover <;> assumption)
