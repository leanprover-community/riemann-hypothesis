module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSpanThetaSeriesOfBoundedHolomorphic
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_span_thetaSeries_of_boundedHolomorphic : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → 4 * (Module.finrank ℚ D.host.E * T.rank) + 4 ≤ S.rank → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → HolUpTo C B (ThFr.wtOf C.X C.hr c c' S.rank) z φ → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → φ ∈ Submodule.span ℂ (thetaSet C om B (C.uVec Lv hn f') c c') := by
  first | exact @GlobalTheory.AdSpan.mem_span_thetaSet_of_holUpTo | exact GlobalTheory.AdSpan.mem_span_thetaSet_of_holUpTo | (intros; apply GlobalTheory.AdSpan.mem_span_thetaSet_of_holUpTo <;> assumption)
