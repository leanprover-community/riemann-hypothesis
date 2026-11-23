module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenComponentSpanRelIndexCriterion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem _root_.GlobalTheory.T.eigenComponent_span_relIndex_criterion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ) (s₀ : 𝓞 E →+* ℂ) (r k : ℕ) (y : Fin r → Λ) (q p : Fin k → Fin g → ℂ), (∀ a, y a ∈ I) → (Submodule.span (𝓞 E) (Set.range y)).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0 → (∀ c, q c ∈ eigSp R.B s₀) → (∀ c, p c - q c ∈ Submodule.span ℂ (R.P '' (I : Set Λ))) → (∀ c, ∀ x ∈ I, R.ip (R.P x) (p c) = 0) → (R.gram (Fin.append (fun a => eigComp R.B s₀ (R.P (y a))) q)).det = (R.gram fun a => eigComp R.B s₀ (R.P (y a))).det * (Matrix.of fun c c' => R.ip (p c) (q c')).det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.IsoSplit.gram_append_split | exact GlobalTheory.CompanionTheory.Ar.Cusp.IsoSplit.gram_append_split | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.IsoSplit.gram_append_split <;> assumption)
