module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrespondingLatticesBlockLattice
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

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport


theorem _root_.GlobalTheory.T.correspondingLattices_blockLattice : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type} [DecidableEq D] [DecidableEq D₂], IsLocIso j → ∀ (cD : D₂ ≃ D) {ϖ : kˣ} {ϖ₂ : k'ˣ}, IsUnif ϖ → IsUnif ϖ₂ → ∀ (e : ℕ) (P : Finset D) (P₂ : Finset D₂), (∀ c, c ∈ P₂ ↔ cD c ∈ P) → LatCorr j cD (blockLat ϖ e P) (blockLat ϖ₂ e P₂) := by
  first | exact @GlobalTheory.PureMatch.Transport.latCorr_blockLat | exact GlobalTheory.PureMatch.Transport.latCorr_blockLat | (intros; apply GlobalTheory.PureMatch.Transport.latCorr_blockLat <;> assumption)
