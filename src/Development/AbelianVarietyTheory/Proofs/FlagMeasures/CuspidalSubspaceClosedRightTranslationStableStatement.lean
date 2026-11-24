module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

@[expose] public section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.cuspidalSubspace_closed_rightTranslation_stable : ∀ B : RowsAut, ∃ S : Submodule ℂ (B.I.L2 B.μf B.fund), (∀ F, F ∈ S ↔ B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext F)) ∧ IsClosed (S : Set (B.I.L2 B.μf B.fund)) ∧ (∀ g, ∀ F ∈ S, B.R g F ∈ S) ∧ ∀ (F : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ), (∀ γ ∈ B.I.GFset, ∀ y, f (γ * y) = f y) → Continuous f → f =ᵐ[B.I.muA B.μf] B.I.ext F → (F ∈ S ↔ B.I.IsCuspFn (B.I.muA B.μf) f) := by
  first | exact @GlobalTheory.CuspSubspace.cuspidal_closed_stable | exact GlobalTheory.CuspSubspace.cuspidal_closed_stable | (intros; apply GlobalTheory.CuspSubspace.cuspidal_closed_stable <;> assumption)
