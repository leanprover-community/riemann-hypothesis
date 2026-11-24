module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalIndexAtSinglePlace
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

@[expose] public section

open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

theorem _root_.GlobalTheory.T.local_index_at_single_place : ∀ (L : Type) [Field L] [NumberField L] (W : Type) [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L) (A B : Submodule (𝓞 L) W), B ≤ A → B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0 → (∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B) → (locAt v B).toAddSubgroup.relIndex (locAt v A).toAddSubgroup = B.toAddSubgroup.relIndex A.toAddSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex.relIndex_locAt | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex.relIndex_locAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex.relIndex_locAt <;> assumption)
