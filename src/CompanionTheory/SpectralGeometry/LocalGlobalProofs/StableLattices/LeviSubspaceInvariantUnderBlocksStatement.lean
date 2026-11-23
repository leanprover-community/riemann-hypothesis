module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviSubspaceInvariantUnderBlocks
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport

theorem _root_.GlobalTheory.T.levi_subspace_invariant_under_blocks : ∀ {n : ℕ} (P : GMod n) (d : Fin 3 → ℕ) (h : ∑ i, d i = n) (χ : Fin n → ℂ) (L : Fin n → Fin 3) (a b : Fin n), blk (stdBlocks d h) a = blk (stdBlocks d h) b → ∀ x ∈ leviSub P d h χ L, P.E a b x ∈ leviSub P d h χ L := by
  first | exact @GlobalTheory.CompanionTheory.RgTransport.leviSub_stable | exact GlobalTheory.CompanionTheory.RgTransport.leviSub_stable | (intros; apply GlobalTheory.CompanionTheory.RgTransport.leviSub_stable <;> assumption)
