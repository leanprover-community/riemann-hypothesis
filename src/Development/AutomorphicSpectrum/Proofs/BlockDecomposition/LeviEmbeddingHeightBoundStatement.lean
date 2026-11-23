module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbeddingHeightBound
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

open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix

theorem _root_.GlobalTheory.T.levi_embedding_height_bound : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (c : GL (Fin (r + s)) (Cinf E)), ∃ B : ℝ, 0 ≤ B ∧ ∀ y : GL (Fin r) (Cinf E), height (lev (Cinf E) r s (y, 1) * c) ≤ B * height y := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le | exact GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le | (intros; apply GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le <;> assumption)
