module

public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefMapEmbeddingOfPositiveAtPlace
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrmOfPosDef

@[expose] public section

open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.posDef_map_embedding_of_positiveAtPlace : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K), Formalism.L2.Rows.PosAt H v → (H.map v.embedding).PosDef := by
  first | exact @GlobalTheory.AmbTiePosDef.posDef_map_of_posAt | exact GlobalTheory.AmbTiePosDef.posDef_map_of_posAt | (intros; apply GlobalTheory.AmbTiePosDef.posDef_map_of_posAt <;> assumption)
