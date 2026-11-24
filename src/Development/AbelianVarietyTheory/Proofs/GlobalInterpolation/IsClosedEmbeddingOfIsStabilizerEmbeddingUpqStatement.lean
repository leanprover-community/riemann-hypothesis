module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClosedEmbeddingOfIsStabilizerEmbeddingUpq
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele

@[expose] public section

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

theorem _root_.GlobalTheory.T.isClosedEmbedding_of_isStabilizerEmbeddingUpq : ∀ (P Q P' Q' : ℕ), P' + Q' + 1 = P + Q → ∀ (x₀ : Fin P ⊕ Fin Q → ℂ), star x₀ ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x₀ ≠ 0 → ∀ j : UpqT P' Q' →* UpqT P Q, IsStabEmb x₀ j → IsClosedEmbedding j := by
  first | exact @GlobalTheory.StabEmbClosed.isClosedEmbedding_of_isStabEmb | exact GlobalTheory.StabEmbClosed.isClosedEmbedding_of_isStabEmb | (intros; apply GlobalTheory.StabEmbClosed.isClosedEmbedding_of_isStabEmb <;> assumption)
