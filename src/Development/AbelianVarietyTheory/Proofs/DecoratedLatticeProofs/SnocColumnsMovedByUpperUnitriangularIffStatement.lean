module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsUnitriGlEquiv
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SnocColumnsMovedByUpperUnitriangularIff
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB


theorem _root_.GlobalTheory.T.snocColumns_moved_by_upperUnitriangular_iff : ∀ (R : Type) [CommRing R] (n σ : ℕ) (M : Matrix (Fin n) (Fin σ) R) (w : Fin n → R) (Y : Matrix (Fin n) (Fin n) R), (∃ U ∈ GlobalTheory.UniIndexPrime.uniSub (σ + 1) R, Y * Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) = Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) * (U : Matrix (Fin (σ + 1)) (Fin (σ + 1)) R)) ↔ ∃ u ∈ GlobalTheory.UniIndexPrime.uniSub σ R, ∃ v : Fin σ → R, Y * M = M * (u : Matrix (Fin σ) (Fin σ) R) ∧ Y *ᵥ w = w + M *ᵥ v := by
  first | exact @GlobalTheory.BlockUni.snoc_uni_iff | exact GlobalTheory.BlockUni.snoc_uni_iff | (intros; apply GlobalTheory.BlockUni.snoc_uni_iff <;> assumption)
