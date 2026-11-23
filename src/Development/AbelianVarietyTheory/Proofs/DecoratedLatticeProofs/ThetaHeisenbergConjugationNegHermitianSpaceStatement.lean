module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.thetaHeisenberg_conjugation_negHermitianSpace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, (∀ f : WO S T → ℂ, (IsThetaFunO ψ S (GlobalTheory.ChiGrid.negSp T) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) ↔ IsThetaFunO ψ S T f) ∧ (IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) ↔ IsThetaFunO ψ S T f)) ∧ ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ S (GlobalTheory.ChiGrid.negSp T) w (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (heisO ψ S T w f) ∧ heisO ψ (GlobalTheory.ChiGrid.negSp S) T w (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (heisO ψ S T w f) := by
  first | exact @GlobalTheory.CjNeg.theta_heis_neg | exact GlobalTheory.CjNeg.theta_heis_neg | (intros; apply GlobalTheory.CjNeg.theta_heis_neg <;> assumption)
