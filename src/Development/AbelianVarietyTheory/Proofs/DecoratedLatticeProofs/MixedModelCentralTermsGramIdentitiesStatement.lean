module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelCentralTermsGramIdentities
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.mixed_model_central_terms_gram_identities : ∀ D : D7, (∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), (∀ x : Mx D T.rank ρ, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T (d.extX T x) ⬝ x = d.jY ⬝ (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D)) ∧ ∀ (c : skewA D ρ) (x : Mx D T.rank ρ), d.qS T c x = -(algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D) ⬝ c.1).trace)) ∧ ∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (c : skewA D ρ) (y : Mx D S.rank ρ), d.qT S c y = -(algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) ((incA D D.host.xi0⁻¹ • (adj y ⬝ (gA S ⬝ y))) ⬝ c.1).trace) := by
  first | exact @GlobalTheory.CentralGram.central_gram | exact GlobalTheory.CentralGram.central_gram | (intros; apply GlobalTheory.CentralGram.central_gram <;> assumption)
