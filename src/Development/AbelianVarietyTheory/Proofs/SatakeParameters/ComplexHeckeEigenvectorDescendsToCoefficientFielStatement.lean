module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexHeckeEigenvectorDescendsToCoefficientFiel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

theorem _root_.GlobalTheory.T.complexHeckeEigenvector_descends_to_coefficientField : ∀ (D : D7) (M : Formalism.L2.MtFam D) (B : Formalism.L2.NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) (μ : D.what₂.Tup) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), μ = D.what₂.muTw w → ∀ (φ : FractionRing (B.Oc j w) →+* ℂ), (∀ x, φ (B.ec j w x) = D.what₂.embLL x) → ∀ (κ : PlE D.host → ℕ → FractionRing (B.Oc j w)) (y : D.what₂.Mt μ j), y ≠ 0 → (∀ v k, Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ Formalism.AUTREP.IsUnif D.host.E s.v ϖ ∧ (∀ (c : ℂ) (f f' : Formalism.AUTREP.GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W), Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k (c • f + f') = c • Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k f + Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k f') ∧ Formalism.L2.NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) = φ (κ v k) • (M μ j h1 h2).real y) → ∃ e : B.V j w, e ≠ 0 ∧ ∀ v k, Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → B.hK j w v k e = κ v k • e := by
  exact @GlobalTheory.PtLocalEig.eig_descends
