module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalComplementIsotropicSandwich
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rational_complement_isotropic_sandwich : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ (k : ℕ) (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E), (∀ (z : Mx D 1 k) (y : Mx D a b), symplO V W (GlobalTheory.IsoMean.cplx V W B z) (GlobalTheory.IsoMean.emb V W P Q y) = 0) ∧ (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∃ (z : Mx D 1 k) (y : Mx D a b), x = GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y) ∧ (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y = 0 → z = 0 ∧ y = 0) ∧ (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y ∈ ratL W V → z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b) ∧ (∀ z : Mx D 1 k, (∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ψ (symplO V W (GlobalTheory.IsoMean.cplx V W B z) (GlobalTheory.IsoMean.cplx V W B c)) = 1) ↔ z ∈ GlobalTheory.MixModel.ratMx D 1 k) := by
  first | exact @GlobalTheory.IsoCompl.ratCompl | exact GlobalTheory.IsoCompl.ratCompl | (intros; apply GlobalTheory.IsoCompl.ratCompl <;> assumption)
