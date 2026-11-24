module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitFactorRegularSemisimpleReducible
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LinearIndependentE

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct


theorem _root_.GlobalTheory.T.exists_split_factor_regularSemisimple_reducible : ∀ {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E), 0 < n → IsRegSS (γ : Matrix (Fin n) (Fin n) E) → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClauseAlg σ J γ → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClauseRank σ J γ → ¬ Irreducible (γ : Matrix (Fin n) (Fin n) E).charpoly → ¬ IsNonFieldAniso σ J (γ : Matrix (Fin n) (Fin n) E) → ∃ (k : ℕ) (K : Fin k → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, Algebra F (K i)), Nonempty (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg σ J (γ : Matrix (Fin n) (Fin n) E) ≃ₐ[F] ∀ i, K i) ∧ ∃ i, ¬ IsField (K i ⊗[F] E) := by
  first | exact @GlobalTheory.SplitFactor.exists_split_factor | exact GlobalTheory.SplitFactor.exists_split_factor | (intros; apply GlobalTheory.SplitFactor.exists_split_factor <;> assumption)
