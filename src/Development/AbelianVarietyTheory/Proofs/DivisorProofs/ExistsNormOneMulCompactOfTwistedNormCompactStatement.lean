module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwConj
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOneMulCompactOfTwistedNormCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.exists_normOne_mul_compact_of_twistedNorm_compact : ∀ (K : Type) [NontriviallyNormedField K] [ProperSpace K] [StarRing K], (∀ x : K, ‖star x‖ = ‖x‖) → ∀ (n : ℕ) (δ : Matrix (Fin n) (Fin n) K), GlobalTheory.Tw.Reg δ → ∀ C : Set (GL (Fin n) K), IsCompact C → ∃ D : Set (GL (Fin n) K), IsCompact D ∧ ∀ z : GL (Fin n) K, (z : Matrix (Fin n) (Fin n) K) ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm δ} → ∀ u ∈ C, (u : Matrix (Fin n) (Fin n) K) = (z : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ (z : Matrix (Fin n) (Fin n) K) → ∃ t : GL (Fin n) K, (t : Matrix (Fin n) (Fin n) K) ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm δ} ∧ (t : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ (t : Matrix (Fin n) (Fin n) K) = 1 ∧ ∃ d ∈ D, z = t * d := by
  first | exact @GlobalTheory.Tw.NormOneCore.exists_normOne_mul_compact | exact GlobalTheory.Tw.NormOneCore.exists_normOne_mul_compact | (intros; apply GlobalTheory.Tw.NormOneCore.exists_normOne_mul_compact <;> assumption)
