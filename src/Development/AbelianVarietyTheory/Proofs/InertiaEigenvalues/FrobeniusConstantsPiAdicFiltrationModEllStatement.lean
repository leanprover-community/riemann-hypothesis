module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusConstantsPiAdicFiltrationModEll
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

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.frobenius_constants_piAdic_filtration_modEll : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (s : ℕ), (∀ a : RA LL, ∃ a' : RA LL, φRW LL (inclR LL a) = inclR LL a') ∧ NearPi AI LL s 2 (φRW LL (piR AI LL s)) ∧ (∀ (m : ℕ) (x : RW LL), NearPi AI LL s m x → NearPi AI LL s m (φRW LL x)) ∧ ∀ o : ↥(OL LL), NearPi AI LL s 1 (algebraMap ↥(OL LL) (RW LL) o) → ∃ o' : ↥(OL LL), o = (l : ↥(OL LL)) * o' := by
  first | exact @GlobalTheory.DecomplFrob.frobenius_and_constants | exact GlobalTheory.DecomplFrob.frobenius_and_constants | (intros; apply GlobalTheory.DecomplFrob.frobenius_and_constants <;> assumption)
