module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableLinearFormOnConstants
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_linearForm_semistable_extending_trace : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), ∃ lam : Bst P →ₗ[ℚ_[l]] ℚ_[l], (∀ c : ↥(K0 K), lam (phiSt P (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) = lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) ∧ ∀ c : ↥(K0 K), (∀ c' : ↥(K0 K), lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c') * Polynomial.C (algebraMap ↥(K0 K) P.R.B c)) = 0) → c = 0 := by
  first | exact @GlobalTheory.PMon.exists_phiSt_invariant_nondegenerate_linearForm | exact GlobalTheory.PMon.exists_phiSt_invariant_nondegenerate_linearForm | (intros; apply GlobalTheory.PMon.exists_phiSt_invariant_nondegenerate_linearForm <;> assumption)
