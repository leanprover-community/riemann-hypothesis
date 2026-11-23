module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TupMemLatT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledProductSpanLatticeEntriesAndSpan
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.scaledProductSpanLattice_entries_and_span : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (L : Fin m → FinExt l) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ), (∀ k g i j, ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ (L k).1) → (∀ k, ∀ x ∈ t k, ∀ i j, x i j ∈ (L k).1) → (∀ k (x : Matrix (Fin a) (Fin a) (Om l)), (∀ i j, x i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l)))) → (∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∀ k i j, x k i j ∈ (L k).1) ∧ ∀ x : Fin m → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (GlobalTheory.TraceConjugationCover.latT ρs t M : Set (Fin m → Matrix (Fin a) (Fin a) (Om l))) := by
  first | (exact @GlobalTheory.TraceConjugationCover.latT_entries_and_span) | (exact GlobalTheory.TraceConjugationCover.latT_entries_and_span) | (intros; apply GlobalTheory.TraceConjugationCover.latT_entries_and_span  <;> assumption)
