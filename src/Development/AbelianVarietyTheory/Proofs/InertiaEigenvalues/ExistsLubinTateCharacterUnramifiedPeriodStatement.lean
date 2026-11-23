module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLubinTateCharacterUnramifiedPeriod
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_lubinTate_character_unramified_period : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (s : ℕ), 0 < s → ∃ (K' : FinExt l) (_ : K.1 ≤ K'.1) (x : P.R.Bˣ) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ), (∀ c : ↥(MaximalUnramifiedExtension l), fr l s c = c → (c : Om l) ∈ K'.1) ∧ (∀ g, fr l s (χ g : ↥(MaximalUnramifiedExtension l)) = χ g) ∧ (Continuous fun g => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l)) ∧ (∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) ∧ P.ιB x ∈ Fil P 1 ∧ P.ιB x ∉ Fil P 2 ∧ ∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1 := by
  first | exact @GlobalTheory.LTChar.main | exact GlobalTheory.LTChar.main | (intros; apply GlobalTheory.LTChar.main <;> assumption)
