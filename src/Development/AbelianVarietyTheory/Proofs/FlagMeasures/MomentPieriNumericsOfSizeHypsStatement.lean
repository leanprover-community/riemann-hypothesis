module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.momentPieriNumerics_of_sizeHyps : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ (τ : D.what₂.Tau) (w : D.what₂.Word) (U : ℕ → ℝ), (∀ i : Fin D.R.k, U (i.val + 1) = uS D w τ i) → Num D.R.k D.R.rS (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) ∧ GapCell D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2) ∧ PI.BesselPeriodGGP.eps48 D.R.k D.R.rS = epsSH D.R := by
  first | exact @GlobalTheory.SizeNum.num_of_size | exact GlobalTheory.SizeNum.num_of_size | (intros; apply GlobalTheory.SizeNum.num_of_size <;> assumption)
