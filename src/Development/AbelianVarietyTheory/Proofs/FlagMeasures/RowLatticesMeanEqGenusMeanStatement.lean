module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesMeanEqGenusMean
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

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowLattices_mean_eq_genus_mean : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ Λ₀ : LatV D, IsRowLat D F0 Λ₀ → ∀ reps : Finset (LatW D), Formalism.ThetaLiftIndependence.IsClassReps (D.sp.X 0).hT (L0X D Λ₀ (lf D F0)) reps → ∀ N : LatW D → ℕ∞, (∀ γ ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ L, N (Formalism.HermitianLatticesTheory.gmap γ L) = N L) → (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * (N (L0X D Λ (lf D F0)) : ℝ≥0∞)) * ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ₀ (lf D F0))) = (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) * ∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT L') : ℝ))⁻¹ * (N L' : ℝ≥0∞) := by
  first | exact @GlobalTheory.MeanGenus.mean_rows_eq_mean_genus | exact GlobalTheory.MeanGenus.mean_rows_eq_mean_genus | (intros; apply GlobalTheory.MeanGenus.mean_rows_eq_mean_genus <;> assumption)
