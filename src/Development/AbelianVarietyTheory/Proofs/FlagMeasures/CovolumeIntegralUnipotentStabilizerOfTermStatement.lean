module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralUnipotentStabilizerOfTerm
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

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.covolume_integralUnipotentStabilizer_of_term : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C : ℝ, 1 ≤ C ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ (F0 : Fb D u) (Λ : LatV D), IsBase D u F0 → IsRowLat D F0 Λ → ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → ∀ (p : Point D.host.E (D.R.rS + 1)) (L U : GramM D), IsLoUni L → IsUpUni U → ZhatOM (ZhatL (lf D F0) F') = L * ptMat p * U → ∃ Ω : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat p) → ℂ), MeasurableSet Ω ∧ MeasureTheory.volume Ω * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) ≤ ENNReal.ofReal (HHZ D large₂.sc.b C (ZhatL (lf D F0) F') ^ (C * (D.R.rS : ℝ) ^ 2)) ∧ ∀ c : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat p) → ℂ, ∃ n ∈ NLam Λ (lf D F0) ∩ NLam Λ F', ∃ a : GramM D, (∀ j : Fin (D.R.rS + 1), n (frame F' j) = ∑ i : Fin (D.R.rS + 1), ((-1) ^ (i.val + j.val) * a i j) • frame F' i) ∧ (fun τ (q : GlobalTheory.LoopV.roots (ptMat p)) => ((U * a * U⁻¹).map (embS D τ) * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat p)) (c τ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) q.1.1 q.1.2) ∈ Ω := by
  first | exact @GlobalTheory.LoopC.CovTerm.covolume_term | exact GlobalTheory.LoopC.CovTerm.covolume_term | (intros; apply GlobalTheory.LoopC.CovTerm.covolume_term <;> assumption)
