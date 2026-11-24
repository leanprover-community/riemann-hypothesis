module

public import Formalism.HermitianCurvature.StatementTBB
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityBigCellEqProdLevelWeightsMulTopForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.topDensity_bigCell_eq_prod_levelWeights_mul_topForm : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), (∀ a, c a ≠ 0) → TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) = (∏ i : Fin (P.r + 1), KB.levW P ((i : ℕ) + 1) (c i)) * (p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).re ∧ (p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).im = 0 ∧ 0 ≤ (p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).re := by
  first | exact @GlobalTheory.TopDensity.topDensity_eq | exact GlobalTheory.TopDensity.topDensity_eq | (intros; apply GlobalTheory.TopDensity.topDensity_eq <;> assumption)
