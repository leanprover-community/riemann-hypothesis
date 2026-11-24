module

public import Formalism.HermitianCurvature.HerGenC
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelModuleFormEqIntegralOfCompactCoeff
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

theorem _root_.GlobalTheory.T.levelModuleForm_eq_integral_of_compactCoeff : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (j : ℕ) (h : C.LPt), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CutWord P p.l0 w → j ≤ P.r → D.IsLocPt h j → Integrable (fun t : ℂ => (KB.levW P (j + 1) t : ℂ) * p.RR H (j + 1) w (h ++ [(1, t)]) (h ++ [(1, t)])) ∧ p.RR H j w h h = ∫ t : ℂ, (KB.levW P (j + 1) t : ℂ) * p.RR H (j + 1) w (h ++ [(1, t)]) (h ++ [(1, t)]) := by
  first | exact @GlobalTheory.LevelIntegralStep.levelForm_eq_integral | exact GlobalTheory.LevelIntegralStep.levelForm_eq_integral | (intros; apply GlobalTheory.LevelIntegralStep.levelForm_eq_integral <;> assumption)
