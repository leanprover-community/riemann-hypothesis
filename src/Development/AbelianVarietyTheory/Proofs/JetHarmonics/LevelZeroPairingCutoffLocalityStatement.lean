module

public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingCutoffLocality
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

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.levelZeroPairing_cutoff_locality : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (χ : ℝ → ℝ) (δ ε ε₁ : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), C6.IsCut0 χ → (∀ x, x < δ → χ x = 0) → 0 < ε → 0 < ε₁ → ε₁ < δ * ε → B.CkOn ⊤ (B.GV P.k P.r) F → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV P.k P.r (a.2 : ℂ) G) ((D.cutF p.T.base χ F ε₁)) w) (D.cutF p.T.base χ F ε) = B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV P.k P.r (a.2 : ℂ) G) (F) w) (D.cutF p.T.base χ F ε) := by
  first | exact @GlobalTheory.beta_fold_cut_eq_beta_fold_of_cut | exact GlobalTheory.beta_fold_cut_eq_beta_fold_of_cut | (intros; apply GlobalTheory.beta_fold_cut_eq_beta_fold_of_cut <;> assumption)
