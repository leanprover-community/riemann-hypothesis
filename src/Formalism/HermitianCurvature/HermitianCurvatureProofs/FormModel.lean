module

public import Formalism.HermitianCurvature.StatementJC
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt

noncomputable section

def FormModel : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (sg : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (a : ℝ) (mm : ℕ)
    (ε' : ℝ) (Sg : Set (B.Mat P0.k (P0.r - j))),
    0 < ε' → P5.Auser P0 w.length + 1 ≤ a → P5.mmUser P0 w.length ≤ mm →
    5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ mm →
    (∀ γ ∈ Sg, ε' ≤ Formalism.QuantumDeterminants.Gf P0.k (P0.r - j) (T.bs j).z (T.bs j).z' γ) →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
      (Mo : U.CCModel P0.k (P0.r - j) (Wd.Ix (Fin w.length) → (Wq →L[ℂ] Wp)) a mm Sg V),
      ∃ (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (Cp : ℝ), 0 ≤ Cp ∧ (∀ u, (Bf u u).re ≤ (Cp * ‖u‖) ^ 2) ∧
        ∀ (u u' : V) (x x' : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε'' : ℝ), 0 < ε'' →
          (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 w.length + 1) (P5.mmUser P0 w.length) ε'' (x e)) →
          (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 w.length + 1) (P5.mmUser P0 w.length) ε'' (x' e)) →
          (∀ e, ∀ γ ∈ B.GV P0.k (P0.r - j), Mo.ev u γ e = x e γ) →
          (∀ e, ∀ γ ∈ B.GV P0.k (P0.r - j), Mo.ev u' γ e = x' e γ) →
          Bf u u' = D.formLev T sg j w x x'

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
