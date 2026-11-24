module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
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

open Matrix Finset

noncomputable section

namespace GlobalTheory.WigSh

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutBP2

def ShiftExists : Prop :=
  ∃ c₃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (P : M.Par) (Wp Wq : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (l n₀ lp lm : ℕ) (b : ℝ),
    (∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i) →
    1 ≤ l → l < P.k → 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1) →
    (∀ i ∈ Finset.Icc 1 P.k, |P.u' i| ≤ b) → (n₀ : ℝ) ≤ b → 1 ≤ b →
    1 ≤ lp → lp ≤ P.k → 1 ≤ lm → lm ≤ P.k →
    ∃ (Wqp : Type) (_ : NormedAddCommGroup Wqp) (_ : InnerProductSpace ℂ Wqp) (_ : FiniteDimensional ℂ Wqp)
      (Wqm : Type) (_ : NormedAddCommGroup Wqm) (_ : InnerProductSpace ℂ Wqm) (_ : FiniteDimensional ℂ Wqm)
      (pp : KB.Pl (shP P P.u (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)))) Wp Wqp)
      (pm : KB.Pl (shP P P.u (Function.update P.u' l (P.u' l - (n₀ : ℝ)))) Wp Wqm)
      (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq))
      (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)),
      pp.l0 = lp ∧ pm.l0 = lm ∧
      pp.T.base.z = p.T.base.z ∧ pp.T.base.z' = p.T.base.z' ∧ pp.T.base.π = p.T.base.π ∧
      pm.T.base.z = p.T.base.z ∧ pm.T.base.z' = p.T.base.z' ∧ pm.T.base.π = p.T.base.π ∧
      KB.InDDplus2 (shP P P.u (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)))) pp.l0 pp.T.base Cb pp.Θ ∧
      KB.InDDplus2 (shP P P.u (Function.update P.u' l (P.u' l - (n₀ : ℝ)))) pm.l0 pm.T.base Cb pm.Θ ∧
      (∃ (t : ℕ) (c : Fin t → B.Mat P.k P.r → ℂ) (L : Fin t → (Wqp →L[ℂ] Wq)),
        (∀ i, U.IsPolyDeg (n₀ * (P.r + 1)) (c i)) ∧ ∀ g, Ap g = ∑ i, c i g • L i) ∧
      (∃ (t : ℕ) (c : Fin t → B.Mat P.k P.r → ℂ) (L : Fin t → (Wqm →L[ℂ] Wq)),
        (∀ i, U.IsPolyDeg (n₀ * (P.r + 1)) (c i)) ∧ ∀ g, Am g = ∑ i, c i g • L i) ∧
      (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ∀ g ∈ B.GV P.k P.r,
        Zhat P.k P.r p.T.base.z p.T.base.z' g = D.ptMatN γ (P.r + 1) → D.IsDFrame p.T.base p.ν' p.m₀ g →
        ApPt γ = Ap g ∧ AmPt γ = Am g) ∧
      ∀ (A₀ : ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
        c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₀ → B.InCC A₀ 1 f →
        AmapsSh p pp pm f Ap Am ApPt AmPt b n₀

end GlobalTheory.WigSh
