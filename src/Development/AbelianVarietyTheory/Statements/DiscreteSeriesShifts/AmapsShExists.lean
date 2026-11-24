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

def AmapsShExists : Prop :=
  ∃ c₃ : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp]
    [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm]
    (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp)
    (pm : KB.Pl (shP P um um') Wp Wqm) (l n₀ : ℕ) (b : ℝ),
    pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' →
    pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' →
    (∀ h ∈ UWset P.k P.r p.T.base.z, pp.T.base.π h = p.T.base.π h) →
    (∀ h ∈ UWset P.k P.r p.T.base.z, pm.T.base.π h = p.T.base.π h) →
    pp.ν' = p.ν' → pp.m₀ = p.m₀ → pm.ν' = p.ν' → pm.m₀ = p.m₀ →
    1 ≤ l → l < P.k → 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1) →
    (∀ i ∈ Finset.Icc 1 P.k, |P.u' i| ≤ b) → (n₀ : ℝ) ≤ b → 1 ≤ b →
    (∀ i ∈ Finset.Icc 1 P.k, up' i = if i = l + 1 then P.u' i + (n₀ : ℝ) else P.u' i) →
    (∀ i ∈ Finset.Icc 1 P.k, um' i = if i = l then P.u' i - (n₀ : ℝ) else P.u' i) →
    ∃ (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq))
      (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)),
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
