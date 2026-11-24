module

public import Formalism.HermitianCurvature.StatementTBB
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

namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def omT (p : KB.Pl P Wp Wq) (N : ℕ) (Q : C.LPt) : ℝ :=
  √(TBB.nPt P.k P.r (TBB.TTp p) Q) * √(Top.wPt (TBB.TTp p) P.r Q ^ N)

end place

def ptT (s : ℕ) (h : C.LPt) (x D : ℂ) : Option ℂ → C.LPt
  | none => h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)]
  | some u => h ++ [(s, u)]

def coT (s : ℕ) (x : ℂ) : Option ℂ → ℂ
  | none => ((‖x‖ ^ (s - 1) : ℝ) : ℂ)
  | some u => -(G.psi U.betaU ((s : ℂ) * u * x) * ((Real.pi ^ (s - 1) * ((s : ℝ) * ‖u‖ ^ (s - 1))⁻¹ : ℝ) : ℂ))

def epsT (s : ℕ) : ℂ := (-1) ^ (s + 1)

def TopGram1 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → (∀ y, 0 < nn y) →
    ∃ (I : Type) (_ : Fintype I) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
      (L : I → (Wq →L[ℂ] Wp) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)),
      (∀ i, 0 ≤ c i) ∧ (∀ i, KB.CptCoef p.T.base (Fi i)) ∧
      ∀ Q Q' : C.LPt, TBB.NP p nn F (P.r + 1) w Q Q' =
        ∑ i, (c i : ℂ) * ⟪(omT p w.length Q' : ℂ) • L i (p.V (Fi i) Q'),
          (omT p w.length Q : ℂ) • L i (p.V (Fi i) Q)⟫_ℂ

def TopCore1 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F' →
    ∀ (N b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
      ‖∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)), (coT s x j * (omT p N (ptT s h x D j) : ℂ)) •
          p.V F' (ptT s h x D j)‖ ≤ C * ‖x‖⁻¹

def YCont : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F' →
    ∀ (N m : ℕ) (h : C.LPt), (∀ q ∈ h, 1 ≤ q.1 ∧ q.2 ≠ 0) → 1 ≤ m → D.ptSize h + m = P.r + 1 →
      ContinuousOn (fun c : ℂ => (omT p N (h ++ [(m, c)]) : ℂ) • p.V F' (h ++ [(m, c)])) {0}ᶜ

end

end Formalism.FourierDecayAlt.P.CutBP.GT
