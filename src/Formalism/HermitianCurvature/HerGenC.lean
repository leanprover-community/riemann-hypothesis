module

public import Formalism.HermitianCurvature.TopDensNonnegOfKappa
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

section HerC

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable (S : Type) [Fintype S] [DecidableEq S]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
  (D : B.RealPlaceData P.k P.r Wp Wq)

def JFOKCpt (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) : Prop :=
  JFOK P z z' F ∧ HasCompactSupport F

inductive HerGenC : Fin (P.r + 1) → RadSp P.k P.r z z' π π' → Prop
  | jf (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (Φ : RadSp P.k P.r z z' π π') :
      JFOKCpt P z z' F → IsRadJF P z z' π π' D F Φ → HerGenC 0 Φ
  | slice (l : Fin P.r) (w : List (Letter ℂ S)) (a b : Ix S) (Φ : RadSp P.k P.r z z' π π') :
      WordOK P z z' π π' st l0 w → HerGenC l.castSucc Φ → HerGenC l.succ ((bTl L l w a b).1 Φ)
  | waveC (l : Fin P.r) (w : List (Letter ℂ S)) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
      (a b : Ix S) (Φ : RadSp P.k P.r z z' π π') :
      WordOK P z z' π π' st l0 w → multiplicationOperator Wv (fun c' _ => fsv s (c' l)) → multiplicationOperator Wv' (fun c' _ => fsv (-s) (c' l)) →
      HerGenC l.castSucc Φ → HerGenC l.castSucc ((Vw (mkP Wv Wv') s w a b).1 Φ)
  | waveZ (w : List (Letter ℂ S)) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
      (a b : Ix S) (Φ : RadSp P.k P.r z z' π π') :
      WordOK P z z' π π' st l0 w → multiplicationOperator Wv (fun _ g => fsv s (zeta P.k P.r z z' g)) →
      multiplicationOperator Wv' (fun _ g => fsv (-s) (zeta P.k P.r z z' g)) →
      HerGenC (Fin.last P.r) Φ → HerGenC (Fin.last P.r) ((Vw (mkP Wv Wv') s w a b).1 Φ)

def herKc (i : Fin (P.r + 1)) : Submodule ℂ (RadSp P.k P.r z z' π π') :=
  Submodule.span ℂ {Φ | HerGenC S P z z' π π' L st l0 D i Φ}

end HerC

def HerClassesCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (A : ℝ) (mm : ℕ),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    Auser P (Fintype.card S) ≤ A → mmUser P (Fintype.card S) ≤ mm →
    ∃ K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π'),
      AdjTop (S := S) P z z' π π' μ L st K l0 ∧ TopDensNonneg (S := S) P z z' π π' L st K l0 ∧
      TopTwist (S := S) P z z' π π' L st K l0 ∧ SliceIn (S := S) P z z' π π' L st K l0 ∧
      StepDens (S := S) P z z' π π' μ L st K l0 ∧ WaveK (S := S) P z z' π π' st K l0 ∧
      FormSesq (S := S) P z z' π π' μ L st K l0 ∧ CompositeFormulaLevelZero (S := S) P z z' π π' μ L st K l0 ∧
      ∀ (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε → (∀ (A' : ℝ) (m' : ℕ), B.InCC A' m' F) →
        HasCompactSupport F → (∀ g ∈ B.GV P.k P.r, F g ≠ 0 → ε ≤ Gf P.k P.r z z' g) →
        ∃ Φ ∈ K 0, ∀ x ∈ DomR P.k P.r z z',
          (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) (B.JF D F) x.1 x.2

def ThmPActualCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (A : ℝ) (mm : ℕ),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    Auser P (Fintype.card S) ≤ A → mmUser P (Fintype.card S) ≤ mm →
    ∃ K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π'),
      ThmPOn (S := S) P z z' π π' μ L st K l0 ∧ SliceIn (S := S) P z z' π π' L st K l0 ∧
      CompositeFormulaLevelZero (S := S) P z z' π π' μ L st K l0 ∧
      ∀ (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε → (∀ (A' : ℝ) (m' : ℕ), B.InCC A' m' F) →
        HasCompactSupport F → (∀ g ∈ B.GV P.k P.r, F g ≠ 0 → ε ≤ Gf P.k P.r z z' g) →
        ∃ Φ ∈ K 0, ∀ x ∈ DomR P.k P.r z z',
          (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) (B.JF D F) x.1 x.2

end Formalism.FourierDecayAlt.P5
