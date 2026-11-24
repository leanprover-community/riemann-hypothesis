module

public import Formalism.HermitianCurvature.StatementNF
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

open Matrix Finset
open scoped ContDiff

namespace Formalism.FourierDecayAlt.NF

open Formalism.REAL Formalism.QuantumDeterminants

def IsMulZ {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
    (W : Module.End ℂ (Q.RadSp k r z z' π π')) (f : ℂ → ℂ) : Prop :=
  ∀ Φ : Q.RadSp k r z z' π π', (W Φ : Q.Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' f (Φ : Q.Fn k r (Wq →L[ℂ] Wp))

def MulZExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
      ∃ W : Module.End ℂ (Q.RadSp P.k P.r z z' π π'), IsMulZ W f

def ActualZetaSmooth : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → ∀ (X : Q.ActualOps P.k P.r z z' π π') (f : ℂ → ℂ),
      ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
      ∀ W W₁ W₂ : Module.End ℂ (Q.RadSp P.k P.r z z' π π'), IsMulZ W f → IsMulZ W₁ (dZ f) → IsMulZ W₂ (dZb f) → ∀ Y : ℂ,
        X.t Y 1 0 * W = W * X.t Y 1 0 - W₁ * X.t Y 1 1 ∧ X.t Y 1 1 * W = W * X.t Y 1 1 ∧
        X.t Y 0 1 * W = W * X.t Y 0 1 + W₂ * X.t Y 1 1

def NFOrder0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → ∀ (X : Q.ActualOps P.k P.r z z' π π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r z z' π π'))),
      Q.IsActualLevel X d.L → Fr.IsStarLevel d.L → d.Rel → (∀ Y, X.QQ Y = d.QQ Y) →
      ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
      ∀ W W₁ W₂ : Module.End ℂ (Q.RadSp P.k P.r z z' π π'), IsMulZ W f → IsMulZ W₁ (dZ f) → IsMulZ W₂ (dZb f) →
        (∀ g, Commute (d.κ g).1 W) ∧
        (∀ l ∈ Finset.Icc 1 (P.k - 1), Commute (d.SS l).1 W ∧ Commute (star (d.SS l)).1 W) ∧
        d.L.nab.1 * W = W * d.L.nab.1 + W₁ ∧ d.L.nabs.1 * W = W * d.L.nabs.1 - W₂

def NFOrder0OfParts : Prop := MulZExists → ActualZetaSmooth → NFOrder0

def RelExtra {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A) : Prop :=
  d.L.nabs * d.L.nab - d.L.nab * d.L.nabs = (d.κ fun ρ => ((2 * M.aC P ρ * P.TT : ℝ) : ℂ)) * d.L.GGi * d.L.GGi ∧
  ∀ l ∈ Finset.Icc 1 (P.k - 1), (d.SS l * star (d.SS l) = d.κ fun ρ => ((M.NrmDown P l ρ : ℝ) : ℂ)) ∧
    ∀ j ∈ Finset.Icc 1 (P.k - 1), j ≠ l →
      d.SS j * d.SS l * (d.κ fun ρ => ((M.rho P ρ j - M.rho P ρ l - 1 : ℝ) : ℂ)) =
        d.SS l * d.SS j * (d.κ fun ρ => ((M.rho P ρ j - M.rho P ρ l + 1 : ℝ) : ℂ)) ∧
      star (d.SS l) * d.SS j = d.SS j * star (d.SS l)

def SExtra : Prop :=
  ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A), P.OK → Fr.IsStarLevel d.L → d.Rel →
    Wd.IsStart d.QQ (M.qC P) → RelExtra d

end Formalism.FourierDecayAlt.NF
