module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearDescentPartialFourierEqFourierDescent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.linearDescent_partialFourier_eq_fourier_descent : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ μK : Measure A.K, SelfDual μK (A.kerK ψ) → ∀ (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → (∀ (g : GL (Fin r) F) (b c : A.K), fourG M ψ f' (act g (LinDesc.pt A hG lam b c)) = A.fourK μK ψ (fun x => f' (act g (LinDesc.pt A hG lam x.1 x.2))) (b, c)) → ∀ x : A.K × A.K, LinDesc.desc A M hG lam α (fourG M ψ f') x = A.fourK μK ψ (LinDesc.desc A M hG lam α f') x := by
  first | exact @GlobalTheory.JR.LinDesc.Swap.desc_fourG_eq_fourK_desc | exact GlobalTheory.JR.LinDesc.Swap.desc_fourG_eq_fourK_desc | (intros; apply GlobalTheory.JR.LinDesc.Swap.desc_fourG_eq_fourK_desc <;> assumption)
