module

public import Formalism.HermitianCurvature.StatementTBB
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EnergyBoundPolynomialWeightPowCapelliEigen
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

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

theorem _root_.GlobalTheory.T.energyBound_polynomialWeightPow_capelliEigen : GlobalTheory.HCXi.BesselXiIntegrable → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wf : Type) [NormedAddCommGroup Wf] [InnerProductSpace ℂ Wf] [FiniteDimensional ℂ Wf] (P : M.Par) (p : KB.Pl P Wp Wq) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ dA : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wf →L[ℂ] Wp)) (Aop : B.Mat P.k P.r → (Wq →L[ℂ] Wf)) (Y : Finset ℝ) (N : ℕ), (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat P.k P.r → ℂ) (L : Fin n₁ → (Wq →L[ℂ] Wf)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → (p.RR (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) 0 w [] []).re ≤ TBB.normC nn w * (B.beta p.T.base (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g))).re := by
  first | exact @GlobalTheory.energy_bound_gfPow_smul_comp_polyOp | exact GlobalTheory.energy_bound_gfPow_smul_comp_polyOp | (intros; apply GlobalTheory.energy_bound_gfPow_smul_comp_polyOp <;> assumption)
