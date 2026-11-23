module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftsAllChartsEqClassSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLifts_all_charts_eq_classSum : ∀ (D : D7) (c : Comm D) (ρ : RealD c), c.Is → ρ.Is → ∀ j (hj : j + 1 ≤ D.R.m) (hab : ρ.N j ≤ ρ.N (j + 1)), BorelSpace (GinfC (c.X j)) ∧ ∃ ν : Measure (GinfC (c.X j)), IsProbabilityMeasure ν ∧ ν.IsMulLeftInvariant ∧ ∀ (m : ℕ) (y : Fin m → c.Fr j) (P : Fin m → PolF D (c.X (j + 1)).rank (c.X j).rank) (m' : ℕ) (y' : Fin m' → D.what₂.Tau → Matrix (Fin (ρ.N (j + 1))) (Fin (ρ.N (j + 1))) ℂ) (y'' : Fin m' → c.Fr (j + 1)) (s : Fin m' → ℂ), (∀ i τ, (ρ.fr (j + 1) (y'' i)).1 τ = ρ.sc j τ • y' i τ) → (∀ F ∈ Vn (ρ.lam j) (ρ.n j), ∀ Λ : FP D.what₂.Tau (ρ.N j) (ρ.N (j + 1)) →ₗ[ℂ] ℂ, ∑ i, (∏ τ, ((ρ.fr j (y i)).1 τ).det ^ (-ρ.sS j τ)) * ∫ k, Λ (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj) k.1 τ)⁻¹) (fun _ => 1) (castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) (P i))) * evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj) k.1 τ * (ρ.fr j (y i)).1 τ) F ∂ν = ∑ i, s i * Λ (subY hab (y' i) F)) → ∀ (t : Tup c) (A : ClsK ρ t), t.Is → A.Is → ∀ ψ ∈ t.Ram j, ∀ γ, ∑ i, ∑ α, (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) (t.rd j α ψ (y i)) = t.cK j • ∑ i, (s i * ∏ τ, ((ρ.fr (j + 1) (y'' i)).1 τ).det ^ ρ.sD j τ) • t.rd (j + 1) γ (t.K j ψ) (y'' i) := by
  first | exact @GlobalTheory.SeeSaw.lift_eq_classSum | exact GlobalTheory.SeeSaw.lift_eq_classSum | (intros; apply GlobalTheory.SeeSaw.lift_eq_classSum <;> assumption)
