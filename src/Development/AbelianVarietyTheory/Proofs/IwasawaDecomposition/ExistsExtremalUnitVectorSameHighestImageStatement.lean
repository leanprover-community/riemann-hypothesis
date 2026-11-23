module

public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtremalUnitVectorSameHighestImage
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_extremalUnitVector_same_highestImage : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (X : Type) [AddCommGroup X] [Module ℂ X] (ε : Fin n → Bool) (lam μ : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (π : Matrix (Fin n) (Fin n) ℂ → (X →ₗ[ℂ] X)) (L : Submodule ℂ H) (φ : H →ₗ[ℂ] X) (v : H), IsURepOn (UJset ε) σ → L ≤ lowKSub ε lam σ → IsKStableOn ε σ L → (∀ k ∈ Formalism.REAL.Kset ε, ∀ x ∈ L, φ (σ k x) = π k (φ x)) → v ∈ L → ‖v‖ = 1 → (∀ t : Fin n → ℝ, π (Matrix.diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I)) (φ v) = Complex.exp (((∑ a, μ a * t a : ℝ) : ℂ) * Complex.I) • φ v) → (∀ (ν : Fin n → ℝ) (y : X), y ∈ Submodule.span ℂ {z | ∃ k ∈ Formalism.REAL.Kset ε, z = π k (φ v)} → y ≠ 0 → (∀ t : Fin n → ℝ, π (Matrix.diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I)) y = Complex.exp (((∑ a, ν a * t a : ℝ) : ℂ) * Complex.I) • y) → ∑ a : Fin n, ν a * (if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ)) ≤ ∑ a : Fin n, μ a * (if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ))) → ∃ x ∈ L, ‖x‖ = 1 ∧ IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) x ∧ φ x = φ v := by
  first | exact @GlobalTheory.ExtRep.exists_extremal_same_image | exact GlobalTheory.ExtRep.exists_extremal_same_image | (intros; apply GlobalTheory.ExtRep.exists_extremal_same_image <;> assumption)
