module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CasselmanWallachExtensionBanachTarget
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

theorem _root_.GlobalTheory.T.casselmanWallach_extension_banach_target : GlobalTheory.Published.CasselmanWallach → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (ρ : Mx n → (E →L[ℂ] E)), ModRep ε ρ → ∀ T₀ : H →ₗ[ℂ] E, (∀ k ∈ Kset ε, ∀ v, IsKFin ε σ v → T₀ (σ k v) = ρ k (T₀ v)) → (∀ X ∈ lieSet ε, ∀ v, IsKFin ε σ v → HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) (T₀ v)) (T₀ (dRep σ X v)) 0) → ∃ T : H →ₗ[ℂ] E, (∀ v, IsKFin ε σ v → T v = T₀ v) ∧ (∀ g ∈ UJset ε, ∀ w, Sm ε σ w → T (σ g w) = ρ g (T w)) ∧ ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ ∀ w, Sm ε σ w → ‖T w‖ ≤ C * sobNorm σ S w := by
  first | exact @GlobalTheory.TypeSum.casselmanWallach_banach | exact GlobalTheory.TypeSum.casselmanWallach_banach | (intros; apply GlobalTheory.TypeSum.casselmanWallach_banach <;> assumption)
