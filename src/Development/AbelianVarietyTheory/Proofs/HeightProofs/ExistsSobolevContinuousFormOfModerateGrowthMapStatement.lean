module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSobolevContinuousFormOfModerateGrowthMap
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
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotMemOfMulExp

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos


theorem _root_.GlobalTheory.T.exists_sobolevContinuous_form_of_moderateGrowthMap : GlobalTheory.Published.CasselmanWallach → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (N : ℕ) (T : H →ₗ[ℂ] (Mx n → ℂ)),
    (∀ v, IsKFin ε σ v → ∃ C : ℝ, ∀ g ∈ UJset ε, ‖T v g‖ ≤ C * (1 + Formalism.REAL.hs g) ^ N) →
    (∀ v, IsKFin ε σ v → ∀ k ∈ Kset ε, ∀ g ∈ UJset ε, T (σ k v) g = T v (g * k)) →
    (∀ v, IsKFin ε σ v → ∀ X ∈ lieSet ε, ∀ g ∈ UJset ε,
      HasDerivAt (fun t : ℝ => T v (g * NormedSpace.exp (t • X))) (T (dRep σ X v) g) 0) →
    ∃ L : H →ₗ[ℂ] ℂ, Sobolev₂ (lieSet ε) σ L ∧ ∀ v, IsKFin ε σ v → ∀ y ∈ UJset ε, T v y = L (σ y v) := by
  first | exact @GlobalTheory.TypeSum.GrowthForm.exists_form | exact GlobalTheory.TypeSum.GrowthForm.exists_form | (intros; apply GlobalTheory.TypeSum.GrowthForm.exists_form <;> assumption)
