module

public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomPull

variable {D : D7} {N N' : ℕ}

def tPullL (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) : VC D N N' →ₗ[ℂ] VC D N N' where
  toFun := Formalism.L2.KerInert.tPull D (tor0 D cc δ) γ γ'
  map_add' := Formalism.L2.KerInert.ie_tPull_add cc δ γ γ'
  map_smul' := Formalism.L2.KerInert.ie_tPull_smul cc δ γ γ'

theorem hf_tPull (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (hγ : (letI := D.host.cmStar; γ * star γ) = 1)
    (hγ' : (letI := D.host.cmStar; γ' * star γ') = 1) (z w : VC D N N') :
    Hf D (tor0 D cc δ) (Formalism.L2.KerInert.tPull D (tor0 D cc δ) γ γ' z)
      (Formalism.L2.KerInert.tPull D (tor0 D cc δ) γ γ' w) = Hf D (tor0 D cc δ) z w := by
  letI := D.host.cmStar
  unfold Hf
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h1 := Formalism.L2.KerInert.PullbackComparison.map_mul_star D (embT D τ) γ hγ
  have h2 := Formalism.L2.KerInert.PullbackComparison.map_mul_star D (embT D τ) γ' hγ'
  rw [Matrix.star_eq_conjTranspose] at h1 h2
  exact Formalism.L2.KerInert.PullbackComparison.sum_mul_star_conj (γ.map (embT D τ)) (γ'.map (embT D τ)) h1 h2
    (Matrix.of (z τ)) (Matrix.of (w τ))

end GlobalTheory.MomPull


open GlobalTheory.MomPull in
theorem GlobalTheory.MomPull.pull_unitary : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ), letI := D.host.cmStar; ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), ∃ g : VC D N N' →L[ℂ] VC D N N', (∀ x ∈ La D (tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M'), g x ∈ La D (tor0 D cc δ) M M') ∧ ∀ (t : VC D N N') (G : VC D N N' → ℂ), U D (tor0 D cc δ) t (pull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) G) = fun z => U D (tor0 D cc δ) (g t) G (g z) := by
  intro D cc δ N N'
  letI := D.host.cmStar
  intro γ γ' M M'
  have h1' : star (γ' : Matrix (Fin N') (Fin N') D.host.E) * γ' = 1 := Matrix.mem_unitaryGroup_iff'.mp γ'.2
  have hγ : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ.2
  have hγ' : (γ' : Matrix (Fin N') (Fin N') D.host.E) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ'.2
  refine ⟨LinearMap.toContinuousLinearMap (tPullL cc δ (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E)), fun x hx => ?_, fun t G => ?_⟩
  · have h := Formalism.L2.KerInert.ie_La_pull cc δ _ _ h1' M M' hx
    exact h
  · funext z
    show G (Formalism.L2.KerInert.tPull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E) (z + t)) * _ =
      G (Formalism.L2.KerInert.tPull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E) z + Formalism.L2.KerInert.tPull D (tor0 D cc δ)
        (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) t) * _
    have e : ∀ y, (LinearMap.toContinuousLinearMap (tPullL cc δ (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E))) y = Formalism.L2.KerInert.tPull D (tor0 D cc δ)
        (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) y := fun _ => rfl
    simp only [e]
    rw [hf_tPull cc δ _ _ hγ hγ', hf_tPull cc δ _ _ hγ hγ', Formalism.L2.KerInert.ie_tPull_add]
