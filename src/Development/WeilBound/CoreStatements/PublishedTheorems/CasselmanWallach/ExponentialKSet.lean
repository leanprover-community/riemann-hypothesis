module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.HahnBanach
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined

namespace PositivityTheory.CW

namespace ExistsFunctional

theorem exists_functional {E : Type} [AddCommGroup E] [Module ℂ E] (q : Seminorm ℂ E) {x₀ : E} (hx : q x₀ ≠ 0) :
    ∃ φ : Module.Dual ℂ E, φ x₀ ≠ 0 ∧ ∀ x, ‖φ x‖ ≤ q x := by
  have h0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx (map_zero q)
  let e := LinearEquiv.toSpanNonzeroSingleton ℂ E x₀ h0
  let f : Module.Dual ℂ (Submodule.span ℂ {x₀}) := (q x₀ : ℂ) • (e.symm : _ →ₗ[ℂ] ℂ)
  have hfe : ∀ t : ℂ, f (e t) = t * q x₀ := by
    intro t
    simp [f, mul_comm]
  obtain ⟨g, hg, hgp⟩ := Module.Dual.exists_extension_of_le_seminorm (Submodule.span ℂ {x₀}) f
    (p := q) (by
      intro y
      obtain ⟨t, rfl⟩ := e.surjective y
      rw [hfe, norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q x₀)]
      rw [LinearEquiv.toSpanNonzeroSingleton_apply]
      simp [map_smul_eq_mul])
  refine ⟨g, ?_, hgp⟩
  have h1 := hg (e 1)
  rw [hfe, one_mul] at h1
  have : ((e 1 : Submodule.span ℂ {x₀}) : E) = x₀ := by
    rw [LinearEquiv.toSpanNonzeroSingleton_one]
  rw [this] at h1
  rw [h1]
  exact_mod_cast hx

end ExistsFunctional

theorem e1b : faceMap_comp_succAbove_castSucc := by
  unfold faceMap_comp_succAbove_castSucc AllTgt
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hrep T hT i w₀ hw₀ hp u hu hu0
  by_contra hall
  push_neg at hall
  obtain ⟨φ, hφ0, hφ⟩ := ExistsFunctional.exists_functional (p i) hp
  let ℓ : H →ₗ[ℂ] ℂ := φ ∘ₗ T
  have hlie : ((GlobalTheory.LowTypeDetermined.lie (Jm ε) : Set (Mx n))) = lieSet ε := rfl
  have hsm : ∀ w, Sm ε σ w →
      w ∈ GlobalTheory.LowTypeDetermined.smooth (Jm ε) (fun g => σ (1 * g * (1 : Mx n)⁻¹)) := by
    intro w hw
    change SmoothVec ((GlobalTheory.LowTypeDetermined.lie (Jm ε) : Set (Mx n)))
      (fun g => σ (1 * g * (1 : Mx n)⁻¹)) w
    simp only [inv_one, mul_one, one_mul]
    rw [hlie]
    exact hw
  have key := GlobalTheory.LowTypeDetermined.eq_zero_of_translates (G := Jm ε) (P := 1) hU hI isUnit_one
    (by simp) (ℓ := ℓ) ?_ (hsm u hu) hu0 ?_ (hsm w₀ hw₀)
  · exact hφ0 key
  · obtain ⟨S, C, hS, hb⟩ := hT.2 i
    refine ⟨S, C, ?_, ?_⟩
    · rw [hlie]
      exact hS
    · simp only [inv_one, mul_one, one_mul]
      rw [hlie]
      intro w hw
      exact (hφ (T w)).trans (hb w hw)
  · intro g hg
    show φ (T (σ g u)) = 0
    rw [hT.1 g hg u hu]
    exact norm_le_zero_iff.mp ((hφ _).trans (hall g hg).le)

end PositivityTheory.CW
