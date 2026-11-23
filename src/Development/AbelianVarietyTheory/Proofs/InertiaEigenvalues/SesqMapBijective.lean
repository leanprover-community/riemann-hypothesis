module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
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
import Mathlib.Tactic.Linter.Style
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

open GlobalTheory.PRep GlobalTheory.SmGL

noncomputable section

namespace GlobalTheory.HermDualSelf

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def sesqMap (π : Representation ℂ G V) {σ : Representation ℂ G W} (hσ : IsSmooth σ)
    (C : V →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (hC : ∀ g v w, C (π g v) (σ g w) = C v w) :
    W →ₗ⋆[ℂ] smoothPart π.dual :=
  LinearMap.codRestrict (smoothPart π.dual) C.flip fun w =>
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((hσ w).mem_nhds (by simp)) fun g hg => by
      have hg' : σ g w = w := hg
      ext a
      show C (π g⁻¹ a) w = C a w
      have h := hC g (π g⁻¹ a) w
      rw [hg'] at h
      rw [← h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])

theorem sesqMap_apply (π : Representation ℂ G V) {σ : Representation ℂ G W} (hσ : IsSmooth σ)
    (C : V →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (hC : ∀ g v w, C (π g v) (σ g w) = C v w) (w : W) (a : V) :
    ((sesqMap π hσ C hC w : smoothPart π.dual) : Module.Dual ℂ V) a = C a w := rfl

theorem sesqMap_comm (π : Representation ℂ G V) {σ : Representation ℂ G W} (hσ : IsSmooth σ)
    (C : V →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (hC : ∀ g v w, C (π g v) (σ g w) = C v w) (g : G) (w : W) :
    sesqMap π hσ C hC (σ g w) = contra π g (sesqMap π hσ C hC w) := by
  refine Subtype.ext (LinearMap.ext fun a => ?_)
  rw [contra_apply, sesqMap_apply, sesqMap_apply]
  have h := hC g (π g⁻¹ a) w
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
  exact h

theorem sesqMap_bijective (π : Representation ℂ G V) {σ : Representation ℂ G W} (hσ : IsSmooth σ)
    (C : V →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (hC : ∀ g v w, C (π g v) (σ g w) = C v w)
    (hinj : ∀ w, (∀ v, C v w = 0) → w = 0) (hne : ∃ w : W, w ≠ 0)
    (hirr : (contra π).IsIrreducible) : Function.Bijective (sesqMap π hσ C hC) := by
  set f := sesqMap π hσ C hC with hf
  have hi : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine hinj w fun v => ?_
    have := congrArg (fun l : smoothPart π.dual => (l : Module.Dual ℂ V) v) hw
    simpa [hf, sesqMap_apply] using this
  refine ⟨hi, ?_⟩
  let R : Subrepresentation (contra π) :=
    { toSubmodule := LinearMap.range f
      apply_mem_toSubmodule := fun g l hl => by
        obtain ⟨w, rfl⟩ := hl
        exact ⟨σ g w, sesqMap_comm π hσ C hC g w⟩ }
  rcases hirr.eq_bot_or_eq_top R with hR | hR
  · exfalso
    obtain ⟨w, hw⟩ := hne
    have : f w ∈ R.toSubmodule := ⟨w, rfl⟩
    rw [hR] at this
    exact hw (hi (by rw [(Submodule.mem_bot ℂ).1 this, map_zero]))
  · intro l
    have : l ∈ R.toSubmodule := by rw [hR]; exact Submodule.mem_top
    obtain ⟨w, hw⟩ := this
    exact ⟨w, hw⟩

end GlobalTheory.HermDualSelf
