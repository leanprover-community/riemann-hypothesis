module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.MainNotions.N

namespace GlobalTheory.ConjugateIrreducibility

private theorem isIrrSub_of_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (H H' : Subgroup Γ)
    (hHH : ∀ s ∈ H, s ∈ H') (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k)
    (hconj : ∀ s : Γ, (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹)
    (hne : (⊤ : Submodule k (Fin n → k)) ≠ ⊥)
    (hmin : ∀ W : Submodule k (Fin n → k), W ≤ ⊤ → IsInv (MonoidHom.comp r (Subgroup.subtype H)) W →
      W = ⊥ ∨ W = ⊤) :
    IsIrrSub (MonoidHom.comp r' (Subgroup.subtype H')) ⊤ := by
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun W _ hinv => ?_⟩

  let W₀ : Submodule k (Fin n → k) := W.comap (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k))
  have hmem : ∀ v, v ∈ W₀ ↔ (g : Matrix (Fin n) (Fin n) k).mulVec v ∈ W := fun v => by
    simp [W₀, Matrix.toLin'_apply]
  have hinv₀ : IsInv (MonoidHom.comp r (Subgroup.subtype H)) W₀ := by
    intro s v hv
    rw [hmem] at hv ⊢
    have key : (g : Matrix (Fin n) (Fin n) k).mulVec ((r s.1 : Matrix (Fin n) (Fin n) k).mulVec v) =
        (r' s.1 : Matrix (Fin n) (Fin n) k).mulVec ((g : Matrix (Fin n) (Fin n) k).mulVec v) := by
      simp [hconj, Matrix.mulVec_mulVec, mul_assoc]
    have h1 := hinv ⟨s, hHH s s.2⟩ _ hv
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at h1 ⊢
    rw [key]
    exact h1
  have hback : ∀ w, ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec w ∈ W₀ ↔ w ∈ W := fun w => by
    rw [hmem, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rcases hmin W₀ le_top hinv₀ with h0 | htop
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 := (hback w).mpr hw
    rw [h0, Submodule.mem_bot] at h1
    have h2 := congrArg (Matrix.mulVec (g : Matrix (Fin n) (Fin n) k)) h1
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    rw [h2]
    exact Submodule.zero_mem _
  · right
    rw [eq_top_iff]
    intro w _
    exact (hback w).mp (htop ▸ Submodule.mem_top)

theorem target : ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} (H H' : Subgroup Γ), (∀ s ∈ H, s ∈ H') → ∀ (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k), (∀ (s : Γ), (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹) → Formalism.MainNotions.N.IsIrrSub (MonoidHom.comp r (Subgroup.subtype H)) ⊤ → Formalism.MainNotions.N.IsIrrSub (MonoidHom.comp r' (Subgroup.subtype H')) ⊤ := by
  intro Γ k _ _ n H H' hHH r r' g hconj hirr
  obtain ⟨hne, -, hmin⟩ := hirr
  exact isIrrSub_of_conj H H' hHH r r' g hconj hne hmin

end GlobalTheory.ConjugateIrreducibility
