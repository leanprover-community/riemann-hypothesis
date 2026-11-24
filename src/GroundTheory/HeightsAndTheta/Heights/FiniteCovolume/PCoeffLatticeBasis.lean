module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

theorem CoeffLatticeBasis.proof (E : Type*) [Field E] [NumberField E] :
    CoeffLatticeBasis.Statement E := by
  intro A hO hfg
  have : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg A).mpr hfg
  obtain ⟨n, b⟩ : Σ n : ℕ, Basis (Fin n) ℤ A := Module.basisOfFiniteTypeTorsionFree'

  let f : A →ₗ[ℤ] E := A.subtype.toIntLinearMap
  let v : Fin n → E := fun i => (b i : E)
  have hv : v = f ∘ b := rfl
  have hliZ : LinearIndependent ℤ v :=
    b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hliQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ

  have hA : ∀ a ∈ A, a ∈ Submodule.span ℚ (Set.range v) := by
    intro a ha
    have h1 : f ⟨a, ha⟩ ∈ Submodule.span ℤ (f '' Set.range b) :=
      Submodule.apply_mem_span_image_of_mem_span f (b.mem_span _)
    rw [← Set.range_comp, ← hv] at h1
    exact Submodule.span_le_restrictScalars ℤ ℚ _ h1
  have hsp : ⊤ ≤ Submodule.span ℚ (Set.range v) := by
    rw [← (integralBasis E).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [integralBasis_apply]
    exact hA _ (hO ⟨_, rfl⟩)
  have hn : finrank ℚ E = n := by
    rw [finrank_eq_card_basis (Basis.mk hliQ hsp), Fintype.card_fin]
  exact ⟨b.reindex (finCongr hn.symm)⟩

end GroundTheory.Heights₂.Heights.FiniteCovolume
