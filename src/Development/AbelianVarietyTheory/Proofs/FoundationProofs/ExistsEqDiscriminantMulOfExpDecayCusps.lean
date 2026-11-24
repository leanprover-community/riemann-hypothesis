module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory

theorem discriminant_slash_specialLinearGroup (x : SL(2, ℤ)) :
    (ModularForm.discriminant ∣[(12 : ℤ)] x) = ModularForm.discriminant :=
  (isCF_coe_top CuspForm.discriminant).1 x (Subgroup.mem_top x)

theorem exists_eq_discriminant_mul (Γ : Subgroup SL(2, ℤ)) (K : ℤ) (H : ℍ → ℂ) (hH : IsMF Γ K H)
    (hdec : ∀ x : SL(2, ℤ), (H ∣[K] x) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) :
    ∃ G : ℍ → ℂ, IsMF Γ (K - 12) G ∧ H = ModularForm.discriminant * G := by
  have hsl : ∀ x : SL(2, ℤ), (H / ModularForm.discriminant) ∣[K - 12] x =
      (H ∣[K] x) / ModularForm.discriminant := by
    intro x
    have := ModularForm.div_slash_SL2 K 12 x H ModularForm.discriminant
    rw [discriminant_slash_specialLinearGroup] at this
    exact this
  refine ⟨H / ModularForm.discriminant, ⟨fun γ hγ => ?_, ?_, fun x => ?_⟩, ?_⟩
  · rw [hsl, hH.1 γ hγ]
  · exact hH.2.1.div CuspForm.discriminant.holo' ModularForm.discriminant_ne_zero
  · rw [hsl, IsBoundedAtImInfty, BoundedAtFilter]
    exact (Asymptotics.div_isBoundedUnder_of_isBigO ((hdec x).trans ModularForm.exp_isBigO_discriminant)).isBigO_one ℝ
  · ext τ
    simp [mul_div_cancel₀ _ (ModularForm.discriminant_ne_zero τ)]

end GlobalTheory
