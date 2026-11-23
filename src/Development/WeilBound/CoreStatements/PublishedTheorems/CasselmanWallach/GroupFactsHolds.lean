module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.IsInLieAlgebraISmulAddConjTranspose
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CompactGroupFacts

variable {n : ℕ}

theorem mul_mem (ε : Fin n → Bool) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) :
    g * h ∈ UJset ε := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hh' : hᴴ * Jm ε * h = Jm ε := hh
  show (g * h)ᴴ * Jm ε * (g * h) = Jm ε
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg', hh']

theorem hilbert_schmidt_continuous : Continuous (hs2 : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold hs2
  fun_prop

theorem isClosed_UJ (ε : Fin n → Bool) : IsClosed (UJset ε) := by
  have : UJset ε = (fun g : Matrix (Fin n) (Fin n) ℂ => gᴴ * Jm ε * g) ⁻¹' {Jm ε} := rfl
  rw [this]
  exact isClosed_singleton.preimage (by fun_prop)

theorem entry_le (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖g i j‖ ^ 2 ≤ hs2 g := by
  unfold hs2
  calc ‖g i j‖ ^ 2 ≤ ∑ j', ‖g i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖g i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖g i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖g i' j'‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

theorem compact (ε : Fin n → Bool) (ρ : ℝ) : IsCompact {g | g ∈ UJset ε ∧ hs2 g ≤ ρ} := by
  let K : Set (Fin n → Fin n → ℂ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) (Real.sqrt ρ)
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hK.of_isClosed_subset ((isClosed_UJ ε).inter (isClosed_le hilbert_schmidt_continuous continuous_const)) ?_
  rintro g ⟨-, hg⟩ i - j -
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact Real.le_sqrt_of_sq_le ((entry_le g i j).trans hg)

theorem Xp_inP (ε : Fin n → Bool) (p : Fin n × Fin n) (hp : p ∈ nc ε) : inP ε (Xp p.1 p.2) := by
  obtain ⟨a, b⟩ := p
  have hab : ε a ≠ ε b := by simpa [nc] using hp
  have hne : a ≠ b := fun h => hab (h ▸ rfl)
  set σ : Fin n → ℂ := fun k => if ε k then 1 else -1 with hσdef
  have hσ : σ b = -σ a := by
    simp only [hσdef]; revert hab; cases ε a <;> cases ε b <;> simp
  have h2 : Xp a b * Jm ε = -(Jm ε * Xp a b) := by
    show Xp a b * Matrix.diagonal σ = -(Matrix.diagonal σ * Xp a b)
    ext i j
    simp only [Xp, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply, Matrix.add_apply,
      Matrix.single_apply]
    by_cases h1 : a = i ∧ b = j <;> by_cases h3 : b = i ∧ a = j
    · exact absurd (h1.1.trans h3.1.symm) hne
    · obtain ⟨rfl, rfl⟩ := h1; simp only [if_neg h3, hσ]; ring
    · obtain ⟨rfl, rfl⟩ := h3; simp only [if_neg h1, hσ]; ring
    · simp only [if_neg h1, if_neg h3]; ring
  have hh : (Xp a b)ᴴ = Xp a b := by
    ext i j
    simp only [Xp, Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.single_apply]
    by_cases hi : a = i <;> by_cases hj : b = j <;> by_cases hi' : b = i <;> by_cases hj' : a = j <;>
      subst_vars <;> simp_all [Complex.ext_iff]
  refine ⟨?_, h2⟩
  show (Xp a b)ᴴ * Jm ε + Jm ε * Xp a b = 0
  rw [hh, h2, neg_add_cancel]

end CompactGroupFacts

theorem group_facts_holds : UnitaryGroupFacts := by
  intro n ε
  refine ⟨CompactGroupFacts.compact ε, ?_, ?_, ?_, CompactGroupFacts.hilbert_schmidt_continuous, CompactGroupFacts.Xp_inP ε⟩
  · show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  · intro g hg X hX t
    refine CompactGroupFacts.mul_mem ε hg ?_
    have := rq_exp_mem ε X hX.1 t
    rwa [Complex.coe_smul] at this
  · intro X s t
    rw [add_smul]
    exact Matrix.exp_add_of_commute _ _ ((Commute.refl X).smul_left s |>.smul_right t)

end PositivityTheory.CW

end
