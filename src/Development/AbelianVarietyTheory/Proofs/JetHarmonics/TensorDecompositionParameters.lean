module

import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorDecompositionParameters
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeries₂.Poulsen
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TensForm

theorem common_bound {ι α β : Type} [DecidableEq ι] (P : α → Prop) (S : Set β) (n : α → β → ℝ)
    (hn : ∀ a v, 0 ≤ n a v) (f : ι → β → ℝ)
    (h : ∀ c, ∃ (C : ℝ) (L : List α), (∀ a ∈ L, P a) ∧ ∀ v ∈ S, f c v ≤ C * (L.map fun a => n a v).sum)
    (s : Finset ι) :
    ∃ (C : ℝ) (L : List α), 0 ≤ C ∧ (∀ a ∈ L, P a) ∧
      ∀ c ∈ s, ∀ v ∈ S, f c v ≤ C * (L.map fun a => n a v).sum := by
  apply Gp91.GlobalTheory.TensForm.common_bound <;> assumption

variable {k r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem hh_act (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (R : Rep k r) (g : Mx k r)
    (hρ : (ρ g)ᴴ * Γ * ρ g = Γ) (hσ : ∀ v, ‖R.σ g v‖ = ‖v‖) (x y : ι → R.H) :
    hh Γ R (act ρ R g x) (act ρ R g y) = hh Γ R x y := by
  apply Gp91.GlobalTheory.TensForm.hh_act <;> assumption


omit [DecidableEq ι] in
theorem norm_hh_le (Γ : Matrix ι ι ℂ) (R : Rep k r) (x y : ι → R.H) (A B : ℝ)
    (hx : ∀ c, ‖x c‖ ≤ A) (hy : ∀ c, ‖y c‖ ≤ B) :
    ‖hh Γ R x y‖ ≤ (∑ i, ∑ j, ‖Γ i j‖) * (A * B) := by
  rw [hh, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans ?_) (norm_nonneg _)
  rw [mul_comm A B]
  exact mul_le_mul (hy i) (hx j) (norm_nonneg _) ((norm_nonneg _).trans (hy i))

theorem family_bound (R R' : Rep k r) (T : ι → R.H → R'.H) (hT : ∀ c, SmMap R R' (T c)) :
    ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
      ∀ c, ∀ v ∈ R.sm, ‖T c v‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W v‖).sum := by
  obtain ⟨C, L, -, hL, hb⟩ := common_bound (fun W : List (Mx k r) => ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) R.sm
    (fun W v => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W v‖) (fun _ _ => norm_nonneg _)
    (fun c v => ‖T c v‖) (fun c => (hT c).cont [] (by simp)) Finset.univ
  exact ⟨C, L, hL, fun c => hb c (Finset.mem_univ c)⟩

theorem pulledBack_isInvForm : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → ∀ I J, IsInvForm (RI I) (RI J) (fun y y' => hh Γ R (fun c => io I c y) (fun c => io J c y')) := by
  intro _ k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI hR _ hF hT I J
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx x' hx' y _
    simp only [hh, fun c => (hT.io_sm I c).add x hx x' hx', inner_add_right, mul_add, Finset.sum_add_distrib]
  · intro a x hx y _
    simp only [hh, fun c => (hT.io_sm I c).smul a x hx, inner_smul_right, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · intro x _ y hy y' hy'
    simp only [hh, fun c => (hT.io_sm J c).add y hy y' hy', inner_add_left, mul_add, Finset.sum_add_distrib]
  · intro a x _ y hy
    simp only [hh, fun c => (hT.io_sm J c).smul a y hy, inner_smul_left, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [RCLike.star_def]; ring
  · intro g hg x hx y hy
    show hh Γ R (fun c => io I c ((RI I).σ g x)) (fun c => io J c ((RI J).σ g y)) = _
    rw [hT.io_eq I g hg x hx, hT.io_eq J g hg y hy]
    exact hh_act ρ Γ R g (hF.2.2.2.2.1 g hg) ((Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hR.2).2 g hg) _ _
  · obtain ⟨C, Ws, hW, hb⟩ := family_bound (RI I) R (io I) (hT.io_sm I)
    obtain ⟨C', Ws', hW', hb'⟩ := family_bound (RI J) R (io J) (hT.io_sm J)
    refine ⟨(∑ i, ∑ j, ‖Γ i j‖) * C * C', Ws, Ws', ?_, ?_⟩
    · intro W hWm
      rcases List.mem_append.1 hWm with h | h
      · exact hW W h
      · exact hW' W h
    · intro x hx y hy
      refine (norm_hh_le Γ R _ _ _ _ (fun c => hb c x hx) (fun c => hb' c y hy)).trans (le_of_eq ?_)
      ring

end GlobalTheory.TensForm
