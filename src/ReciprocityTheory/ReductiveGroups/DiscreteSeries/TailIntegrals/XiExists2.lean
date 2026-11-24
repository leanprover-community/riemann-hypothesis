module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs
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

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem aAll_of (hb : AStepBase) (hs : AStepSucc) : ∀ k r : ℕ, 1 ≤ k → AAt k r := by
  intro k r hk
  induction r with
  | zero => exact hb k hk
  | succ r' ih => exact hs k (r' + 1) r' (by omega) hk ih

theorem bAll_of (hb : BStepBase) (hs : BStepSucc) :
    ∀ k r : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → BAt k r δ := by
  intro k r hk
  induction r with
  | zero => intro δ hδ _; exact hb k hk δ hδ
  | succ r' ih =>
    intro δ hδ hδ'
    exact hs k (r' + 1) r' (by omega) hk δ hδ hδ' (ih (δ / 4) (by positivity) (by linarith))

theorem xiExists_of (hA : ∀ k r : ℕ, 1 ≤ k → AAt k r) (hB : ∀ k r : ℕ, 1 ≤ k → BAt k r (1 / 2))
    (hC : CoefStep) (hX : XiIntStep) : XiExists := by
  intro k r Wp Wq _ _ _ _ _ _ D A hA'
  obtain ⟨eS, heS, hBs⟩ := hB k r D.k_pos
  have he0 : 0 < min eS (1 / 10 : ℝ) := lt_min heS (by norm_num)
  have adm : SAdm k r (fun l => s0 k r l - min eS (1 / 10)) := fun l => by
    simp only [sub_sub_cancel]; exact ⟨he0, min_le_right _ _⟩
  have adm' : ∀ l, 0 < s0 k r l - (s0 k r l - min eS (1 / 10)) ∧ s0 k r l - (s0 k r l - min eS (1 / 10)) ≤ eS :=
    fun l => by simp only [sub_sub_cancel]; exact ⟨he0, min_le_left _ _⟩
  exact ⟨xiN k r _, hC k r Wp Wq D A _ adm hA' (hA k r D.k_pos _ adm D.μG D.haarG A hA'),
    hX k r Wp Wq D _ adm (hBs _ adm' D.z D.z_mem D.T_pos D.μN D.haarN)
      (hBs _ adm' D.z' D.z'_mem D.T'_pos D.μN D.haarN)⟩

theorem xiExists_of_induction_steps (hAb : AStepBase) (hAs : AStepSucc) (hBb : BStepBase) (hBs : BStepSucc)
    (hC : CoefStep) (hX : XiIntStep) : XiExists :=
  xiExists_of (aAll_of hAb hAs) (fun k r hk => bAll_of hBb hBs k r hk (1 / 2) (by norm_num) le_rfl) hC hX

end ReciprocityTheory.ChartRestriction.DS.Xi
