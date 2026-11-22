module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffOnFubiniStudyProfileInvNormSqFirst

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular

open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (polyMax Mollifier molli regMax coordDiv)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart)

noncomputable section

def ell (t : ℝ) : ℝ := Real.log t⁻¹

def errE (C t : ℝ) : ℝ := C * Real.log (ell t) / ell t

variable {D : ℕ} {X : Type*} [TopologicalSpace X]

structure RegCharts (A : FinHolAtlas D X) where

  n : ℕ

  ψ : Fin n → OpenPartialHomeomorph X (Fin D → ℂ)
  compat : ∀ j, IsCompatChart A (ψ j)

  W : Fin n → Set (Fin D → ℂ)

  W' : Fin n → Set (Fin D → ℂ)

  W'' : Fin n → Set (Fin D → ℂ)
  isOpen_kappaOpenNeighbourhood : ∀ j, IsOpen (W j)
  isOpen_alt : ∀ j, IsOpen (W' j)
  isOpen_alt_alt : ∀ j, IsOpen (W'' j)
  W_subset : ∀ j, W j ⊆ (ψ j).target
  isCompact_closure_middle : ∀ j, IsCompact (closure (W' j))
  closure_W'_subset : ∀ j, closure (W' j) ⊆ W j
  closure_W''_subset : ∀ j, closure (W'' j) ⊆ W' j
  cover : ∀ x, ∃ j, x ∈ (ψ j).source ∧ ψ j x ∈ W'' j

  θ : LocPot X
  θ_pot : IsPotential A θ

  om : LocPot X
  om_pot : IsPotential A om
  om_pos : IsPosPot A om

  q : Fin n → (Fin D → ℂ) → ℝ
  q_smooth : ∀ j, ContDiffOn ℝ ∞ (q j) (W j)
  q_θ : ∀ j, ∀ y ∈ (ψ j).source, ψ j y ∈ W j → ∃ V : Set X, IsOpen V ∧ y ∈ V ∧ ∃ G : X → ℂ,
    A.HoloOn V G ∧ ∀ x ∈ V ∩ θ.U y ∩ (ψ j).source, ψ j x ∈ W j →
      θ.φ y x - q j (ψ j x) = (G x).re

namespace RegCharts

variable {A : FinHolAtlas D X} (R : RegCharts A)

def V'' (j : Fin R.n) : Set X := (R.ψ j).source ∩ R.ψ j ⁻¹' R.W'' j

def u (φ : X → ℝ) (j : Fin R.n) (z : Fin D → ℂ) : ℝ := R.q j z + φ ((R.ψ j).symm z)

end RegCharts

structure RegChartData (A : FinHolAtlas D X) extends RegCharts A where

  Yo : Set X
  isOpen_Yo : IsOpen Yo

  S : Fin n → Finset (Fin D)
  mem_Yo_iff : ∀ j, ∀ z ∈ W j, (ψ j).symm z ∈ Yo ↔ z ∉ coordDiv (S j)

  r : X → ℝ

  f : Fin n → (Fin D → ℂ) → ℝ
  f_cont : ∀ j, ContinuousOn (f j) (W j)
  f_bdd : ∀ j, ∃ B, ∀ z ∈ W j, |f j z| ≤ B
  r_chart : ∀ j, ∀ z ∈ W j \ coordDiv (S j),
    r ((ψ j).symm z) = Real.exp 1 + f j z - ∑ i ∈ S j, Real.log (‖z i‖ ^ 2)
  one_le_r : ∀ x ∈ Yo, 1 ≤ r x

  φ : X → ℝ
  φ_smooth : A.SmoothOn Yo φ
  psh : ∀ j, ReciprocityTheory.AnForm.A.IsPsh (W j \ coordDiv (S j)) (toRegCharts.u φ j)

  C : ℝ
  φ_le : ∀ x ∈ Yo, φ x ≤ C
  le_φ : ∀ x ∈ Yo, -(C * Real.log (r x)) ≤ φ x
  grad : ∀ j, ∀ z ∈ W j \ coordDiv (S j),
    ‖fderiv ℝ (toRegCharts.u φ j) z‖ ≤
      C * r ((ψ j).symm z) ^ C * Real.exp (r ((ψ j).symm z) / 2)

namespace PeriodPolydisc

variable {n a g : ℕ} (P : PeriodPolydisc n a g)

end PeriodPolydisc

section ProjectiveLine

open ReciprocityTheory.AnForm.M

@[reducible] def projLineCharts : RegCharts p1 where
  n := 2
  ψ := p1.chart
  compat := projLine_isCompatibleChart
  W _ := ball 0 2
  W' _ := ball 0 (3 / 2)
  W'' _ := ball 0 (5 / 4)
  isOpen_kappaOpenNeighbourhood _ := isOpen_ball
  isOpen_alt _ := isOpen_ball
  isOpen_alt_alt _ := isOpen_ball
  W_subset j := by rw [projLine_chart_target]; exact Set.subset_univ _
  isCompact_closure_middle _ := by
    rw [closure_ball _ (by norm_num)]; exact isCompact_closedBall _ _
  closure_W'_subset _ := closure_ball_subset_closedBall.trans (closedBall_subset_ball (by norm_num))
  closure_W''_subset _ :=
    closure_ball_subset_closedBall.trans (closedBall_subset_ball (by norm_num))
  cover x := by
    induction x with
    | infty =>
      refine ⟨1, show (OnePoint.infty : OnePoint ℂ) ∈ projectiveLineChartAtInfinity.source from OnePoint.infty_ne_coe 0, ?_⟩
      rw [projLine_chart_apply, mem_ball_zero_iff, norm_fin_one_eq_alt]
      show ‖(0 : ℂ)‖ < 5 / 4
      norm_num
    | coe z =>
      by_cases hz : ‖z‖ ≤ 1
      · refine ⟨0, ⟨z, rfl⟩, ?_⟩
        rw [projLine_chart_apply, mem_ball_zero_iff, norm_fin_one_eq_alt]
        show ‖z‖ < 5 / 4
        linarith
      · have hz0 : z ≠ 0 := by rintro rfl; simp at hz
        refine ⟨1, show (z : OnePoint ℂ) ∈ projectiveLineChartAtInfinity.source from
          fun h => hz0 (OnePoint.coe_injective h), ?_⟩
        rw [projLine_chart_apply, mem_ball_zero_iff, norm_fin_one_eq_alt]
        show ‖z⁻¹‖ < 5 / 4
        rw [norm_inv]
        have h1 : 1 < ‖z‖ := lt_of_not_ge hz
        have h2 : ‖z‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
        linarith
  θ := LocPot.ofFun 0
  θ_pot := isPotential_ofFun p1 0 (fun _ => contDiffOn_const)
  om := fsPot
  om_pot := projLine_isSmoothPotential
  om_pos := projLine_fubiniStudy_isPosPot
  q _ _ := 0
  q_smooth _ := contDiffOn_const
  q_θ _ _ _ _ := ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0, holoOn_const _ 0,
    fun x _ _ => by simp [LocPot.ofFun]⟩

end ProjectiveLine

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
