import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.SimilitudeFactorFormGroupBoundedOfTestSupport
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.AffineChartParamCoverProjectiveLine
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GramSignatureTwoOneEntryZeroZero

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.PieceModel

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P MeasureTheory GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open GlobalTheory.CompanionTheory.Ar.PB.LineModel

instance uniqueLow : Unique (LowEnt Unit 2) where
  default := ((), ⟨(1, 0), by decide⟩)
  uniq := by decide

def q1 : LowEnt Unit 2 ≃ Fin 1 := Equiv.ofUnique _ _

theorem lowMat_two (q : LowEnt Unit 2 ≃ Fin 1) (z : Fin 1 → ℂ) (τ : Unit) : lowMat q z τ = !![1, 0; z 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [lowMat]
  congr 1; exact Subsingleton.elim _ _

theorem cellDom_two_two (q : LowEnt Unit 2 ≃ Fin 1) : cellDom 2 q = Set.univ := by
  refine Set.eq_univ_of_forall fun z τ => ?_
  rw [lowMat_two]
  exact (chart_flag (z 0)).2.2.2.1 () (z 0 : ℂ) ⟨_, rfl⟩





def lineUnif : PieceUnif sysFlag 2 1 where
  q _ := q1
  π _ := projectiveLineChartAtZero.symm
  FF _ := Set.univ
  mem_open _ z _ h := OnePoint.coe_ne_infty (z 0) ((mem_boundary_projectiveLine _).1 h)
  param _ z _ := ⟨Set.univ, trivial, by rw [cellDom_two_two], affine_chart_param_cover_projective_line.1 0⟩
  pot _ z _ p := by
    refine ⟨fun _ => 0, analyticAt_const, Eventually.of_forall fun z' => ?_⟩
    rw [lowMat_two]
    obtain ⟨⟨⟩, i⟩ := p
    fin_cases i
    · show (flagTh ((), 0)).φ (z 0 : ℂ) (z' 0 : ℂ) + 0 = stepPot 2 2 0 !![1, 0; z' 0, 1] + 0
      rw [flagTh_zero, fsPot_φ_coe, Model.stepPot_pos_zero]
      simp
    · show (flagTh ((), 1)).φ (z 0 : ℂ) (z' 0 : ℂ) + 0 =
        gramLog (sigForm 2 2) 2 (frame () (z' 0 : ℂ)) - gramLog (sigForm 2 2) 0 (frame () (z' 0 : ℂ)) + 0
      rw [flagTh_one, gramLog, gramLog, det_head_zero, det_head_two, det_gram_frame]
      simp [sigForm, LocPot.ofFun]
  meas _ := MeasurableSet.univ
  sub _ := by rw [cellDom_two_two]
  inj _ := projectiveLineChartAtZero.symm.injOn
  disj k k' h := absurd (Subsingleton.elim k k') h
  cover := by
    intro j
    refine measure_mono_null ?_ (affine_chart_param_cover_projective_line.2.2.2 j)
    refine Set.inter_subset_inter_right _ (Set.preimage_mono (Set.compl_subset_compl.2 ?_))
    refine Set.iUnion_subset fun n => ?_
    exact (Set.image_mono (Set.subset_univ _)).trans (Set.subset_iUnion (fun _ : Fin 1 => projectiveLineChartAtZero.symm '' Set.univ) 0)






end GlobalTheory.CompanionTheory.Ar.Cmp.PieceModel
