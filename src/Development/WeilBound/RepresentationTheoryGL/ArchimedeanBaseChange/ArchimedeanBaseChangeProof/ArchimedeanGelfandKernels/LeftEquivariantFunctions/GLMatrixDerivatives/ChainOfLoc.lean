module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevIntegrationByParts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Loc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

open scoped Matrix.Norms.Elementwise

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) :=
  isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const

theorem rd_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) (X : Mat n) :
    Set.EqOn (Rd X f) (Rd X f') U := by
  intro x hx
  simp only [Rd]
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h)]

theorem eu_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) (s : Bool) (a b : Fin n) :
    Set.EqOn (Eu s a b f) (Eu s a b f') U := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply]
  rw [rd_congr hU h _ hx, rd_congr hU h _ hx]

theorem epow_congr {U : Set (Mat n)} (hU : IsOpen U) (s : Bool) (m : ℕ) : ∀ (a b : Fin n) {f f' : Mat n → V},
    Set.EqOn f f' U → Set.EqOn (Epow s m a b f) (Epow s m a b f') U := by
  intros
  apply _root_.GlobalTheory.CompanionTheory.WaveAll.Epow_congr <;> assumption

theorem gel_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : Set.EqOn f f' U) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m f) (gel s m f') U := by
  intro x hx
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_congr hU s m a a h hx

theorem zop_congr {U : Set (Mat n)} (hU : IsOpen U) : ∀ (w : List (Bool × ℕ)) {f f' : Mat n → V},
    Set.EqOn f f' U → Set.EqOn (zOp w f) (zOp w f') U := by
  intro w
  induction w with
  | nil => intro f f' h; exact h
  | cons p w ih => intro f f' h; exact gel_congr hU (ih h) p.1 p.2

theorem integrable_cpt (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : Mat n → W) (hF : ContinuousOn F (GLs n))
    (hc : Cpt F) : Integrable (fun y : G n => F y.val) μ := by
  apply _root_.GlobalTheory.CompanionTheory.WeightIbp.integrable_of_continuousOn <;> assumption

end PositivityTheory.RgBcC.LfSt.ChainPf.Loc
