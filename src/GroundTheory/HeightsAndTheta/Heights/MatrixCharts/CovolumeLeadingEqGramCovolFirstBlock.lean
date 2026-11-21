import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.IsOpenKappaOpenNeighbourhood
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart

open Matrix

noncomputable section

theorem unitPolydisc_eq_ball (n : ℕ) :
    GroundTheory.Heights₂.Heights.unitPolydisc n = Metric.ball (0 : Fin n → ℂ) 1 := by
  ext z
  simp [GroundTheory.Heights₂.Heights.unitPolydisc, Metric.mem_ball, dist_zero_right,
    pi_norm_lt_iff one_pos]

theorem cuspTime_eq_logWeight {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) (j : Fin a) :
    GroundTheory.Heights₂.Heights.cuspTime h z j = lwP₂ (z (Fin.castLE h j)) := by
  simp only [GroundTheory.Heights₂.Heights.cuspTime, GroundTheory.Heights₂.Heights.cuspCoord, lwP₂, one_div]
  ring


theorem chartImag_eq_chartY {n a g : ℕ} (h : a ≤ n)
    (τ0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℝ)
    (z : Fin n → ℂ) : GroundTheory.Heights₂.Heights.chartImag h τ0 B z = chartY h τ0 B z := by
  simp only [GroundTheory.Heights₂.Heights.chartImag, chartY, imPart, cuspTime_eq_logWeight]



theorem hermValue_eq_qf {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (w : ι → ℂ) :
    GroundTheory.Heights₂.Heights.hermValue A w = qf A w := rfl




namespace PeriodChartData

def ofBundled (D : GroundTheory.Heights₂.Heights.PeriodChartData) :
    PeriodChartData D.n D.a D.g D.m D.rk where
  U := D.U
  isOpen_U := D.isOpen_U
  U_sub := by rw [← unitPolydisc_eq_ball]; exact D.U_subset
  a_le := D.a_le
  tau0 := D.τ0
  tau_analyticOn := D.τ0_analytic
  tau_transpose_eq := D.τ0_symm
  B := D.B
  B_psd := D.B_psd
  c := D.c
  c_pos := D.c_pos
  Y_ge := fun z hz => by rw [← chartImag_eq_chartY]; exact D.Y_ge z hz
  V := D.V
  isOpen_V := D.isOpen_V
  f := D.f
  f_analytic := D.f_analytic
  f_rank := D.f_rank
  K := D.K
  K_compact := D.isCompact_K
  K_sub := D.K_subset

def bundle {n a g m k : ℕ} (D : PeriodChartData n a g m k) :
    GroundTheory.Heights₂.Heights.PeriodChartData where
  n := n
  m := m
  g := g
  a := a
  rk := k
  a_le := D.a_le
  U := D.U
  isOpen_U := D.isOpen_U
  U_subset := by rw [unitPolydisc_eq_ball]; exact D.U_sub
  τ0 := D.tau0
  τ0_analytic := D.tau_analyticOn
  τ0_symm := D.tau_transpose_eq
  B := D.B
  B_psd := D.B_psd
  c := D.c
  c_pos := D.c_pos
  Y_ge := fun z hz => by rw [chartImag_eq_chartY]; exact D.Y_ge z hz
  V := D.V
  isOpen_V := D.isOpen_V
  f := D.f
  f_analytic := D.f_analytic
  f_rank := D.f_rank
  K := D.K
  isCompact_K := D.K_compact
  K_subset := D.K_sub

section ofBundled

variable (D : GroundTheory.Heights₂.Heights.PeriodChartData)

@[simp] theorem ofBundled_U : (ofBundled D).U = D.U := rfl
@[simp] theorem periodChartData_ofBundled_tau : (ofBundled D).tau0 = D.τ0 := rfl
@[simp] theorem ofBundled_B : (ofBundled D).B = D.B := rfl
@[simp] theorem ofBundled_c : (ofBundled D).c = D.c := rfl
@[simp] theorem ofBundled_V : (ofBundled D).V = D.V := rfl
@[simp] theorem ofBundled_f : (ofBundled D).f = D.f := rfl
@[simp] theorem ofBundled_K : (ofBundled D).K = D.K := rfl






end ofBundled

section bundle

variable {n a g m k : ℕ} (D : PeriodChartData n a g m k)

@[simp] theorem bundle_n : D.bundle.n = n := rfl
@[simp] theorem bundle_a : D.bundle.a = a := rfl
@[simp] theorem bundle_g : D.bundle.g = g := rfl
@[simp] theorem bundle_m : D.bundle.m = m := rfl
@[simp] theorem bundle_rk : D.bundle.rk = k := rfl
theorem bundle_τ0 : D.bundle.τ0 = D.tau0 := rfl







end bundle

theorem bundle_ofBundled (D : GroundTheory.Heights₂.Heights.PeriodChartData) : (ofBundled D).bundle = D := by
  cases D
  rfl

def equiv : GroundTheory.Heights₂.Heights.PeriodChartData ≃ Σ n a g m k : ℕ, PeriodChartData n a g m k where
  toFun D := ⟨D.n, D.a, D.g, D.m, D.rk, ofBundled D⟩
  invFun E := E.2.2.2.2.2.bundle
  left_inv D := bundle_ofBundled D
  right_inv := by rintro ⟨n, a, g, m, k, E⟩; rfl

end PeriodChartData

namespace ToricBlock

theorem ofBundled {D : GroundTheory.Heights₂.Heights.PeriodChartData} (T : GroundTheory.Heights₂.Heights.ToricBlock D) :
    ToricBlock (PeriodChartData.ofBundled D) T.r where
  r_le := T.r_le
  B_support := T.support
  sum_posDef := T.pos

def toBundled {D : GroundTheory.Heights₂.Heights.PeriodChartData} {r : ℕ}
    (T : ToricBlock (PeriodChartData.ofBundled D) r) : GroundTheory.Heights₂.Heights.ToricBlock D where
  r := r
  r_le := T.r_le
  support := T.B_support
  pos := T.sum_posDef


def equiv (D : GroundTheory.Heights₂.Heights.PeriodChartData) :
    GroundTheory.Heights₂.Heights.ToricBlock D ≃ {r : ℕ // ToricBlock (PeriodChartData.ofBundled D) r} where
  toFun T := ⟨T.r, ofBundled T⟩
  invFun T := toBundled T.2
  left_inv T := by cases T; rfl
  right_inv T := rfl


end ToricBlock

namespace PshData

def ofSiegelFamily {N g k : ℕ} (S : GroundTheory.Heights₂.Heights.SiegelFamily N g k) : PshData N g k where
  W := S.W
  isOpen_kappaOpenNeighbourhood := S.isOpen_kappaOpenNeighbourhood
  tau := S.τ
  tau_analytic := S.τ_analytic
  tau_symm := S.τ_symm
  im_posDef := S.im_posDef
  F := S.f
  F_analytic := S.f_analytic
  F_rank := S.f_rank

def toSiegelFamily {N g k : ℕ} (P : PshData N g k) : GroundTheory.Heights₂.Heights.SiegelFamily N g k where
  W := P.W
  isOpen_kappaOpenNeighbourhood := P.isOpen_kappaOpenNeighbourhood
  τ := P.tau
  τ_analytic := P.tau_analytic
  τ_symm := P.tau_symm
  im_posDef := P.im_posDef
  f := P.F
  f_analytic := P.F_analytic
  f_rank := P.F_rank

def equiv (N g k : ℕ) : GroundTheory.Heights₂.Heights.SiegelFamily N g k ≃ PshData N g k where
  toFun := ofSiegelFamily
  invFun := toSiegelFamily
  left_inv S := by cases S; rfl
  right_inv P := by cases P; rfl



end PshData








def realIPForm {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) : LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (realIP Y)
    (fun v v' w => by simp [realIP, star_add, add_dotProduct])
    (fun c v w => by simp [realIP, star_smul, smul_dotProduct])
    (fun v w w' => by simp [realIP, mulVec_add, dotProduct_add])
    (fun c v w => by simp [realIP, mulVec_smul, dotProduct_smul])






end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart
