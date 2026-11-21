import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart

open Matrix

noncomputable section

def imPart {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℝ :=
  M.map Complex.im

def cplx {ι κ : Type*} (M : Matrix ι κ ℝ) : Matrix ι κ ℂ :=
  M.map (fun x : ℝ => (x : ℂ))

def qf {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℝ) (w : ι → ℂ) : ℝ :=
  (star w ⬝ᵥ (cplx Q *ᵥ w)).re

def realIP {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (v w : Fin g → ℂ) : ℝ :=
  (star v ⬝ᵥ (cplx Y⁻¹ *ᵥ w)).re

def yNorm {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (w : Fin g → ℂ) : ℝ :=
  Real.sqrt (qf Y⁻¹ w)

def punctured {n a : ℕ} (ha : a ≤ n) (U : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {z | z ∈ U ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0}

def lwP₂ (z : ℂ) : ℝ :=
  Real.log (1 / ‖z‖) / (2 * Real.pi)

def chartY {n a g : ℕ} (ha : a ≤ n) (tau0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℝ :=
  imPart (tau0 z) + ∑ i : Fin a, lwP₂ (z (Fin.castLE ha i)) • B i

def chartR {n a : ℕ} (ha : a ≤ n) (z : Fin n → ℂ) : ℝ :=
  Real.exp 1 + ∑ i : Fin a, Real.log (1 / ‖z (Fin.castLE ha i)‖ ^ 2)

def gramLogDet {g k : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (F : Matrix (Fin g) (Fin k) ℂ) : ℝ :=
  Real.log (Fᴴ * cplx Y⁻¹ * F).det.re

structure PeriodChartData (n a g m k : ℕ) where
  U : Set (Fin n → ℂ)
  isOpen_U : IsOpen U
  U_sub : U ⊆ Metric.ball 0 1
  a_le : a ≤ n
  tau0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ
  tau_analyticOn : ∀ j l : Fin g, AnalyticOnNhd ℂ (fun z => tau0 z j l) U
  tau_transpose_eq : ∀ z ∈ U, (tau0 z)ᵀ = tau0 z
  B : Fin a → Matrix (Fin g) (Fin g) ℝ
  B_psd : ∀ i, (B i).PosSemidef
  c : ℝ
  c_pos : 0 < c
  Y_ge : ∀ z ∈ punctured a_le U, (chartY a_le tau0 B z - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef
  V : Set (Fin m → ℂ)
  isOpen_V : IsOpen V
  f : (Fin n → ℂ) × (Fin m → ℂ) → Matrix (Fin g) (Fin k) ℂ
  f_analytic : ∀ (j : Fin g) (l : Fin k), AnalyticOnNhd ℂ (fun p => f p j l) (U ×ˢ V)
  f_rank : ∀ p ∈ U ×ˢ V, (f p).rank = k
  K : Set ((Fin n → ℂ) × (Fin m → ℂ))
  K_compact : IsCompact K
  K_sub : K ⊆ U ×ˢ V

namespace PeriodChartData

variable {n a g m k : ℕ} (D : PeriodChartData n a g m k)

def Ustar : Set (Fin n → ℂ) := punctured D.a_le D.U

def Y (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℝ := chartY D.a_le D.tau0 D.B z

def r (z : Fin n → ℂ) : ℝ := chartR D.a_le z

def u (p : (Fin n → ℂ) × (Fin m → ℂ)) : ℝ := gramLogDet (D.Y p.1) (D.f p)

def tau (l : Fin a → ℂ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  D.tau0 z + ∑ i : Fin a, (l i / (2 * (Real.pi : ℂ) * Complex.I)) • cplx (D.B i)

end PeriodChartData

def splitPt {n m : ℕ} (x : Fin (n + m) → ℂ) : (Fin n → ℂ) × (Fin m → ℂ) :=
  (fun i => x (Fin.castAdd m i), fun j => x (Fin.natAdd n j))

def M1.Statement : Prop :=
  ∀ (n a g m k : ℕ) (D : PeriodChartData n a g m k), ∃ C : ℝ,
    ∀ p ∈ D.K, p.1 ∈ D.Ustar →
      (D.Y p.1 - D.c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef ∧
      ((C * D.r p.1) • (1 : Matrix (Fin g) (Fin g) ℝ) - D.Y p.1).PosSemidef ∧
      -(C * Real.log (D.r p.1)) ≤ D.u p ∧ D.u p ≤ C

def M2.Statement : Prop :=
  ∀ (n a g m k : ℕ) (D : PeriodChartData n a g m k), ∃ C : ℝ,
    ∀ p ∈ D.K, p.1 ∈ D.Ustar →
      DifferentiableAt ℝ D.u p ∧
        ‖fderiv ℝ D.u p‖ ≤ C * D.r p.1 ^ C * Real.exp (D.r p.1 / 2)

structure PshData (N g k : ℕ) where
  W : Set (Fin N → ℂ)
  isOpen_kappaOpenNeighbourhood : IsOpen W
  tau : (Fin N → ℂ) → Matrix (Fin g) (Fin g) ℂ
  tau_analytic : ∀ j l : Fin g, AnalyticOnNhd ℂ (fun z => tau z j l) W
  tau_symm : ∀ z ∈ W, (tau z)ᵀ = tau z
  im_posDef : ∀ z ∈ W, (imPart (tau z)).PosDef
  F : (Fin N → ℂ) → Matrix (Fin g) (Fin k) ℂ
  F_analytic : ∀ (j : Fin g) (l : Fin k), AnalyticOnNhd ℂ (fun z => F z j l) W
  F_rank : ∀ z ∈ W, (F z).rank = k

def M3.Statement : Prop :=
  ∀ (N g k : ℕ) (P : PshData N g k),
    ReciprocityTheory.AnForm.A.IsPsh P.W (fun z => gramLogDet (imPart (P.tau z)) (P.F z))

def PeriodMatrixChart.Statement : Prop :=
  ∀ (n a g m k : ℕ) (D : PeriodChartData n a g m k),
    ReciprocityTheory.AnForm.A.IsPsh (splitPt ⁻¹' (D.Ustar ×ˢ D.V)) (fun x => D.u (splitPt x))

def M4.Statement : Prop :=
  ∀ (r s : ℕ) (Y : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ), Y.PosDef → ∀ v : Fin s → ℂ,
    IsLeast (Set.range fun x : Fin r → ℂ => qf Y⁻¹ (Sum.elim x v)) (qf (Y.toBlocks₂₂)⁻¹ v)

def periodLattice {g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ) : Submodule ℤ (Fin g → ℂ) :=
  Submodule.span ℤ (Set.range (fun j : Fin g => (Pi.single j (1 : ℂ) : Fin g → ℂ)) ∪
    Set.range (fun j : Fin g => T *ᵥ (Pi.single j (1 : ℂ) : Fin g → ℂ)))

def firstBlock {g r : ℕ} (hr : r ≤ g) : Submodule ℤ (Fin g → ℂ) :=
  Submodule.span ℤ (Set.range (fun j : Fin r => (Pi.single (Fin.castLE hr j) (1 : ℂ) : Fin g → ℂ)))

def succMin {g : ℕ} (len : (Fin g → ℂ) → ℝ) (L : Submodule ℤ (Fin g → ℂ)) (j : ℕ) : ℝ :=
  sInf {t : ℝ | j ≤ Module.finrank ℝ (Submodule.span ℝ {v | v ∈ L ∧ len v ≤ t})}

def gramCovol {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (I : Submodule ℤ (Fin g → ℂ)) : ℝ :=
  sInf {x : ℝ | ∃ (q : ℕ) (b : Fin q → Fin g → ℂ), LinearIndependent ℤ b ∧
    Submodule.span ℤ (Set.range b) = I ∧
    x = Real.sqrt (Matrix.of (fun i j => realIP Y (b i) (b j))).det}

structure ToricBlock {n a g m k : ℕ} (D : PeriodChartData n a g m k) (r : ℕ) : Prop where
  r_le : r ≤ g
  B_support : ∀ (i : Fin a) (j l : Fin g), (r ≤ j.val ∨ r ≤ l.val) → D.B i j l = 0
  sum_posDef : ((∑ i, D.B i).submatrix (Fin.castLE r_le) (Fin.castLE r_le)).PosDef

def M5.Statement : Prop :=
  ∀ (n a g m k : ℕ) (D : PeriodChartData n a g m k) (r : ℕ) (T : ToricBlock D r),
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ p ∈ D.K, p.1 ∈ D.Ustar → ∀ l : Fin a → ℂ,
        (∀ i, Complex.exp (l i) = p.1 (Fin.castLE D.a_le i)) →
        (∀ w ∈ periodLattice (D.tau l p.1), w ∉ firstBlock T.r_le → c₁ ≤ yNorm (D.Y p.1) w) ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ r →
          succMin (yNorm (D.Y p.1)) (firstBlock T.r_le) j ≤ D.c ^ (-(1 / 2 : ℝ))) ∧
        (∀ I : Submodule ℤ (Fin g → ℂ), I ≤ periodLattice (D.tau l p.1) →
          c₂ * gramCovol (D.Y p.1) (firstBlock T.r_le) ≤ gramCovol (D.Y p.1) I)

def exampleChart : PeriodChartData 1 1 2 1 2 where
  U := Metric.ball 0 1
  isOpen_U := Metric.isOpen_ball
  U_sub := subset_rfl
  a_le := le_rfl
  tau0 := fun _ => Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  tau_analyticOn := fun _ _ => analyticOnNhd_const
  tau_transpose_eq := fun _ _ => by simp [transpose_smul]
  B := fun _ => diagonal ![1, 0]
  B_psd := fun _ => by
    rw [posSemidef_diagonal_iff]
    intro i; fin_cases i <;> simp
  c := 1
  c_pos := one_pos
  Y_ge := by
    intro z hz
    have hb : ‖z 0‖ < 1 := by
      have h1 : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz.1
      exact lt_of_le_of_lt (norm_le_pi_norm z 0) h1
    have hw : 0 ≤ lwP₂ (z 0) := by
      unfold lwP₂
      apply div_nonneg _ (by positivity)
      apply Real.log_nonneg
      have hz0 : z 0 ≠ 0 := by simpa using hz.2 0
      rw [one_le_div (norm_pos_iff.mpr hz0)]
      exact hb.le
    have heq : chartY le_rfl (fun _ => Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        (fun _ => diagonal ![1, 0]) z - (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) =
        diagonal ![lwP₂ (z 0), 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [chartY, imPart]
    rw [heq, posSemidef_diagonal_iff]
    intro i; fin_cases i <;> simp [hw]
  V := Set.univ
  isOpen_V := isOpen_univ
  f := fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  f_analytic := fun _ _ => analyticOnNhd_const
  f_rank := fun _ _ => by simp [Matrix.rank_one]
  K := {((fun _ => (1 / 2 : ℂ)), (fun _ => (0 : ℂ)))}
  K_compact := isCompact_singleton
  K_sub := by
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨?_, Set.mem_univ _⟩
    rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff (by norm_num)]
    intro i; norm_num



def examplePsh : PshData 1 2 2 where
  W := Set.univ
  isOpen_kappaOpenNeighbourhood := isOpen_univ
  tau := fun _ => Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  tau_analytic := fun _ _ => analyticOnNhd_const
  tau_symm := fun _ _ => by simp [transpose_smul]
  im_posDef := by
    intro z _
    have : imPart (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [imPart]
    rw [this]
    exact PosDef.one
  F := fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  F_analytic := fun _ _ => analyticOnNhd_const
  F_rank := fun _ _ => by simp [Matrix.rank_one]


end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart
end

section
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
end
