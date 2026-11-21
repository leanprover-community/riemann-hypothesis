import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.ContDiffOnExpPartialHomeomorphSymm
import Formalism.PeriodIntegrals.IsLowUnitH

section
namespace CompanionTheory.D.Upq

open Matrix

set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

section Generic

variable (J : Matrix n n ℂ)

def lieJ : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X | Xᴴ * J + J * X = 0}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq, conjTranspose_add, Matrix.add_mul, Matrix.mul_add] at hX hY ⊢
    calc Xᴴ * J + Yᴴ * J + (J * X + J * Y) = (Xᴴ * J + J * X) + (Yᴴ * J + J * Y) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' r X hX := by
    simp only [Set.mem_ofPred_eq, conjTranspose_smul, star_trivial, Matrix.smul_mul,
      Matrix.mul_smul] at hX ⊢
    rw [← smul_add, hX, smul_zero]

theorem mem_lieJ {X : Matrix n n ℂ} : X ∈ lieJ J ↔ Xᴴ * J + J * X = 0 := Iff.rfl

variable {J}

theorem conjTranspose_mul_eq_of_mem {X : Matrix n n ℂ} (hX : X ∈ lieJ J) : Xᴴ * J = -(J * X) :=
  eq_neg_of_add_eq_zero_left hX

theorem commutator_mem_lieJ {X Y : Matrix n n ℂ} (hX : X ∈ lieJ J) (hY : Y ∈ lieJ J) :
    X * Y - Y * X ∈ lieJ J := by
  have hX' := conjTranspose_mul_eq_of_mem hX
  have hY' := conjTranspose_mul_eq_of_mem hY
  show (X * Y - Y * X)ᴴ * J + J * (X * Y - Y * X) = 0
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul,
    Matrix.mul_assoc Yᴴ Xᴴ J, hX', Matrix.mul_assoc Xᴴ Yᴴ J, hY', Matrix.mul_neg, Matrix.mul_neg,
    ← Matrix.mul_assoc Yᴴ J X, hY', ← Matrix.mul_assoc Xᴴ J Y, hX']
  simp only [Matrix.neg_mul, neg_neg, Matrix.mul_sub, Matrix.mul_assoc]
  abel

variable (J) in

def lieSubJ : LieSubalgebra ℝ (Matrix n n ℂ) :=
  { lieJ J with
    lie_mem' := fun {X Y} hX hY => by
      rw [Ring.lie_def]
      exact commutator_mem_lieJ hX hY }

@[simp] theorem mem_lieSubJ {X : Matrix n n ℂ} : X ∈ lieSubJ J ↔ X ∈ lieJ J := Iff.rfl


end Generic

section Involutive

variable {J : Matrix n n ℂ} (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ

theorem mul_J_J (Z : Matrix n n ℂ) : Z * J * J = Z := by
  rw [Matrix.mul_assoc, hJ, Matrix.mul_one]

theorem J_J_mul (Z : Matrix n n ℂ) : J * (J * Z) = Z := by
  rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]

theorem mem_lieJ_iff {X : Matrix n n ℂ} : X ∈ lieJ J ↔ Xᴴ = -(J * X * J) := by
  constructor
  · intro h
    calc Xᴴ = Xᴴ * J * J := (mul_J_J hJ _).symm
      _ = -(J * X * J) := by rw [conjTranspose_mul_eq_of_mem h, Matrix.neg_mul]
  · intro h
    show Xᴴ * J + J * X = 0
    rw [h, Matrix.neg_mul, mul_J_J hJ, neg_add_cancel]




end Involutive

section Cartan

variable (J : Matrix n n ℂ)

def kJ : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X | X ∈ lieJ J ∧ X * J = J * X}
  add_mem' {X Y} hX hY := ⟨add_mem hX.1 hY.1, by rw [Matrix.add_mul, Matrix.mul_add, hX.2, hY.2]⟩
  zero_mem' := ⟨zero_mem _, by simp⟩
  smul_mem' c X hX := ⟨Submodule.smul_mem _ c hX.1, by
    rw [Matrix.smul_mul, Matrix.mul_smul, hX.2]⟩

def pJ : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X | X ∈ lieJ J ∧ X * J = -(J * X)}
  add_mem' {X Y} hX hY := ⟨add_mem hX.1 hY.1, by
    rw [Matrix.add_mul, Matrix.mul_add, hX.2, hY.2, neg_add]⟩
  zero_mem' := ⟨zero_mem _, by simp⟩
  smul_mem' c X hX := ⟨Submodule.smul_mem _ c hX.1, by
    rw [Matrix.smul_mul, Matrix.mul_smul, hX.2, smul_neg]⟩





variable {J} (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ








end Cartan

section Complexification

variable (J : Matrix n n ℂ)

def thetaG (M : Matrix n n ℂ) : Matrix n n ℂ := -(J * Mᴴ * J)

noncomputable def reG (M : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℂ) • (M + thetaG J M)

noncomputable def imG (M : Matrix n n ℂ) : Matrix n n ℂ := (-(Complex.I / 2)) • (M - thetaG J M)

variable {J}




variable (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ hJh

theorem thetaG_thetaG (M : Matrix n n ℂ) : thetaG J (thetaG J M) = M := by
  simp only [thetaG, conjTranspose_neg, conjTranspose_mul, hJh, conjTranspose_conjTranspose,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg, ← Matrix.mul_assoc, hJ, Matrix.one_mul, mul_J_J hJ]

omit hJh in

theorem mem_lieJ_iff_thetaG {X : Matrix n n ℂ} : X ∈ lieJ J ↔ thetaG J X = X := by
  rw [mem_lieJ_iff hJ, thetaG]
  constructor
  · intro h
    rw [h]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, hJ, Matrix.one_mul,
      mul_J_J hJ]
  · intro h
    calc Xᴴ = J * (J * Xᴴ * J) * J := by
          simp only [← Matrix.mul_assoc, hJ, Matrix.one_mul, mul_J_J hJ]
      _ = -(J * (-(J * Xᴴ * J)) * J) := by simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]
      _ = -(J * X * J) := by rw [h]



omit hJ hJh in
theorem reG_add_I_smul_imG (M : Matrix n n ℂ) : M = reG J M + Complex.I • imG J M := by
  rw [reG, imG, smul_smul, show Complex.I * -(Complex.I / 2) = 1 / 2 by
    rw [mul_neg, ← mul_div_assoc, Complex.I_mul_I, neg_div, neg_neg], ← smul_add,
    add_add_sub_cancel, ← two_smul ℂ M, smul_smul]
  norm_num



end Complexification

end CompanionTheory.D.Upq
end

section
namespace CompanionTheory.D.Upq

open Matrix NormedSpace PI.UpqRep
open scoped Matrix.Norms.L2Operator Manifold

section General

variable {m : Type*} [Fintype m] [DecidableEq m] {J : Matrix m m ℂ}

theorem exp_conj_J (hJJ : J * J = 1) (X : Matrix m m ℂ) : exp (J * X * J) = J * exp X * J := by
  have hu : IsUnit J := ⟨⟨J, J, hJJ, hJJ⟩, rfl⟩
  have hinv : J⁻¹ = J := inv_eq_left_inv hJJ
  have := Matrix.exp_conj J X hu
  rwa [hinv] at this

theorem exp_mul_exp_neg' (X : Matrix m m ℂ) : exp X * exp (-X) = 1 :=
  (expUnit ℝ (Matrix m m ℂ) X).mul_inv

theorem exp_neg_mul_exp' (X : Matrix m m ℂ) : exp (-X) * exp X = 1 :=
  (expUnit ℝ (Matrix m m ℂ) X).inv_mul

theorem isExpLieAlgebra_of_J (hJJ : J * J = 1) (G : Subgroup (Matrix m m ℂ)ˣ)
    (hG : ∀ g : (Matrix m m ℂ)ˣ, g ∈ G ↔ (g : Matrix m m ℂ)ᴴ * J * g = J) :
    IsExpLieAlgebra G (lieJ J) where
  expUnit_mem X hX := by
    have h1 : -(J * X * J) = J * (-X) * J := by rw [Matrix.mul_neg, Matrix.neg_mul]
    rw [hG, coe_expUnit, ← Matrix.exp_conjTranspose, (mem_lieJ_iff hJJ).1 hX, h1, exp_conj_J hJJ,
      mul_J_J hJJ (J * exp (-X)), Matrix.mul_assoc, exp_neg_mul_exp', Matrix.mul_one]
  exists_nhds := by
    obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 (expPartialHomeomorph ℝ (Matrix m m ℂ)).open_source
      (0 : Matrix m m ℂ) (zero_mem_expPartialHomeomorph_source ℝ (Matrix m m ℂ))
    refine ⟨Metric.ball (0 : Matrix m m ℂ) ε ∩
      (fun X : Matrix m m ℂ => Xᴴ) ⁻¹' Metric.ball (0 : Matrix m m ℂ) ε ∩
      (fun X : Matrix m m ℂ => -(J * X * J)) ⁻¹' Metric.ball (0 : Matrix m m ℂ) ε, ?_, ?_, ?_, ?_⟩
    · exact (Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage
        continuous_id.matrix_conjTranspose)).inter (Metric.isOpen_ball.preimage
        ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).neg)
    · refine ⟨⟨Metric.mem_ball_self εpos, ?_⟩, ?_⟩ <;>
        simpa using Metric.mem_ball_self (x := (0 : Matrix m m ℂ)) εpos
    · exact fun X hX => hε hX.1.1
    · intro X hX hGX
      rw [hG, coe_expUnit] at hGX
      rw [mem_lieJ_iff hJJ]
      have h1 : (exp X)ᴴ = J * exp (-X) * J := by
        calc (exp X)ᴴ = (exp X)ᴴ * J * (exp X * exp (-X)) * J := by
              rw [exp_mul_exp_neg', Matrix.mul_one, mul_J_J hJJ]
          _ = (exp X)ᴴ * J * exp X * exp (-X) * J := by simp only [Matrix.mul_assoc]
          _ = J * exp (-X) * J := by rw [hGX]
      have h2 : exp Xᴴ = exp (-(J * X * J)) := by
        rw [Matrix.exp_conjTranspose, h1, show -(J * X * J) = J * (-X) * J by
          rw [Matrix.mul_neg, Matrix.neg_mul], exp_conj_J hJJ]
      exact (expPartialHomeomorph ℝ (Matrix m m ℂ)).injOn (hε hX.1.2) (hε hX.2) h2

end General

section UJ

variable {n : ℕ} (ε : Fin n → Bool)

theorem mem_UJ_iff (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    g ∈ UJ ε ↔ (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * g = Jm ε := Iff.rfl

theorem isExpLieAlgebra_UJ : IsExpLieAlgebra (UJ ε) (lieJ (Jm ε)) :=
  isExpLieAlgebra_of_J (Jm_mul_self ε) _ (mem_UJ_iff ε)

noncomputable instance chartedSpace_UJ : ChartedSpace (lieJ (Jm ε)) (UJ ε) :=
  (isExpLieAlgebra_UJ ε).chartedSpace

instance lieGroup_UJ (k : WithTop ℕ∞) : LieGroup 𝓘(ℝ, lieJ (Jm ε)) k (UJ ε) :=
  (isExpLieAlgebra_UJ ε).lieGroup k

theorem isCompact_Kset : IsCompact (Kset ε) := by
  have hcl : IsClosed (Kset ε) := by
    refine IsClosed.inter ?_ ?_
    · have : (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
          {u | star u * u = 1} := by ext u; exact Matrix.mem_unitaryGroup_iff'
      rw [this]
      exact isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const
    · exact isClosed_eq (continuous_id.matrix_mul continuous_const)
        (continuous_const.matrix_mul continuous_id)
  have hB : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hB.of_isClosed_subset hcl ?_
  rintro u ⟨hu, -⟩ i - j -
  simpa using entry_norm_bound_of_unitary hu i j

theorem isCompact_KG : IsCompact (KG ε : Set (UJ ε)) := by
  have hE := (isClosedEmbeddingMatrix n ε).1
  have : (KG ε : Set (UJ ε)) = (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
      Matrix (Fin n) (Fin n) ℂ)) ⁻¹' Kset ε := rfl
  rw [this]
  exact hE.isCompact_preimage (isCompact_Kset ε)

instance compactSpace_KG : CompactSpace (KG ε) :=
  isCompact_iff_compactSpace.1 (isCompact_KG ε)

end UJ

end CompanionTheory.D.Upq
end
