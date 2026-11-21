import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionGradedIsotropicFlag

section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResLineLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

omit [NumberField E] in

theorem initCols_zero {r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) : initCols X 0 = col X :=
  Matrix.ext fun i j => congrArg (X i) (Fin.ext (Nat.lt_one_iff.1 j.2))

theorem mem_frameStab_of_parFlag {s : ℕ} {C : Matrix (Fin n) (Fin s) E} {L : Matrix (Fin s) (Fin n) E} (hL : L * C = 1)
    {d : Fin s → ℕ} {g : GAd σ J} (hg : g ∈ GlobalTheory.UAut.parFlag σ J C d) : g ∈ frameStab σ J C ⊤ := by
  obtain ⟨⟨B, -, e⟩, B', -, e'⟩ := hg
  have hL' : adMat F L * adMat F C = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMM : (matHom _ σ J g).1 * (matHom _ σ J g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hBB : B * B' = 1 := by
    calc B * B' = adMat F L * (adMat F C * B) * B' := by rw [← Matrix.mul_assoc, hL', Matrix.one_mul]
      _ = adMat F L * ((matHom _ σ J g).1 * ((matHom _ σ J g⁻¹).1 * adMat F C)) := by
          simp only [← e, e', Matrix.mul_assoc]
      _ = 1 := by rw [← Matrix.mul_assoc (matHom _ σ J g).1, hMM, Matrix.one_mul, hL']
  exact ⟨⟨B, B', hBB, mul_eq_one_comm.1 hBB⟩, Subgroup.mem_top _, e⟩

omit [NumberField E] in

theorem unipRad_fix {s : ℕ} {C : Matrix (Fin n) (Fin s) E} {u : GAd σ J} (hu : u ∈ unipRad σ J C) :
    (matHom _ σ J u).1 * adMat F C = adMat F C := by
  have : unipRad σ J C ≤ frameStab σ J C ⊥ := (Subgroup.closure_le _).2 fun g hg => ⟨1, one_mem _, by
    have h := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
    rw [h, Units.val_one, Matrix.mul_one]⟩
  obtain ⟨B, hB, e⟩ := this hu
  rw [e, Subgroup.mem_bot.1 hB, Units.val_one, Matrix.mul_one]

omit [NumberField E] in

theorem scales_inv {x : Matrix (Fin n) (Fin 1) E} {p : GAd σ J} {l : (AF F ⊗[F] E)ˣ} (e : Scales σ J x p l) :
    Scales σ J x p⁻¹ l⁻¹ := by
  unfold Scales at *
  have := congrArg (fun Z => (l⁻¹).1 • ((matHom _ σ J p⁻¹).1 * Z)) e
  simp only [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
    Matrix.mul_smul, smul_smul, Units.inv_mul, one_smul] at this
  exact this.symm


end GlobalTheory.ResLineLevi
end
end

section
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviDecompositionFrame

theorem levi_dec_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ p β, ScalesBy σ J X p β → ∃ u ∈ unipRad σ J X, ∃ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, p = u * m ∧ ScalesBy σ J X m β ∧ (p ∈ ratPts σ J → m ∈ ratPts σ J) ∧ (absE F E (Matrix.GeneralLinearGroup.det β) = 1 → m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW p β hp
  have yx' : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := GlobalTheory.StdPar.yx h hJ hW
  have hinv : ScalesBy σ J X p⁻¹ β⁻¹ := by
    unfold ScalesBy at *
    have := congrArg (fun Z => (matHom _ σ J p⁻¹).1 * Z * (β⁻¹).1) hp
    simp only [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul] at this
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this
    exact this.symm
  have hpF : p ∈ GlobalTheory.UAut.parFlag σ J X fun _ => 0 :=
    ⟨⟨_, fun _ _ hlt => absurd hlt (lt_irrefl _), hp⟩, _, fun _ _ hlt => absurd hlt (lt_irrefl _), hinv⟩
  obtain ⟨u, hu, m, hmF, hpm, hr⟩ := (GlobalTheory.LeviFlag.levi_decomposition F E σ h n J hJ (r + 1) X Y (fun _ => 0)
    hW.xx hW.yy hW.xy).1 p hpF
  rw [GlobalTheory.UAut.unipFlag_const] at hu
  have hm : m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} := by
    simp only [GlobalTheory.StdPar.levi, Subgroup.mem_iInf, Finset.mem_singleton]
    rintro k rfl
    exact Subgroup.mem_inf.2 ⟨GlobalTheory.ResLineLevi.mem_frameStab_of_parFlag yx' hmF.1,
      GlobalTheory.ResLineLevi.mem_frameStab_of_parFlag hW.xy hmF.2⟩
  have hmb : ScalesBy σ J X m β := by
    have e : m = u⁻¹ * p := by rw [hpm, inv_mul_cancel_left]
    unfold ScalesBy at *
    rw [e, map_mul, Units.val_mul, Matrix.mul_assoc, hp, ← Matrix.mul_assoc,
      GlobalTheory.ResLineLevi.unipRad_fix (inv_mem hu)]
  refine ⟨u, hu, m, hm, hpm, hmb, hr, fun hl => Subgroup.mem_inf.2 ⟨hm, ?_⟩⟩
  simp only [Subgroup.mem_iInf, Finset.mem_singleton]
  rintro k rfl
  exact ⟨β, by simpa [MonoidHom.mem_ker] using hl, hmb⟩

end GlobalTheory.LeviDecompositionFrame
end
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviDecomposition_wittFrameStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ p β, ScalesBy σ J X p β → ∃ u ∈ unipRad σ J X, ∃ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, p = u * m ∧ ScalesBy σ J X m β ∧ (p ∈ ratPts σ J → m ∈ ratPts σ J) ∧ (absE F E (Matrix.GeneralLinearGroup.det β) = 1 → m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) := by
  atlas_forward_decl GlobalTheory.LeviDecompositionFrame.levi_dec_frame
end
