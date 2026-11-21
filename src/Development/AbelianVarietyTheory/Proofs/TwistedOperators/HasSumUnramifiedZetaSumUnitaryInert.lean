import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlace
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSatVecUOfDiag
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedDoublingIntegral_inert_place : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert := by
  first | exact @GlobalTheory.InertZeta.unramDoublingInert | exact GlobalTheory.InertZeta.unramDoublingInert | (intros; apply GlobalTheory.InertZeta.unramDoublingInert <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UGraph

open GlobalTheory.Doubling Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_GLint_of_entries {ι : Type} [Fintype ι] [DecidableEq ι] {x : GL ι L}
    (h1 : ∀ i j, x.1 i j ∈ Formalism.UG.intL L) (h2 : ∀ i j, (x⁻¹).1 i j ∈ Formalism.UG.intL L) :
    x ∈ Formalism.UG.GLint ι (Formalism.UG.intL L) := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective (Formalism.UG.intL L).subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective (Formalism.UG.intL L).subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem unif_mem_int {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) : ϖ ∈ Formalism.UG.intL L := by
  show Valued.v ϖ ≤ 1
  rw [hU.2.2.2.1, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
  omega

theorem exp_rev {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q) {d : Fin n → ℤ} {t : GU σ n}
    (ht : t.1.1 = Matrix.diagonal (fun i => (ϖ : L) ^ d i)) (i : Fin n) : d (Fin.rev i) = -d i := by
  have h : Formalism.UG.cT σ t.1.1 * Formalism.UG.antiJ L n * t.1.1 = Formalism.UG.antiJ L n := t.2
  have h1 := congrFun (congrFun h i) (Fin.rev i)
  have hJ : Formalism.UG.antiJ L n i (Fin.rev i) = 1 := by
    simp only [Formalism.UG.antiJ, Fin.val_rev]
    rw [if_pos (by omega)]
  rw [hJ, ht, Formalism.UG.cT, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, hJ] at h1
  rw [map_zpow₀, hU.2.2.1, mul_one, ← zpow_add₀ ϖ.ne_zero] at h1
  have h2 := congrArg Formalism.UG.ordL h1
  rw [Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1, ← zpow_zero (ϖ : L), Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1] at h2
  omega

theorem antiJ_mul_diagonal {n : ℕ} (f g : Fin n → L) (h : ∀ i, f (Fin.rev i) = g i) :
    Formalism.UG.antiJ L n * Matrix.diagonal f = Matrix.diagonal g * Formalism.UG.antiJ L n := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Formalism.UG.antiJ]
  split_ifs with hij
  · have : j = Fin.rev i := Fin.ext (by rw [Fin.val_rev]; omega)
    subst this
    rw [h]
    ring
  · simp

theorem exists_kappa {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q) (d : Fin n → ℤ)
    (hd : ∀ i, d (Fin.rev i) = -d i) :
    ∃ κ : GL (Fin (n + n)) L, κ ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n ∧ κ ∈ Formalism.UG.GLint (Fin (n + n)) (Formalism.UG.intL L) ∧
      GlobalTheory.Doubling.KeepsDiag finSumFinEquiv (GlobalTheory.Doubling.blkMat finSumFinEquiv (Matrix.diagonal fun i => (ϖ : L) ^ d i) 1 * κ.1) ∧
      GlobalTheory.Doubling.leviMat finSumFinEquiv (GlobalTheory.Doubling.blkMat finSumFinEquiv (Matrix.diagonal fun i => (ϖ : L) ^ d i) 1 * κ.1) =
        Matrix.diagonal fun i => (ϖ : L) ^ (d i).toNat := by
  set e := finSumFinEquiv (m := n) (n := n)
  set J := Formalism.UG.antiJ L n
  set u : Fin n → L := fun i => (ϖ : L) ^ (-d i).toNat - 1 with hu
  set w : Fin n → L := fun i => (ϖ : L) ^ (d i).toNat - 1 with hw
  have huw : ∀ i, u i * w i = 0 := fun i => by
    rcases le_total (d i) 0 with h | h
    · simp [hw, Int.toNat_of_nonpos h]
    · simp [hu, Int.toNat_of_nonpos (neg_nonpos.2 h)]
  set B : Matrix (Fin n) (Fin n) L := Matrix.diagonal u with hB
  set C : Matrix (Fin n) (Fin n) L := Matrix.diagonal w with hC
  have hBC : B * C = 0 := by rw [hB, hC, diagonal_mul_diagonal]; simp [huw]
  have hCB : C * B = 0 := by rw [hB, hC, diagonal_mul_diagonal]; simp [mul_comm (w _), huw]
  have hJB : J * B = C * J := antiJ_mul_diagonal u w fun i => by simp [hu, hw, hd]
  have hJC : J * C = B * J := antiJ_mul_diagonal w u fun i => by simp [hu, hw, hd]
  have hσu : B.map σ = B := by
    rw [hB, diagonal_map (map_zero σ)]
    congr 1; funext i
    simp [hu, map_sub, map_pow, hU.2.2.1]
  have hσw : C.map σ = C := by
    rw [hC, diagonal_map (map_zero σ)]
    congr 1; funext i
    simp [hw, map_sub, map_pow, hU.2.2.1]
  let κ : GL (Fin (n + n)) L := ⟨(fromBlocks 1 B C 1).submatrix e.symm e.symm,
    (fromBlocks 1 (-B) (-C) 1).submatrix e.symm e.symm,
    by rw [submatrix_mul_equiv, fromBlocks_multiply]; simp [hBC, hCB],
    by rw [submatrix_mul_equiv, fromBlocks_multiply]; simp [hBC, hCB]⟩
  have hint : ∀ i j, (fromBlocks (1 : Matrix (Fin n) (Fin n) L) B C 1) i j ∈ Formalism.UG.intL L ∧
      (fromBlocks (1 : Matrix (Fin n) (Fin n) L) (-B) (-C) 1) i j ∈ Formalism.UG.intL L := by
    have h1 : ∀ a b : Fin n, (1 : Matrix (Fin n) (Fin n) L) a b ∈ Formalism.UG.intL L := fun a b => by
      rw [one_apply]; split_ifs
      exacts [one_mem _, zero_mem _]
    have h2 : ∀ (f : Fin n → ℕ) (a b : Fin n),
        (Matrix.diagonal fun i => (ϖ : L) ^ f i - 1) a b ∈ Formalism.UG.intL L := fun f a b => by
      rw [diagonal_apply]; split_ifs
      · exact sub_mem (pow_mem (unif_mem_int hU) _) (one_mem _)
      · exact zero_mem _
    intro i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, neg_apply]
    all_goals first
      | exact ⟨h1 _ _, h1 _ _⟩
      | exact ⟨h2 _ _ _, neg_mem (h2 _ _ _)⟩
  have hM : (GlobalTheory.Doubling.blkMat e (Matrix.diagonal fun i => (ϖ : L) ^ d i) 1 * κ.1).submatrix e e =
      fromBlocks (Matrix.diagonal fun i => (ϖ : L) ^ d i) ((Matrix.diagonal fun i => (ϖ : L) ^ d i) * B) C 1 := by
    show ((fromBlocks (Matrix.diagonal fun i => (ϖ : L) ^ d i) 0 0 1).submatrix e.symm e.symm *
      (fromBlocks 1 B C 1).submatrix e.symm e.symm).submatrix e e = _
    rw [submatrix_mul_equiv, submatrix_submatrix]
    simp [fromBlocks_multiply]
  have h1 : (Matrix.diagonal fun i => (ϖ : L) ^ d i) + (Matrix.diagonal fun i => (ϖ : L) ^ d i) * B =
      Matrix.diagonal fun i => (ϖ : L) ^ (d i).toNat := by
    rw [hB, diagonal_mul_diagonal, diagonal_add]
    congr 1; funext i
    simp only [hu]
    rw [mul_sub, mul_one, add_sub_cancel, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ϖ.ne_zero]
    congr 1
    omega
  have h2 : C + 1 = Matrix.diagonal fun i => (ϖ : L) ^ (d i).toNat := by
    rw [hC, ← diagonal_one, diagonal_add]
    congr 1; funext i
    simp [hw]
  refine ⟨κ, ?_, mem_GLint_of_entries (fun i j => (hint _ _).1) (fun i j => (hint _ _).2), ?_, ?_⟩
  · show Formalism.UG.cT σ ((fromBlocks 1 B C 1).submatrix e.symm e.symm) * GlobalTheory.Doubling.blkMat e J (-J) *
      (fromBlocks 1 B C 1).submatrix e.symm e.symm = GlobalTheory.Doubling.blkMat e J (-J)
    have hcT : Formalism.UG.cT σ ((fromBlocks (1 : Matrix (Fin n) (Fin n) L) B C 1).submatrix e.symm e.symm) =
        (fromBlocks 1 C B 1).submatrix e.symm e.symm := by
      rw [Formalism.UG.cT, ← submatrix_map, transpose_submatrix, fromBlocks_map, fromBlocks_transpose, hσu, hσw]
      simp [hB, hC, diagonal_transpose]
    rw [hcT, GlobalTheory.Doubling.blkMat, submatrix_mul_equiv, submatrix_mul_equiv, fromBlocks_multiply, fromBlocks_multiply]
    congr 1
    have e1 : C * J * C = 0 := by rw [Matrix.mul_assoc, hJC, ← Matrix.mul_assoc, hCB, Matrix.zero_mul]
    have e2 : B * J * B = 0 := by rw [Matrix.mul_assoc, hJB, ← Matrix.mul_assoc, hBC, Matrix.zero_mul]
    simp [Matrix.mul_neg, Matrix.neg_mul, hJB, hJC, e1, e2]
  · rw [GlobalTheory.Doubling.KeepsDiag, GlobalTheory.Doubling.leviMat, hM]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, h1, h2]
  · rw [GlobalTheory.Doubling.leviMat, hM]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, h1]

theorem secVal_unif_pow {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q) (χ : Lˣ →* ℂˣ) (s : ℂ)
    (k : ℕ) : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal q χ (s + (n : ℂ) / 2) (ϖ ^ k) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX q n (χ ϖ) s ^ k := by
  have h := Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1 (k : ℤ)
  rw [zpow_natCast] at h
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal, Units.val_pow_eq_pow_val, h, map_pow, Units.val_pow_eq_pow_val,
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX, mul_pow, ← Complex.cpow_nat_mul]
  congr 2
  push_cast
  ring

theorem sphericalDoublingSection_graph_diagonal_cartan [CompleteSpace L] {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q)
    {χ : Lˣ →* ℂˣ} (hχ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr χ) {s : ℂ} {Φ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n → ℂ}
    (hΦ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec σ q n χ s Φ) (d : Fin n → ℤ) (t : GU σ n)
    (ht : t.1.1 = Matrix.diagonal (fun i => (ϖ : L) ^ d i)) (k₁ : GU σ n) (hk₁ : k₁ ∈ KU σ n) (k₂ : GU σ n)
    (hk₂ : k₂ ∈ KU σ n) :
    Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (k₁ * t * k₂)) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX q n (χ ϖ) s ^ (∑ i, max (d i) 0) := by
  have hq : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  obtain ⟨κ, hκG, hκI, hkeep, hlev⟩ := exists_kappa hU d (exp_rev hU ht)
  set e := finSumFinEquiv (m := n) (n := n)
  let K : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n := ⟨κ, hκG⟩
  have hK : K ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD σ n := ⟨hκG, hκI⟩
  obtain ⟨x₁, hx₁⟩ := hk₁.2
  obtain ⟨x₂, hx₂⟩ := hk₂.2
  obtain ⟨y₁, hy₁⟩ := (inv_mem hk₁).2
  let p0 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n := GlobalTheory.Doubling.ioU σ e rfl (k₁, k₁)
  let r : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n := GlobalTheory.Doubling.ioU σ e rfl (k₂, k₁⁻¹)
  have hp0P : p0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n :=
    GlobalTheory.Doubling.mem_siegelOf.2 ((GlobalTheory.Doubling.keepsDiag_blkMat e).2 rfl)
  have hp0K : p0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD σ n :=
    ⟨p0.2, GlobalTheory.Doubling.blkGL e (x₁, x₁), by rw [GlobalTheory.Doubling.bc_blkGL, hx₁]; rfl⟩
  have hrK : r ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD σ n :=
    ⟨r.2, GlobalTheory.Doubling.blkGL e (x₂, y₁), by rw [GlobalTheory.Doubling.bc_blkGL, hx₂, hy₁]; rfl⟩
  have hp1P : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * K ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n := by
    refine GlobalTheory.Doubling.mem_siegelOf.2 ?_
    change GlobalTheory.Doubling.KeepsDiag e (GlobalTheory.Doubling.blkMat e t.1.1 1 * κ.1)
    rw [ht]
    exact hkeep
  let P0 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n := ⟨p0, hp0P⟩
  let P1 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n := ⟨_, hp1P⟩
  have hdec : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (k₁ * t * k₂) = ((P0 * P1 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD σ n) :
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n) * (K⁻¹ * r) := by
    rw [Subgroup.coe_mul]
    change _ = p0 * (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * K) * (K⁻¹ * r)
    rw [show p0 * (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * K) * (K⁻¹ * r) = p0 * GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n t * r by group]
    change GlobalTheory.Doubling.ioU σ e rfl (k₁ * t * k₂, 1) = GlobalTheory.Doubling.ioU σ e rfl (k₁, k₁) *
      GlobalTheory.Doubling.ioU σ e rfl (t, 1) * GlobalTheory.Doubling.ioU σ e rfl (k₂, k₁⁻¹)
    rw [← map_mul, ← map_mul]
    congr 1
    ext1
    · rfl
    · simp
  have ha1 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.aD σ n P1 = ϖ ^ (∑ i, (d i).toNat) := by
    apply Units.ext
    rw [GlobalTheory.Doubling.val_aOf, Units.val_pow_eq_pow_val]
    change (GlobalTheory.Doubling.leviMat e (GlobalTheory.Doubling.blkMat e t.1.1 1 * κ.1)).det = _
    rw [ht, hlev, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  rw [hdec, hΦ _ _ (mul_mem (inv_mem hK) hrK), map_mul, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal_mul hq,
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.secVal_unit q hχ _ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.v_aD_eq P0 hp0K), one_mul, ha1, secVal_unif_pow hU]
  rw [show ∑ i, max (d i) 0 = ((∑ i, (d i).toNat : ℕ) : ℤ) by push_cast; simp [Int.toNat_eq_max], zpow_natCast]

theorem sphSec_io_diag : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (χ : Lˣ →* ℂˣ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr χ → ∀ (s : ℂ) (Φ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec σ q n χ s Φ → ∀ (d : Fin n → ℤ) (t : GU σ n), t.1.1 = Matrix.diagonal (fun i => (ϖ : L) ^ d i) → ∀ k₁ ∈ KU σ n, ∀ k₂ ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (k₁ * t * k₂)) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX q n (χ ϖ) s ^ (∑ i, max (d i) 0) := by
  intro L _ _ _ ϖ σ q n hU χ hχ s Φ hΦ d t ht k₁ hk₁ k₂ hk₂
  exact sphericalDoublingSection_graph_diagonal_cartan hU hχ hΦ d t ht k₁ hk₁ k₂ hk₂

end GlobalTheory.UGraph

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalDoublingSection_graph_diagonal_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (χ : Lˣ →* ℂˣ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr χ → ∀ (s : ℂ) (Φ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec σ q n χ s Φ → ∀ (d : Fin n → ℤ) (t : GU σ n), t.1.1 = Matrix.diagonal (fun i => (ϖ : L) ^ d i) → ∀ k₁ ∈ KU σ n, ∀ k₂ ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (k₁ * t * k₂)) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varX q n (χ ϖ) s ^ (∑ i, max (d i) 0) := by
  atlas_forward_decl GlobalTheory.UGraph.sphSec_io_diag
end

section
section
open MeasureTheory

namespace GlobalTheory

theorem summable_norm_coset_out (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G)
    (hK : IsOpen (K : Set G)) (hμ : μ K = 1) (F : G → ℂ)
    (hF : ∀ g, ∀ k ∈ K, F (g * k) = F g) (hint : Integrable F μ) :
    Summable (fun x : G ⧸ K => ‖F x.out‖) := by
  classical
  set C : G ⧸ K → Set G := fun x => (fun y => x.out⁻¹ * y) ⁻¹' (K : Set G) with hCdef
  have hCmeas : ∀ x, MeasurableSet (C x) := fun x =>
    (hK.preimage (continuous_const.mul continuous_id)).measurableSet
  have hCμ : ∀ x, μ (C x) = 1 := by
    intro x
    simp only [C]
    rw [measure_preimage_mul]; exact hμ
  have hconst : ∀ x, ∀ y ∈ C x, F y = F x.out := by
    intro x y hy
    have hy' : x.out⁻¹ * y ∈ K := hy
    have := hF x.out _ hy'
    simpa using this
  have hmk : ∀ x, ∀ y ∈ C x, (QuotientGroup.mk y : G ⧸ K) = x := by
    intro x y hy
    have hy' : x.out⁻¹ * y ∈ K := hy
    have h1 : (QuotientGroup.mk y : G ⧸ K) = QuotientGroup.mk x.out :=
      (QuotientGroup.eq.mpr hy').symm
    rw [h1]; exact Quotient.out_eq x
  have hdisj : Pairwise (Function.onFun Disjoint C) := by
    intro x y hxy
    rw [Function.onFun, Set.disjoint_left]
    intro z hzx hzy
    exact hxy ((hmk x z hzx).symm.trans (hmk y z hzy))
  have hnorm : Integrable (fun y => ‖F y‖) μ := hint.norm
  have hterm : ∀ x, ∫ y in C x, ‖F y‖ ∂μ = ‖F x.out‖ := by
    intro x
    rw [setIntegral_congr_fun (hCmeas x) (g := fun _ => ‖F x.out‖) (fun y hy => by
      simp only; rw [hconst x y hy])]
    rw [setIntegral_const]
    simp [Measure.real, hCμ x]
  refine summable_of_sum_le (c := ∫ y, ‖F y‖ ∂μ) (fun x => norm_nonneg _) ?_
  intro S
  calc ∑ x ∈ S, ‖F x.out‖ = ∑ x ∈ S, ∫ y in C x, ‖F y‖ ∂μ := by
        simp only [hterm]
    _ = ∫ y in ⋃ x ∈ S, C x, ‖F y‖ ∂μ := by
        rw [integral_biUnion_finset S (fun x _ => hCmeas x) (hdisj.set_pairwise _)
          (fun x _ => hnorm.integrableOn)]
    _ ≤ ∫ y, ‖F y‖ ∂μ :=
        setIntegral_le_integral hnorm (Filter.Eventually.of_forall (fun y => norm_nonneg _))

end GlobalTheory
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_norm_coset_out' : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G), IsOpen (K : Set G) → μ K = 1 → ∀ F : G → ℂ, (∀ g, ∀ k ∈ K, F (g * k) = F g) → Integrable F μ → Summable (fun x : G ⧸ K => ‖F x.out‖) := by
  atlas_forward_decl GlobalTheory.summable_norm_coset_out
end

section
section
open Formalism.UG (IsUnramInv GU KU Hecke dosetInd)

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists

open Formalism.UG

section Generic

variable {G : Type} [Group G] {K : Subgroup G}

def cosetsIn (K : Subgroup G) (g : G) : Set (G ⧸ K) := {x | ∃ a b : K, x.out = (a : G) * g * b}

theorem mem_cosetsIn_iff (x : G ⧸ K) (t : G) :
    x ∈ cosetsIn K t ↔ x.out ∈ DoubleCoset.doubleCoset t (K : Set G) K := by
  rw [DoubleCoset.mem_doubleCoset]
  exact ⟨fun ⟨a, b, e⟩ => ⟨a, a.2, b, b.2, e⟩, fun ⟨a, ha, b, hb, e⟩ => ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩⟩

theorem cosetsIn_eq {g g' : G} (h : g' ∈ DoubleCoset.doubleCoset g (K : Set G) K) :
    cosetsIn K g' = cosetsIn K g := by
  ext x
  rw [mem_cosetsIn_iff, mem_cosetsIn_iff, DoubleCoset.doubleCoset_eq_of_mem h]

theorem dosetInd_eq {g g' : G} (h : g' ∈ DoubleCoset.doubleCoset g (K : Set G) K) :
    dosetInd ℂ K g' = dosetInd ℂ K g := by
  rw [dosetInd, dosetInd, DoubleCoset.doubleCoset_eq_of_mem h]

theorem cosetsIn_ncard_ne_zero (hK : IsCommensurated K) (g : G) : (cosetsIn K g).ncard ≠ 0 := by
  refine ((Set.ncard_pos (P.finite_cosets_in_doset hK g)).2 ⟨(g : G ⧸ K), ?_⟩).ne'
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul K g
  exact ⟨1, u, by simpa using hu⟩

theorem cosetsIn_one : cosetsIn K 1 = {((1 : G) : G ⧸ K)} := by
  ext x
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, b, e⟩
    rw [← QuotientGroup.out_eq' x, e]
    exact QuotientGroup.eq.2 (by simpa using K.inv_mem (K.mul_mem a.2 b.2))
  · rintro rfl
    refine ⟨⟨((1 : G) : G ⧸ K).out, ?_⟩, 1, by simp⟩
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((1 : G) : G ⧸ K))
    simpa using K.inv_mem this

end Generic

theorem exists_isZonal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ α : Fin (n / 2) → ℂˣ, ∃ w : GU σ n → ℂ,
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal ϖ q α w := by
  intro L _ _ _ ϖ σ q n hU α
  classical
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have law := GlobalTheory.LFun.SatCompare.satU_laws (n := n) hU α
  have hN : ∀ g : GU σ n, ((cosetsIn (KU σ n) g).ncard : ℂ) ≠ 0 := fun g =>
    Nat.cast_ne_zero.2 (cosetsIn_ncard_ne_zero hK g)
  let w : GU σ n → ℂ := fun g =>
    SatU ϖ q (dosetInd ℂ (KU σ n) g) (fun i => (α i : ℂ)) / ((cosetsIn (KU σ n) g).ncard : ℂ)
  have hw : ∀ g g' : GU σ n, g' ∈ DoubleCoset.doubleCoset g (KU σ n : Set (GU σ n)) (KU σ n) → w g' = w g :=
    fun g g' h => by simp only [w, dosetInd_eq h, cosetsIn_eq h]
  refine ⟨w, fun a b g => hw _ _ (DoubleCoset.mem_doubleCoset.2 ⟨a, a.2, b, b.2, rfl⟩), ?_, fun h hh => ?_⟩
  · simp only [w, law.2.2, cosetsIn_one, Set.ncard_singleton, Nat.cast_one, div_one]
  refine GlobalTheory.LFun.hecke_induction (K := KU σ n)
    (p := fun f => hAct (KU σ n) f w 1 = SatU ϖ q f fun i => (α i : ℂ)) ?_ ?_ ?_ hh
  · simpa [hAct] using (law.2.1 0 0 (zero_mem _)).symm
  · intro f hf f' hf' e e'
    have fin : ∀ f ∈ Hecke ℂ (KU σ n), (Function.support fun x : GU σ n ⧸ KU σ n => f x.out • w (1 * x.out)).Finite :=
      fun f hf => (P.finite_support_cosets hK hf.2).subset fun x hx h0 => hx (by simp [h0])
    rw [law.1 _ hf _ hf', ← e, ← e', hAct, hAct, hAct]
    simp only [Pi.add_apply, add_smul]
    exact finsum_add_distrib (fin f hf) (fin f' hf')
  · intro r g
    have hfin := P.finite_cosets_in_doset hK g
    have hterm : ∀ x ∈ hfin.toFinset, (r • dosetInd ℂ (KU σ n) g) x.out • w (1 * x.out) = r * w g := fun x hx => by
      have hm := (mem_cosetsIn_iff x g).1 ((Set.Finite.mem_toFinset _).1 hx)
      rw [Pi.smul_apply, dosetInd, Set.indicator_of_mem hm, one_mul, hw g _ hm]
      simp
    rw [law.2.1 r _ (Final.DosetIndMem _ _ ℂ g), hAct,
      finsum_eq_sum_of_support_subset (s := hfin.toFinset), Finset.sum_congr rfl hterm,
      Finset.sum_const, ← Set.ncard_eq_toFinset_card _ hfin, nsmul_eq_mul]
    · have := hN g
      simp only [w]
      rw [← cosetsIn]
      field_simp
    · intro x hx
      rw [Set.Finite.coe_toFinset]
      by_contra h
      refine hx ?_
      show (r • dosetInd ℂ (KU σ n) g) x.out • w (1 * x.out) = 0
      rw [Pi.smul_apply, dosetInd, Set.indicator_of_notMem (fun h' => h ((mem_cosetsIn_iff x g).2 h'))]
      simp

end GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists
end
end

open Formalism.UG (IsUnramInv GU KU Hecke dosetInd)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zonalSphericalFunction_unramifiedUnitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ α : Fin (n / 2) → ℂˣ, ∃ w : GU σ n → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal ϖ q α w := by
  atlas_forward_decl GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists.exists_isZonal
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ZetaSumU

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem cartan_complete : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ g : GU σ n, ∃ (d : Fin n → ℤ) (t : GU σ n),
      t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) ∧ ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g = k₁ * t * k₂ := by
  intro L _ _ _ ϖ σ q n hU g
  obtain ⟨d, hd, a, ha, b, hb, e⟩ := GlobalTheory.LFun.UnitaryDiv.exists_good_div L ϖ σ q n hU g
  obtain ⟨t, ht⟩ := GlobalTheory.InertThetaCompare.exists_diag hU hd
  obtain ⟨k₁, h₁, k₂, h₂, e'⟩ := GlobalTheory.T.unitaryDoubleCoset_of_GLintDoubleCoset L ϖ σ q n hU t g a b ha hb (Units.ext (by rw [e, ← ht]; rfl))
  exact ⟨fun i => d.getD i.1 0, t, ht, k₁, h₁, k₂, h₂, e'⟩

section
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {σ : L →+* L} {q n : ℕ}

theorem kerU_biInv {ϖ : L} (hU : IsUnramInv ϖ σ q) {N : ℕ} {z : ℂˣ} {φ : GU σ n → ℂ} (hφ : KerU ϖ q N z φ)
    (g : GU σ n) {k₁ k₂ : GU σ n} (h₁ : k₁ ∈ KU σ n) (h₂ : k₂ ∈ KU σ n) : φ (k₁ * g * k₂) = φ g := by
  obtain ⟨d, t, ht, a, ha, b, hb, rfl⟩ := cartan_complete L ϖ σ q n hU g
  rw [show k₁ * (a * t * b) * k₂ = (k₁ * a) * t * (b * k₂) by group, hφ d t ht _ (mul_mem h₁ ha) _ (mul_mem hb h₂),
    hφ d t ht a ha b hb]

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem sph_eq (ϖ : Lˣ) (hU : IsUnramInv (ϖ : L) σ q) {χ : Lˣ →* ℂˣ} (hχ : IsUnr χ) {s : ℂ} {Φ : GD σ n → ℂ}
    (hΦ : IsSphSec σ q n χ s Φ) {N : ℕ} {z : ℂˣ} {φ : GU σ n → ℂ} (hφ : KerU (ϖ : L) q N z φ)
    (hX : varX q n (χ ϖ) s = (z : ℂ) * ((q : ℂ) ^ N)⁻¹) (g : GU σ n) : Φ (io1 σ n g) = φ g := by
  obtain ⟨d, t, ht, a, ha, b, hb, rfl⟩ := cartan_complete L (ϖ : L) σ q n hU g
  rw [GlobalTheory.T.sphericalDoublingSection_graph_diagonal_eq L ϖ σ q n hU χ hχ s Φ hΦ d t ht a ha b hb, hφ d t ht a ha b hb, hX]

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem exists_unr_char (ϖ : Lˣ) (hU : IsUnramInv (ϖ : L) σ q) (z : ℂˣ) : ∃ χ : Lˣ →* ℂˣ, IsUnr χ ∧ χ ϖ = z := by
  refine ⟨{ toFun := fun u => z ^ Formalism.UG.ordL (u : L), map_one' := ?_, map_mul' := fun a b => ?_ }, fun u hu => ?_, ?_⟩
  · have : Formalism.UG.ordL (1 : L) = 0 := by simp [Formalism.UG.ordL]; rfl
    simp [this]
  · simp [Formalism.UG.P.fIwasawa_ordL_mul _ _ a.ne_zero b.ne_zero, _root_.zpow_add]
  · have : Formalism.UG.ordL (u : L) = 0 := by
      have h0 : Valued.v (u : L) ≠ 0 := by rw [hu]; exact one_ne_zero
      have h1 : WithZero.unzero h0 = 1 := WithZero.coe_injective (by rw [WithZero.coe_unzero, hu]; rfl)
      simp [Formalism.UG.ordL, h0, h1]
    simp [this]
  · have h := Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1 (1 : ℤ)
    rw [zpow_one] at h
    simp [h]

theorem exists_haar (ϖ : L) (hU : IsUnramInv ϖ σ q) (n : ℕ) [MeasurableSpace (GU σ n)] [BorelSpace (GU σ n)] :
    ∃ μ : Measure (GU σ n), μ.IsHaarMeasure ∧ μ (KU σ n) = 1 := by
  haveI := GlobalTheory.LGrp.locallyCompact_GU_of_unram hU n
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU
  let K₀ : TopologicalSpace.PositiveCompacts (GU σ n) :=
    ⟨⟨_, hc⟩, by rw [ho.interior_eq]; exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self⟩

end

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem closedForm_eq' (q r : ℕ) (X y : ℂ) (α : Fin (r / 2) → ℂˣ) :
    closedForm q r X y α = eulerFac (bcParam r α) y * ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * X) := by
  rw [closedForm, GlobalTheory.LGrp.bcParam, GlobalTheory.LFun.eulerFac_add, GlobalTheory.LFun.eulerFac_add,
    GlobalTheory.LFun.eulerFac_map, GlobalTheory.LFun.eulerFac_map, Finset.prod_mul_distrib]
  simp only [Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm y]
  rcases Nat.even_or_odd r with h | h
  · rw [if_neg (Nat.not_odd_iff_even.2 h), Nat.even_iff.1 h]
    simp only [Multiset.replicate_zero, GlobalTheory.LFun.eulerFac_zero]
    ring
  · rw [if_pos h, Nat.odd_iff.1 h]
    simp only [Multiset.replicate_one, GlobalTheory.LFun.eulerFac_singleton, Units.val_one, one_mul]
    ring

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem varXY_eq (q r t : ℕ) (hq : 2 ≤ q) (z : ℂ) :
    varX q r z ((t : ℂ) / 2) = z * ((q : ℂ) ^ (r + t))⁻¹ ∧ varY q z ((t : ℂ) / 2) = z * ((q : ℂ) ^ (t + 1))⁻¹ := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  constructor
  · rw [varX, show -(2 * ((t : ℂ) / 2) + r) = -(((r + t : ℕ) : ℂ)) by push_cast; ring, Complex.cpow_neg,
      Complex.cpow_natCast]
  · rw [varY, show -(2 * ((t : ℂ) / 2) + 1) = -(((t + 1 : ℕ) : ℂ)) by push_cast; ring, Complex.cpow_neg,
      Complex.cpow_natCast]

theorem tb_triv : ∀ (q r : ℕ), 2 ≤ q → ∀ α : Fin (r / 2) → ℂˣ, (∀ i, (α i : ℂ) = (q : ℂ) ^ ((r : ℤ) - 1 - 2 * (i.val : ℤ))) → GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α := by
  intro q r hq α hα i
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hn : ‖(α i : ℂ)‖ = (q:ℝ) ^ ((((r:ℤ) - 1 - 2 * (i.val:ℤ) : ℤ)) : ℝ) := by
    rw [hα, norm_zpow, Complex.norm_natCast, Real.rpow_intCast]
  have hi : 2 * i.val + 1 ≤ r := by have := i.2; omega
  have hi' : 2 * (i.val : ℝ) + 1 ≤ r := by exact_mod_cast hi
  have hi0 : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
  rw [Real.rpow_neg (by positivity), GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq, hn, ← Real.rpow_neg (by positivity)]
  constructor <;> apply Real.rpow_le_rpow_of_exponent_le hq1 <;> push_cast <;> linarith

theorem dom_of_tb : ∀ (q r t : ℕ), 2 ≤ q → r ≤ t → ∀ (z : ℂ), ‖z‖ = 1 → ∀ α : Fin (r / 2) → ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY q z ((t : ℂ) / 2)) α := by
  intro q r t hq hrt z hz α hα
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hq1' : (1:ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hq0 : (0:ℝ) < q := by linarith
  rw [(varXY_eq q r t hq z).2]
  have hy : ‖z * ((q:ℂ)^(t+1))⁻¹‖ = ((q:ℝ)^(t+1))⁻¹ := by
    rw [norm_mul, hz, one_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have hB : ((q:ℝ)^2)^(((r:ℝ)-1)/2) ≤ (q:ℝ)^t := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by have : (r:ℝ) ≤ t := (by exact_mod_cast hrt); linarith)
  have hBp : 0 < ((q:ℝ)^2)^(((r:ℝ)-1)/2) := by positivity
  have e : ((q:ℝ)^(t+1))⁻¹ * (q:ℝ)^t = (q:ℝ)⁻¹ := by rw [pow_succ]; field_simp
  have key : ∀ a : ℝ, a ≤ (q:ℝ)^t → ((q:ℝ)^(t+1))⁻¹ * a < 1 := fun a ha =>
    calc ((q:ℝ)^(t+1))⁻¹ * a ≤ ((q:ℝ)^(t+1))⁻¹ * (q:ℝ)^t := mul_le_mul_of_nonneg_left ha (by positivity)
      _ = (q:ℝ)⁻¹ := e
      _ < 1 := inv_lt_one_of_one_lt₀ hq1'
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain, hy]
  refine ⟨by simpa using key 1 (one_le_pow₀ hq1), fun i => ⟨key _ ((hα i).2.trans hB), key _ ?_⟩⟩
  have h1 := (hα i).1
  rw [Real.rpow_neg (by positivity)] at h1
  have hαp : 0 < ‖(α i : ℂ)‖ := norm_pos_iff.2 (α i).ne_zero
  exact (inv_le_of_inv_le₀ hBp h1).trans hB

set_option maxHeartbeats 1000000 in
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in

theorem hasSum_zetaSum_inert : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q r t : ℕ), IsUnramInv ϖ σ q → r ≤ t → ∀ (z : ℂˣ) (φ : GU σ r → ℂ), ‖(z : ℂ)‖ = 1 → KerU ϖ q (r + t) z φ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ r) V) (x : V) (α : Fin (r / 2) → ℂˣ), IsSatVecU ϖ q ρ x α → GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → HasSum (fun a : GU σ r ⧸ KU σ r => φ a.out * ℓ (ρ a.out x)) (eulerFac (bcParam r α) ((z : ℂ) * ((q : ℂ) ^ (t + 1))⁻¹) * (∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((z : ℂ) * ((q : ℂ) ^ (r + t))⁻¹))) * ℓ x) := by
  intro L _ _ _ ϖ σ q r t hU hrt z φ hz hφ V _ _ ρ x α hx hα ℓ hℓ
  obtain ⟨C, hC⟩ := hℓ
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq : q ≠ 0 := by omega
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    have h' := hU.2.2.2.1
    rw [h, map_zero] at h'
    exact WithZero.zero_ne_coe h'
  let ϖu : Lˣ := Units.mk0 ϖ hϖ0
  have hUu : IsUnramInv (ϖu : L) σ q := hU
  obtain ⟨χ, hχ, hχϖ⟩ := exists_unr_char ϖu hUu z
  obtain ⟨Φ, hΦ⟩ := exists_isSphSec σ hq r hχ ((t : ℂ) / 2)
  obtain ⟨hXe, hYe⟩ := varXY_eq q r t hq2 (z : ℂ)
  have hX : varX q r (χ ϖu) ((t : ℂ) / 2) = (z : ℂ) * ((q : ℂ) ^ (r + t))⁻¹ := by rw [hχϖ, hXe]
  have hΦφ : ∀ g, Φ (io1 σ r g) = φ g := sph_eq ϖu hUu hχ hΦ hφ hX
  letI : MeasurableSpace (GU σ r) := borel _
  haveI : BorelSpace (GU σ r) := ⟨rfl⟩
  obtain ⟨μ, hμH, hμK⟩ := exists_haar ϖ hU r
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU r
  have hKo := (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q r hU).1
  have hright : ∀ g, ∀ k ∈ KU σ r, φ (g * k) = φ g := fun g k hk => by
    simpa using kerU_biInv hU hφ g (one_mem _) hk
  have hdouble := GlobalTheory.T.unramifiedDoublingIntegral_inert_place L ϖu σ q r hUu μ hμK χ hχ _ Φ hΦ
  have hzχ : ((χ ϖu : ℂˣ) : ℂ) = z := by rw [hχϖ]
  have hdom : ∀ β : Fin (r / 2) → ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r β →
      Domain (varY q (χ ϖu) ((t : ℂ) / 2)) β := fun β hβ => by
    rw [hzχ]; exact dom_of_tb q r t hq2 hrt z hz β hβ

  obtain ⟨α0, hα0, hw0⟩ := isZonal_one hU r
  have hint1 := ((hdouble α0 _ hw0).1 (hdom α0 (tb_triv q r hq2 α0 hα0))).1
  have hintφ : Integrable φ μ := by simpa [hΦφ] using hint1

  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_zonalSphericalFunction_unramifiedUnitary L ϖ σ q r hU α
  obtain ⟨hintw, hval, -⟩ := (hdouble α w hw).1 (hdom α hα)
  simp only [hΦφ] at hintw hval
  have hFw : ∀ g, ∀ k ∈ KU σ r, φ (g * k) * w (g * k) = φ g * w g := fun g k hk => by
    have h1 := hw.1 1 ⟨k, hk⟩ g
    simp only [OneMemClass.coe_one, one_mul] at h1
    rw [hright g k hk, h1]
  have hsw := (GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ r) hKo hμK _ hFw hintw).of_norm
  have hci := (GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets _ μ (KU σ r) hKo hμK (fun g => φ g * w g) _ hFw hsw.hasSum).2
  have hS1 : HasSum (fun a : GU σ r ⧸ KU σ r => φ a.out * w a.out)
      (closedForm q r (varX q r (χ ϖu) ((t : ℂ) / 2)) (varY q (χ ϖu) ((t : ℂ) / 2)) α) := by
    rw [← hval, hci]; exact hsw.hasSum

  have hsφ := GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ r) hKo hμK φ hright hintφ
  have hsψ : Summable (fun a : GU σ r ⧸ KU σ r => φ a.out * ℓ (ρ a.out x)) := by
    refine Summable.of_norm_bounded (hsφ.mul_left C) fun a => ?_
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)

  have hm : ∀ g : GU σ r, dosetInd ℂ (KU σ r) g ∈ Formalism.UG.Hecke ℂ (KU σ r) := fun g => Formalism.UG.Final.DosetIndMem _ _ ℂ g
  have hcond : ∀ g : GU σ r, Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) (fun g => ℓ x * w g) 1 =
      Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) (fun g => ℓ (ρ g x)) 1 := fun g => by
    have h1 := hw.2.2 _ (hm g)
    have h2 := congrArg ℓ (hx.2.2 _ (hm g))
    rw [map_smul, smul_eq_mul] at h2
    have e1 : Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) (fun g => ℓ x * w g) 1 =
        ℓ x * Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) w 1 := by
      unfold Formalism.UG.hAct
      rw [mul_finsum]
      exact finsum_congr fun c => by simp only [smul_eq_mul]; ring
    have e2 : Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) (fun g => ℓ (ρ g x)) 1 =
        ℓ (GlobalTheory.LFun.heckeVec ρ (KU σ r) (dosetInd ℂ (KU σ r) g) x) := by
      refine Eq.trans (finsum_congr fun c => ?_)
        (ℓ.toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec hK (hm g) ρ x)).symm
      simp
    rw [e1, e2, h1, h2, mul_comm]
  have hswap := GlobalTheory.T.biInvariant_replace_same_double_coset_sums _ (KU σ r) hK φ (fun g => ℓ x * w g) (fun g => ℓ (ρ g x)) _
    (fun a b g => kerU_biInv hU hφ g a.2 b.2)
    (fun a b g => by simp only [hw.1 a b g]) hcond hsψ.hasSum
  have h2 : HasSum (fun a : GU σ r ⧸ KU σ r => φ a.out * (ℓ x * w a.out))
      (closedForm q r (varX q r (χ ϖu) ((t : ℂ) / 2)) (varY q (χ ϖu) ((t : ℂ) / 2)) α * ℓ x) := by
    have h3 : (fun a : GU σ r ⧸ KU σ r => φ a.out * (ℓ x * w a.out)) = fun a => φ a.out * w a.out * ℓ x :=
      funext fun a => by ring
    rw [h3]; exact hS1.mul_right (ℓ x)
  have e := hswap.unique h2
  rw [hX, hzχ, hYe, closedForm_eq'] at e
  rw [← e]
  exact hsψ.hasSum

end GlobalTheory.ZetaSumU

end
end
