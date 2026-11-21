import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne

section
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.IdTorus

theorem mat_eq_of_isIdTorusElt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ {l : Fin r → (AF F ⊗[F] E)ˣ} {a : GAd σ J}, IsIdTorusElt σ J X Y l a →
    (matHom _ σ J a).1 = 1 + adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) Y * J)
      + adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) X * J) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW l a ha
  obtain ⟨h1, h2, h3⟩ := ha
  have hxx : adMat F (cT (σ : E →+* E) X * J) * adMat F X = 0 := by
    rw [← Matrix.map_mul, hW.xx, Matrix.map_zero _ (map_zero _)]
  have hxy : adMat F (cT (σ : E →+* E) X * J) * adMat F Y = 1 := by
    rw [← Matrix.map_mul, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]
  have hyx : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [← Matrix.map_mul, GlobalTheory.StdPar.yx h hJ hW, Matrix.map_one _ (map_zero _) (map_one _)]
  have hyy : adMat F (cT (σ : E →+* E) Y * J) * adMat F Y = 0 := by
    rw [← Matrix.map_mul, hW.yy, Matrix.map_zero _ (map_zero _)]
  set A := (matHom _ σ J a).1 with hAdef
  set Xs := adMat F (cT (σ : E →+* E) X * J) with hXs
  set Ys := adMat F (cT (σ : E →+* E) Y * J) with hYs
  set P := 1 - adMat F X * Ys - adMat F Y * Xs with hP
  have hXP : Xs * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hxx, hxy,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hYP : Ys * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hyx, hyy,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hAP : A * P = P := by
    ext i j
    have hz : (fun k => P k j) ∈ colPerp σ J X Set.univ ⊓ colPerp σ J Y Set.univ := by
      rw [Submodule.mem_inf]
      refine ⟨?_, ?_⟩
      · simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
        intro k _
        change (Xs *ᵥ fun k => P k j) k = 0
        rw [show (Xs *ᵥ fun k => P k j) k = (Xs * P) k j from rfl, hXP]; rfl
      · simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
        intro k _
        change (Ys *ᵥ fun k => P k j) k = 0
        rw [show (Ys *ᵥ fun k => P k j) k = (Ys * P) k j from rfl, hYP]; rfl
    have := congrFun (h3 _ hz) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hsum : P + adMat F X * Ys + adMat F Y * Xs = 1 := by rw [hP]; abel
  have hA : A = P + adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) * Ys
      + adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) * Xs := by
    calc A = A * (P + adMat F X * Ys + adMat F Y * Xs) := by rw [hsum, Matrix.mul_one]
      _ = _ := by
        rw [Matrix.mul_add, Matrix.mul_add, hAP, ← Matrix.mul_assoc, h1, ← Matrix.mul_assoc A, h2]
  have hd : ∀ f : Fin r → AF F ⊗[F] E, diagonal (fun k => f k - 1) = diagonal f - 1 := fun f => by
    rw [← diagonal_one, diagonal_sub]
  rw [hA, hd, hd, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_one, hP]
  abel

end GlobalTheory.IdTorus
end

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idelicFrameTorusElement_matrix_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ {l : Fin r → (AF F ⊗[F] E)ˣ} {a : GAd σ J}, IsIdTorusElt σ J X Y l a →
    (matHom _ σ J a).1 = 1 + adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) Y * J)
      + adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) X * J) := by
  atlas_forward_decl GlobalTheory.IdTorus.mat_eq_of_isIdTorusElt
end

section
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IdTorus

theorem levi_mulVec_col : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {S : Finset (Fin r)}, (∀ k ∈ S, ∀ i, i ≤ k → i ∈ S) →
    ∀ {g : GAd σ J}, g ∈ levi σ J X Y S → ∀ k ∈ S,
    (matHom _ σ J g).1 *ᵥ (fun i => adMat F X i k) =
      (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 * adMat F X) k k • (fun i => adMat F X i k) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW S hS g hg k hk
  classical
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E),
      cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) := fun Z => rfl
  have mem : ∀ {h' : GAd σ J}, h' ∈ levi σ J X Y S → ∀ k ∈ S,
      h' ∈ frameStab σ J (initCols X k) ⊤ ∧ h' ∈ frameStab σ J (initCols Y k) ⊤ := fun hh k hk =>
    Subgroup.mem_inf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hh k) hk)

  have fr : ∀ (C : Matrix (Fin n) (Fin r) E) (h' : GAd σ J) (k : Fin r), h' ∈ frameStab σ J (initCols C k) ⊤ →
      ∃ c : Fin r → AF F ⊗[F] E, (∀ j, k < j → c j = 0) ∧
        ∀ i, ((matHom _ σ J h').1 * adMat F C) i k = (adMat F C *ᵥ c) i := by
    rintro C h' k ⟨B, -, e⟩
    let P : Matrix (Fin r) (Fin (k.val + 1)) (AF F ⊗[F] E) :=
      (1 : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)).submatrix id (Fin.castLE k.2)
    have hP : adMat F (initCols C k) = adMat F C * P := by
      ext i j; simp [P, initCols, Matrix.mul_apply, Matrix.one_apply]
    refine ⟨fun j => (P * B.1) j ⟨k, Nat.lt_succ_self _⟩, fun j hj => ?_, fun i => ?_⟩
    · simp only [P, Matrix.mul_apply, Matrix.submatrix_apply, id]
      refine Finset.sum_eq_zero fun j' _ => ?_
      rw [Matrix.one_apply_ne, zero_mul]
      intro hjj
      rw [show j = _ from hjj] at hj
      exact absurd hj (not_lt.2 (Nat.le_of_lt_succ j'.2))
    · have e2 : ((matHom _ σ J h').1 * adMat F C) i k =
          ((matHom _ σ J h').1 * adMat F (initCols C k)) i ⟨k, Nat.lt_succ_self _⟩ := by
        simp [Matrix.mul_apply, initCols]
      rw [e2, e, hP, Matrix.mul_assoc]
      rfl
  set M := (matHom _ σ J g).1 with hMdef
  obtain ⟨hX, -⟩ := mem hg k hk
  obtain ⟨c, hc0, hcM⟩ := fr X g k hX
  have hYX : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [← Matrix.map_mul, yx h hJ hW, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG : ∀ j, (adMat F (cT (σ : E →+* E) Y * J) * M * adMat F X) j k = c j := by
    intro j
    have : (fun i => (M * adMat F X) i k) = adMat F X *ᵥ c := funext hcM
    calc (adMat F (cT (σ : E →+* E) Y * J) * M * adMat F X) j k
        = (adMat F (cT (σ : E →+* E) Y * J) *ᵥ fun i => (M * adMat F X) i k) j := by
          rw [Matrix.mul_assoc]; rfl
      _ = c j := by rw [this, mulVec_mulVec, hYX, one_mulVec]
  have hone : cT (sigR (AF F) σ) (adMat F Y) * adMat F J * adMat F X = 1 := by
    rw [c1, ← Matrix.map_mul, ← Matrix.map_mul, yx h hJ hW, Matrix.map_one _ (map_zero _) (map_one _)]
  have hlt : ∀ j, j < k → c j = 0 := by
    intro j hjk
    obtain ⟨-, hY⟩ := mem (inv_mem hg) j (hS k hk j hjk.le)
    obtain ⟨c', hc'0, hc'M⟩ := fr Y g⁻¹ j hY
    set Mi := (matHom _ σ J g⁻¹).1 with hMidef
    have hMMi : M * Mi = 1 := by
      rw [hMdef, hMidef, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    have hu : cT (sigR (AF F) σ) M * adMat F J * M = adMat F J := g.2
    have hJM : adMat F J * M = cT (sigR (AF F) σ) Mi * adMat F J := by
      conv_rhs => rw [← hu]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, hMMi, Formalism.UG.cT_one, Matrix.one_mul]
    set W : Matrix (Fin r) (Fin r) (AF F ⊗[F] E) := Matrix.of fun (m : Fin r) (_ : Fin r) => c' m with hWdef
    have hD : ∀ l, (Mi * adMat F Y) l j = (adMat F Y * W) l j := by
      intro l; rw [hc'M l]; rfl
    have e0 : adMat F (cT (σ : E →+* E) Y * J) = adMat F (cT (σ : E →+* E) Y) * adMat F J := Matrix.map_mul
    have e1 : adMat F (cT (σ : E →+* E) Y * J) * M = cT (sigR (AF F) σ) (Mi * adMat F Y) * adMat F J := by
      rw [e0, ← c1, Matrix.mul_assoc, hJM, Formalism.UG.cT_mul, Matrix.mul_assoc]
    have key : (adMat F (cT (σ : E →+* E) Y * J) * M * adMat F X) j k =
        (cT (sigR (AF F) σ) (adMat F Y * W) * adMat F J * adMat F X) j k := by
      rw [e1]
      simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hD]
    rw [← hG j, key, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ (adMat F Y)), hone,
      Matrix.mul_one]
    show sigR (AF F) σ (c' k) = 0
    rw [hc'0 k hjk, map_zero]
  have hc : c = Pi.single k (c k) := by
    funext j
    rcases lt_trichotomy j k with hj | rfl | hj
    · rw [hlt j hj]; simp [Pi.single_apply, hj.ne]
    · simp
    · rw [hc0 j hj]; simp [Pi.single_apply, hj.ne']
  funext i
  calc (M *ᵥ fun i => adMat F X i k) i = (M * adMat F X) i k := rfl
    _ = (adMat F X *ᵥ c) i := hcM i
    _ = _ := by
      rw [hc, hG k]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

end GlobalTheory.IdTorus
end
end

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_element_preserves_witt_column_span : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {S : Finset (Fin r)}, (∀ k ∈ S, ∀ i, i ≤ k → i ∈ S) →
    ∀ {g : GAd σ J}, g ∈ levi σ J X Y S → ∀ k ∈ S,
    (matHom _ σ J g).1 *ᵥ (fun i => adMat F X i k) =
      (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 * adMat F X) k k • (fun i => adMat F X i k) := by
  atlas_forward_decl GlobalTheory.IdTorus.levi_mulVec_col
end

section
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.TorusCentRow

theorem row_scalar : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {g : GAd σ J} {k : Fin r} (γ : AF F ⊗[F] E),
    (matHom _ σ J g⁻¹).1 *ᵥ (fun i => adMat F Y i k) = γ • (fun i => adMat F Y i k) → ∀ i,
    (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1) k i =
      (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 * adMat F X) k k * adMat F (cT (σ : E →+* E) Y * J) k i := by
  intro F E _ _ _ _ _ σ n J r X Y hCM hJ hW g k γ hγ i
  set S := sigR (AF F) σ with hS
  set M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g).1 with hMdef
  set Mi : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g⁻¹).1 with hMidef
  have hinv : matHom (AF F) σ J g⁻¹ = (matHom (AF F) σ J g)⁻¹ := map_inv _ g
  have hMMi : M * Mi = 1 := by
    rw [hMdef, hMidef, hinv]; exact Units.mul_inv _
  have hU : cT S M * adMat F J * M = adMat F J := g.2
  have hadY : adMat F (cT (σ : E →+* E) Y * J) = cT S (adMat F Y) * adMat F J := by
    rw [adMat, Matrix.map_mul]
    congr 1
  have hJM : adMat F J * M = cT S Mi * adMat F J := by
    calc adMat F J * M = (cT S Mi * cT S M) * adMat F J * M := by
          rw [← Formalism.UG.cT_mul, hMMi, Formalism.UG.cT_one, Matrix.one_mul]
      _ = cT S Mi * (cT S M * adMat F J * M) := by simp only [Matrix.mul_assoc]
      _ = cT S Mi * adMat F J := by rw [hU]
  have hcol : ∀ j, (Mi * adMat F Y) j k = γ * adMat F Y j k := by
    intro j
    have := congrFun hγ j
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  have hrow : ∀ i, (adMat F (cT (σ : E →+* E) Y * J) * M) k i
      = S γ * adMat F (cT (σ : E →+* E) Y * J) k i := by
    intro i
    rw [hadY, Matrix.mul_assoc, hJM, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul]
    simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, hcol, map_mul,
      Finset.mul_sum, mul_assoc]
  have hyx : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [adMat, adMat, ← Matrix.map_mul, GlobalTheory.StdPar.yx hCM hJ hW]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hkk : (adMat F (cT (σ : E →+* E) Y * J) * M * adMat F X) k k = S γ := by
    rw [Matrix.mul_apply]
    simp_rw [hrow, mul_assoc, ← Finset.mul_sum, ← Matrix.mul_apply, hyx, Matrix.one_apply_eq, mul_one]
  rw [hkk, hrow]

end GlobalTheory.TorusCentRow
end

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_frame_eigenvector_column_form : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {g : GAd σ J} {k : Fin r} (γ : AF F ⊗[F] E),
    (matHom _ σ J g⁻¹).1 *ᵥ (fun i => adMat F Y i k) = γ • (fun i => adMat F Y i k) → ∀ i,
    (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1) k i =
      (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 * adMat F X) k k * adMat F (cT (σ : E →+* E) Y * J) k i := by
  atlas_forward_decl GlobalTheory.TorusCentRow.row_scalar
end

section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IdTorusCent

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem swap (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) : IsWittFrame σ J Y X :=
  ⟨hW.yy, hW.xx, yx h hJ hW, fun z h1 h2 h3 => hW.aniso z h2 h1 h3⟩

theorem levi_swap (S : Finset (Fin r)) : levi σ J Y X S = levi σ J X Y S := by
  simp only [levi, inf_comm]

theorem comm_block (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {S : Finset (Fin r)}
    (hS : ∀ k ∈ S, ∀ i, i ≤ k → i ∈ S) {g : GAd σ J} (hg : g ∈ levi σ J X Y S) (d : Fin r → AF F ⊗[F] E)
    (hd : ∀ k ∉ S, d k = 0) :
    (matHom _ σ J g).1 * (adMat F X * diagonal d * adMat F (cT (σ : E →+* E) Y * J)) =
      adMat F X * diagonal d * adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 := by
  have e1 : (matHom _ σ J g).1 * adMat F X * diagonal d = adMat F X * diagonal (fun k =>
      (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 * adMat F X) k k * d k) := by
    ext i k
    rw [mul_diagonal, mul_diagonal]
    by_cases hk : k ∈ S
    · have := congrFun (GlobalTheory.T.levi_element_preserves_witt_column_span h hJ hW hS hg k hk) i
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      rw [Matrix.mul_apply, this]
      ring
    · simp [hd k hk]
  have e2 : diagonal d * adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 =
      diagonal (fun k => (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 * adMat F X) k k * d k) *
        adMat F (cT (σ : E →+* E) Y * J) := by
    ext k i
    rw [Matrix.mul_assoc, diagonal_mul, diagonal_mul]
    by_cases hk : k ∈ S
    · have hg' : g⁻¹ ∈ levi σ J Y X S := by rw [levi_swap]; exact inv_mem hg
      rw [GlobalTheory.T.witt_frame_eigenvector_column_form h hJ hW _ (GlobalTheory.T.levi_element_preserves_witt_column_span h hJ (swap h hJ hW) hS hg' k hk) i]
      ring
    · simp [hd k hk]
  calc (matHom _ σ J g).1 * (adMat F X * diagonal d * adMat F (cT (σ : E →+* E) Y * J))
      = ((matHom _ σ J g).1 * adMat F X * diagonal d) * adMat F (cT (σ : E →+* E) Y * J) := by
        simp only [Matrix.mul_assoc]
    _ = adMat F X * (diagonal d * adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1) := by
        rw [e1, e2]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem centre_levi : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {S : Finset (Fin r)}, (∀ k ∈ S, ∀ i, i ≤ k → i ∈ S) → ∀ {l : Fin r → (AF F ⊗[F] E)ˣ} {a : GAd σ J}, (∀ k ∉ S, l k = 1) → IsIdTorusElt σ J X Y l a → a ∈ levi σ J X Y S ∧ ∀ m ∈ levi σ J X Y S, a * m = m * a := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW S hS l a hl ha
  refine ⟨?_, fun m hm => ?_⟩
  · simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf]
    intro k hk
    refine ⟨⟨⟨diagonal fun i => ((l (Fin.castLE k.2 i) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E),
      diagonal fun i => (((l (Fin.castLE k.2 i))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E), by simp [diagonal_mul_diagonal],
      by simp [diagonal_mul_diagonal]⟩, Subgroup.mem_top _, ?_⟩,
      ⟨⟨diagonal fun i => (((conjUnit σ (l (Fin.castLE k.2 i)))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E),
      diagonal fun i => ((conjUnit σ (l (Fin.castLE k.2 i)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E), by simp [diagonal_mul_diagonal],
      by simp [diagonal_mul_diagonal]⟩, Subgroup.mem_top _, ?_⟩⟩
    · ext i j
      have := congrFun (congrFun ha.1 i) (Fin.castLE k.2 j)
      rw [mul_diagonal] at this
      rw [mul_diagonal]
      simpa [Matrix.mul_apply, initCols] using this
    · ext i j
      have := congrFun (congrFun ha.2.1 i) (Fin.castLE k.2 j)
      rw [mul_diagonal] at this
      rw [mul_diagonal]
      simpa [Matrix.mul_apply, initCols] using this
  · apply matHom_injective
    apply Units.ext
    have hd1 : ∀ k ∉ S, ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = 0 := fun k hk => by simp [hl k hk]
    have hd2 : ∀ k ∉ S, (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = 0 := fun k hk => by simp [hl k hk]
    have c1 := comm_block h hJ hW hS hm _ hd1
    have c2 := comm_block h hJ (swap h hJ hW) hS (by rwa [levi_swap]) _ hd2
    simp only [map_mul, Units.val_mul, GlobalTheory.T.idelicFrameTorusElement_matrix_eq h hJ hW ha, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, c1, c2]

end GlobalTheory.IdTorusCent

end
end
