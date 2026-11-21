import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.SymmetricPatternGroup

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.SymCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

section Plain
variable {k : Type*} [Field k] {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}

abbrev sE {n m : Type*} (e : n ≃ m) (c : ℕ) : n ⊕ Fin c ≃ m ⊕ Fin c := e.sumCongr (Equiv.refl _)





theorem mul_embX_mem_R {p : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) (g : GL n k) :
    u * embX c g ∈ R k n c p :=
  mul_mem ((le_sup_right : N k n c p ≤ R k n c p) hu) ((le_sup_left : (embX c).range ≤ R k n c p) ⟨g, rfl⟩)





end Plain

section Local
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}


omit [DecidableEq n] [DecidableEq m] [DecidableEq n'] [DecidableEq m'] in
theorem opE_submatrix [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
    (p : ℕ) (e : n ≃ m) (e' : n' ≃ m') (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix m m' k) :
    opE ψ ν p (fun x => Φ (x.submatrix (sE e c) (sE e' (c + 1)))) x₀ = opE ψ ν p Φ (x₀.submatrix e e') := by
  classical
  have := secondCountable k
  have := t2Space k
  have hf : ∀ r s, Free p (r, s) ↔ Free p (sE e c r, sE e' (c + 1) s) := by
    rintro (r | r) (s | s) <;> exact Iff.rfl
  let σ : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} ≃ {rs : (m ⊕ Fin c) × (m' ⊕ Fin (c + 1)) // Free p rs} :=
    ((sE e c).prodCongr (sE e' (c + 1))).subtypeEquiv fun rs => hf rs.1 rs.2
  have h1 : ∀ f, (affPt p x₀ f).submatrix (sE e c) (sE e' (c + 1)) =
      affPt p (x₀.submatrix e e') (MeasurableEquiv.piCongrLeft (fun _ => k) σ.symm f) := fun f => by
    have h2 : ∀ a, MeasurableEquiv.piCongrLeft (fun _ => k) σ.symm f a = f (σ a) := fun a => by
      obtain ⟨a, rfl⟩ := σ.symm.surjective a
      rw [MeasurableEquiv.piCongrLeft_apply_apply, Equiv.apply_symm_apply]
    ext r s
    have hb : basePt c x₀ (sE e c r) (sE e' (c + 1) s) = basePt c (x₀.submatrix e e') r s := by
      rcases r with r | r <;> rcases s with s | s <;> rfl
    simp only [affPt, submatrix_apply, Matrix.add_apply, hb, of_apply, h2]
    by_cases h : Free p (r, s)
    · rw [dif_pos h, dif_pos ((hf r s).1 h)]; rfl
    · rw [dif_neg h, dif_neg fun H => h ((hf r s).2 H)]
  unfold opE
  rw [← (measurePreserving_piCongrLeft (fun _ => ν) σ.symm).integral_comp']
  simp only [← h1]
  rfl



theorem reGL_symm_mem_KO (e : n ≃ m) {g : GL m k} : (reGL e).symm g ∈ KO k n ↔ g ∈ KO k m :=
  ⟨fun h => ((TypeDatum.full k n).reindex e).le_KO h, fun h => ((TypeDatum.full k m).reindex e.symm).le_KO
    (show (reGL e.symm).symm ((reGL e).symm g) ∈ KO k m by
      have : (reGL e.symm).symm ((reGL e).symm g) = g := by ext i j; simp [reGL_symm_val]
      rwa [this])⟩

theorem exists_reindex_iff (P : TypeDatum k n) (e : n ≃ m) (M : Matrix m m k) :
    (∃ g ∈ (P.reindex e).J, g.val = M) ↔ ∃ g ∈ P.J, g.val = M.submatrix e e := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, hg, rfl⟩
  · rintro ⟨g, hg, h⟩
    refine ⟨reGL e g, ?_, by rw [reGL_val, h]; simp⟩
    change (reGL e).symm (reGL e g) ∈ P.J
    rwa [MulEquiv.symm_apply_apply]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] in
theorem maxM_submatrix (e : n ≃ m) (e' : n' ≃ m') (M : Matrix m m' k) : MaxM (M.submatrix e e') ↔ MaxM M :=
  ⟨fun h i j => by simpa using h (e.symm i) (e'.symm j), fun h _ _ => h _ _⟩

theorem det_reGL_symm (e : n ≃ m) (g : GL m k) :
    Matrix.GeneralLinearGroup.det ((reGL e).symm g) = Matrix.GeneralLinearGroup.det g := by
  rw [← det_reGL e, MulEquiv.apply_symm_apply]


omit [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] in
theorem Phi_reindex (P : TypeDatum k n) (e : n ≃ m) (f : n' ≃ m') (μ : kˣ →* ℂˣ) (x : Matrix (m ⊕ m') m k) :
    (P.reindex e).Phi m' μ x = P.Phi n' μ (x.submatrix (e.sumCongr f) e) := by
  have hi : (P.reindex e).Phi m' μ x ≠ 0 ↔ P.Phi n' μ (x.submatrix (e.sumCongr f) e) ≠ 0 := by
    rw [TypeDatum.Phi_ne_zero_iff, TypeDatum.Phi_ne_zero_iff, exists_reindex_iff, ← maxM_submatrix f e]
    rfl
  by_cases h : (P.reindex e).Phi m' μ x = 0
  · rw [h, not_not.1 (hi.not.1 (not_not.2 h))]
  · obtain ⟨⟨g, hg, eg⟩, h2⟩ := (TypeDatum.Phi_ne_zero_iff _ _).1 h
    rw [TypeDatum.Phi_of_mem _ μ ⟨g, hg⟩ eg h2, TypeDatum.Phi_of_mem _ μ (x := x.submatrix (e.sumCongr f) e) ⟨(reGL e).symm g, hg⟩
      (by rw [reGL_symm_val, eg]; rfl) ((maxM_submatrix f e _).2 h2), det_reGL_symm]
    rfl

end Local

section Iter
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t t' : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] [Fintype t'] [DecidableEq t']

abbrev eI (r : Type*) {t t' : Type*} (f : t ≃ t') (j : ℕ) : Ix r t j ≃ Ix r t' j :=
  (Equiv.refl r).sumCongr ((Equiv.refl (Fin j)).prodCongr f)





variable {κ : Type*} [Fintype κ] [DecidableEq κ] {s : ℕ}



end Iter

end GlobalTheory.SymCompare
