import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormSumLieWordInnerStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SmVecDeriv

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem contDiff_snoc {k : ℕ} :
    ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (k + 1) → ℝ) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using contDiff_snd
  · simp only [Fin.snoc_castSucc]
    fun_prop

theorem snoc_mem {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ} (hXs : ∀ i, Xs i ∈ lieG G)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (i : Fin (k + 1)) :
    (Fin.snoc Xs X : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) i ∈ lieG G := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hX
  · simpa using hXs j

theorem rep_snoc (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hXs : ∀ i, Xs i ∈ lieG G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (t : Fin k → ℝ) (s : ℝ) (u : H) :
    π (List.ofFn fun i => NormedSpace.exp ((Fin.snoc t s : Fin (k + 1) → ℝ) i •
        (Fin.snoc Xs X : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) i)).prod u =
      π (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod (π (NormedSpace.exp (s • X)) u) := by
  rw [← rep_mul hπ (expProd_mem_UH hG hXs t) (exp_mem_UH hG hX s)]
  simp [List.ofFn_succ', -List.ofFn_succ]

theorem contDiff_word (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {w : H} (hw : w ∈ smSub G π)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) {l : List (Matrix (Fin n) (Fin n) ℂ)}
    (hl : ∀ Y ∈ l, Y ∈ lieG G) (k : ℕ) (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (hXs : ∀ i, Xs i ∈ lieG G) :
    ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => π (List.ofFn fun i => NormedSpace.exp (p.1 i • Xs i)).prod
      (word π l (π (NormedSpace.exp (p.2 • X)) w)) := by
  induction l generalizing k with
  | nil =>
    have h1 := (hw (k + 1) (Fin.snoc Xs X) (snoc_mem hXs hX)).comp contDiff_snoc
    convert h1 using 2 with p
    exact (rep_snoc hG hπ hXs hX p.1 p.2 w).symm
  | cons Y l ih =>
    have hl' : ∀ Z ∈ l, Z ∈ lieG G := fun Z hZ => hl Z (by simp [hZ])
    have hY := hl Y (by simp)
    have h1 := ih hl' (k + 1) (Fin.snoc Xs Y) (snoc_mem hXs hY)
    have hs : ContDiff ℝ ∞ fun q : ((Fin k → ℝ) × ℝ) × ℝ =>
        (((Fin.snoc q.1.1 q.2 : Fin (k + 1) → ℝ), q.1.2) : (Fin (k + 1) → ℝ) × ℝ) :=
      (contDiff_snoc.comp (contDiff_fst.fst.prodMk contDiff_snd)).prodMk contDiff_fst.snd
    have h2 : ContDiff ℝ ∞ (Function.uncurry fun (p : (Fin k → ℝ) × ℝ) (r : ℝ) =>
        π (List.ofFn fun i => NormedSpace.exp (p.1 i • Xs i)).prod (π (NormedSpace.exp (r • Y))
          (word π l (π (NormedSpace.exp (p.2 • X)) w)))) := by
      convert h1.comp hs using 1
      funext q
      exact (rep_snoc hG hπ hXs hY q.1.1 q.2 _).symm
    have h3 := (ContDiff.fderiv (𝕜 := ℝ) (m := ∞) (n := ∞) (g := fun _ : (Fin k → ℝ) × ℝ => (0 : ℝ)) h2
      contDiff_const (le_of_eq rfl)).clm_apply (contDiff_const (c := (1 : ℝ)))
    convert h3 using 2 with p
    have hu := word_mem hG hπ hl' (rep_mem hG hπ hw (exp_mem_UH hG hX p.2))
    have h4 := (((π _).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dRep hu hY) :
      HasDerivAt (fun r : ℝ => π (List.ofFn fun i => NormedSpace.exp (p.1 i • Xs i)).prod
        (π (NormedSpace.exp (r • Y)) (word π l (π (NormedSpace.exp (p.2 • X)) w)))) _ 0)
    exact h4.deriv.symm

theorem contDiff_word_curve (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {w : H} (hw : w ∈ smSub G π)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) {l : List (Matrix (Fin n) (Fin n) ℂ)}
    (hl : ∀ Y ∈ l, Y ∈ lieG G) :
    ContDiff ℝ ∞ fun s : ℝ => word π l (π (NormedSpace.exp (s • X)) w) := by
  have h1 := (contDiff_word hG hπ hw hX hl 0 Fin.elim0 (fun i => i.elim0)).comp
    ((contDiff_const (c := (0 : Fin 0 → ℝ))).prodMk (contDiff_id (E := ℝ)))
  simpa [Function.comp_def, rep_one hπ] using h1

theorem hasDerivAt_word : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) → ∀ w ∈ smSub G (trRep σ P), ∀ X ∈ lieG G, HasDerivAt (fun t : ℝ => word (trRep σ P) l ((trRep σ P) (NormedSpace.exp (t • X)) w)) (word (trRep σ P) l (dRep (trRep σ P) X w)) 0 := by
  intro n ε H _ _ _ σ P G hP h hσ l hl w hw X hX
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  have h1 := ((contDiff_word_curve hG hπ hw hX hl).differentiable (by simp) 0).hasDerivAt
  convert h1 using 1
  refine ext_inner_smooth hP h hσ fun u hu => ?_
  obtain ⟨u', -, h2⟩ := word_adjoint hG hπ hl hu
  have h3 := (hasDerivAt_const (0 : ℝ) u).inner ℂ h1
  have h4 := (hasDerivAt_const (0 : ℝ) u').inner ℂ (hasDerivAt_dRep hw hX)
  simp only [h2 _ (rep_mem hG hπ hw (exp_mem_UH hG hX _)), inner_zero_left, add_zero] at h3 h4
  rw [h2 _ (dRep_mem hG hπ hw hX)]
  exact h4.unique h3

end GlobalTheory.SmVecDeriv

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieWord_commutes_oneParameter_derivative : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) → ∀ w ∈ smSub G (trRep σ P), ∀ X ∈ lieG G, HasDerivAt (fun t : ℝ => word (trRep σ P) l ((trRep σ P) (NormedSpace.exp (t • X)) w)) (word (trRep σ P) l (dRep (trRep σ P) X w)) 0 := by
  atlas_forward_decl GlobalTheory.SmVecDeriv.hasDerivAt_word
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultGelf

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}

theorem mem_sm (M : DSModel V S) (τ : D.what₂.Tau) {w : M.H τ} :
    w ∈ M.sm τ ↔ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := by rw [sm_eq]

theorem isURep (M : DSModel V S) (τ : D.what₂.Tau) : IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (trRep (M.σ τ) (M.fr τ)) :=
  isURepOn_trRep (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1

theorem rder_apply (hT : IsMultMap θ M J χ T) [inst : DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (v : M.Vec)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieG (gramAt D V τ)) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRep (trRep (M.σ τ) (M.fr τ)) X u) :
    Rder θ V τ X (T (Function.update v τ u)) = T (Function.update v τ w) := by
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  letI : DecidableEq D.what₂.Tau := fun a b => Classical.propDecidable (a = b)
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  funext x
  obtain ⟨ℓ, hℓ, hℓT⟩ := hT.cont τ v x
  obtain ⟨m, ls, a, hls, ha⟩ := GlobalTheory.T.sobolevContinuousForm_sum_lieWord_inner _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 ℓ hℓ
  have hu := (mem_sm M τ).1 u.2
  have hmem : ∀ t : ℝ, trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u ∈
      smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := fun t =>
    rep_mem hG (isURep M τ) hu (exp_mem_UH hG hX t)
  have h1 : (fun t : ℝ => T (@Function.update _ _ (fun a b => Classical.propDecidable (a = b)) v τ u)
      (x * oneP θ V τ X t)) = fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ := by
    funext t
    rw [← ha _ (hmem t)]
    have h2 := hT.equiv τ _ (exp_mem_UH hG hX t)
      (@Function.update _ _ (fun a b => Classical.propDecidable (a = b)) v τ u) ⟨_, (mem_sm M τ).2 (hmem t)⟩
      (by rw [Function.update_self]; rfl)
    rw [Function.update_idem] at h2
    have h3 := hℓT ⟨_, (mem_sm M τ).2 (hmem t)⟩
    rw [h2] at h3
    exact h3.symm
  have h4 : HasDerivAt (fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ)
      (∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (dRep (trRep (M.σ τ) (M.fr τ)) X u)⟫_ℂ) 0 := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have h5 := (hasDerivAt_const (0 : ℝ) (a i)).inner ℂ
      (GlobalTheory.T.lieWord_commutes_oneParameter_derivative _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (ls i) (hls i) _ hu X hX)
    simpa using h5
  unfold Rder
  rw [h1, h4.deriv, ← hℓT w, hw, ha _ (dRep_mem hG (isURep M τ) hu hX)]

theorem rderC_apply (hT : IsMultMap θ M J χ T) [DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (v : M.Vec)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z u) :
    RderC θ V τ Z (T (Function.update v τ u)) = T (Function.update v τ w) := by
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  have hp := parts_mem hG (gram_herm (M.fr_gram τ)) Z
  have hu := (mem_sm M τ).1 u.2
  have h1 := rder_apply hT τ v hp.1 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ rfl
  have h2 := rder_apply hT τ v hp.2 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ rfl
  have h3 : w = ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ +
      Complex.I • ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ := Subtype.ext hw
  rw [h3, T.map_update_add, T.map_update_smul, ← h1, ← h2]
  rfl

theorem foldr_apply (hT : IsMultMap θ M J χ T) [DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (v : M.Vec)
    (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (u : M.sm τ) :
    ∃ w : M.sm τ, (w : M.H τ) =
        (l.map fun Z => dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z).foldr (fun f acc => f acc) (u : M.H τ) ∧
      (l.map fun Z => RderC θ V τ Z).foldr (fun f acc => f acc) (T (Function.update v τ u)) =
        T (Function.update v τ w) := by
  induction l with
  | nil => exact ⟨u, rfl, rfl⟩
  | cons Z l ih =>
    obtain ⟨w, h1, h2⟩ := ih
    refine ⟨⟨_, (mem_sm M τ).2 (dRepC_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (gram_herm (M.fr_gram τ))
      (isURep M τ) Z ((mem_sm M τ).1 w.2))⟩, ?_, ?_⟩
    · rw [List.map_cons, List.foldr_cons, ← h1]
    · rw [List.map_cons, List.foldr_cons, h2]
      exact rderC_apply hT τ v Z w _ rfl

theorem gelf_apply : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ T : MMap M, IsMultMap θ M J χ T → ∀ [DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (k : ℕ) (v : M.Vec) (w : M.sm τ), (w : M.H τ) = gelfH (gramAt D V τ) (M.rep τ) k (v τ) → gelf θ V τ k (T v) = T (Function.update v τ w) := by
  intro D θ V S M J χ _ T hT _ τ k v w hw
  choose f hf1 hf2 using fun idx : Fin (k + 1) → Fin V.rank =>
    foldr_apply hT τ v (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) (v τ)
  simp only [List.map_ofFn, Function.comp_def, Function.update_eq_self] at hf1 hf2
  have h1 : w = ∑ idx, f idx := by
    refine Subtype.ext ?_
    rw [hw, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun idx _ => (hf1 idx).symm
  rw [h1]
  refine Eq.trans ?_ (map_sum (T.toLinearMap v τ) f Finset.univ).symm
  exact Finset.sum_congr rfl fun idx _ => hf2 idx

end GlobalTheory.MultGelf

end
end
