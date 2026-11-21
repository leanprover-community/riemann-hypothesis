import Formalism.HermitianCurvature.HermitianCurvatureProofs.CvRhoOfParts

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section WS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def wsum (L : List (ℂ × List (Mat k r))) (f : Mat k r → E) (g : Mat k r) : E :=
  (L.map fun cw => cw.1 • Rw cw.2 f g).sum

theorem wsum_nil (f : Mat k r → E) (g : Mat k r) : wsum [] f g = 0 := by
  simp [wsum]

theorem wsum_cons (cw : ℂ × List (Mat k r)) (L : List (ℂ × List (Mat k r))) (f : Mat k r → E) (g : Mat k r) :
    wsum (cw :: L) f g = cw.1 • Rw cw.2 f g + wsum L f g := by
  simp [wsum]

theorem wsum_append (L₁ L₂ : List (ℂ × List (Mat k r))) (f : Mat k r → E) (g : Mat k r) :
    wsum (L₁ ++ L₂) f g = wsum L₁ f g + wsum L₂ f g := by
  simp [wsum, List.map_append, List.sum_append]

theorem wsum_scale (c : ℂ) (L : List (ℂ × List (Mat k r))) (f : Mat k r → E) (g : Mat k r) :
    wsum (L.map fun cw => (c * cw.1, cw.2)) f g = c • wsum L f g := by
  induction L with
  | nil => simp [wsum]
  | cons cw L ih =>
    simp only [List.map_cons, wsum_cons, ih, smul_add, mul_smul]

theorem wsum_flatMap {ι : Type*} (l : List ι) (F : ι → List (ℂ × List (Mat k r))) (f : Mat k r → E) (g : Mat k r) :
    wsum (l.flatMap F) f g = (l.map fun i => wsum (F i) f g).sum := by
  induction l with
  | nil => simp [wsum]
  | cons i l ih => simp [List.flatMap_cons, wsum_append, ih]

def WOK (L : List (ℂ × List (Mat k r))) (j : ℕ) : Prop :=
  ∀ cw ∈ L, (∀ X ∈ cw.2, inLie k r X) ∧ cw.2.length ≤ j

theorem ckOn_Rw_loc {UU : Set (Mat k r)} {w : List (Mat k r)} (hw : ∀ X ∈ w, inLie k r X) {j : ℕ}
    (hj : w.length + 1 ≤ j + 1) {f : Mat k r → E} (hf : CkOn ((j + 1 : ℕ) : ℕ∞) UU f) :
    CkOn 1 UU (Rw w f) := by
  rw [← Dw_wR]
  apply CkOn_Dw
  · intro x hx
    simp only [wR, List.mem_map] at hx
    obtain ⟨X, hX, rfl⟩ := hx
    exact hw X hX
  · apply sCkOn_mono _ hf
    have h1 : (wR w).length = w.length := by simp [wR]
    rw [h1]
    exact_mod_cast (by omega : 1 + w.length ≤ j + 1)

theorem wsum_hasDeriv {O : Set (Mat k r)} {L : List (ℂ × List (Mat k r))} {j : ℕ} (hL : WOK L j)
    {f : Mat k r → E} (hf : CkOn ((j + 1 : ℕ) : ℕ∞) (O ∩ GV k r) f) {X : Mat k r} (hX : inLie k r X)
    {g : Mat k r} (hgO : g ∈ O) (hgG : g ∈ GV k r) :
    HasDerivAt (fun t : ℝ => wsum L f (crv (false, X) g t)) (wsum (L.map fun cw => (cw.1, X :: cw.2)) f g) 0 := by
  have hgU : g ∈ O ∩ GV k r := ⟨hgO, hgG⟩
  have hword : ∀ cw ∈ L, HasDerivAt (fun t : ℝ => Rw cw.2 f (g * NormedSpace.exp ((t : ℂ) • X)))
      (Rw (X :: cw.2) f g) 0 := by
    intro cw hcw
    obtain ⟨h1, h2⟩ := hL cw hcw
    obtain ⟨U, f', hU, hgU', hf', he⟩ := ckOn_Rw_loc h1 (by omega) hf g hgU
    have hγ := Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt g X 0
    have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
    have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hgU')
    have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
        Rw cw.2 f (g * NormedSpace.exp ((t : ℂ) • X)) = f' (g * NormedSpace.exp ((t : ℂ) • X)) := by
      filter_upwards [hmem] with t ht
      exact he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hX t)
    have hf'd : DifferentiableAt ℝ f' (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
      rw [hγ0]
      exact (hf'.contDiffAt (hU.mem_nhds hgU')).differentiableAt (by simp)
    exact ((hf'd.comp (0 : ℝ) hγ.differentiableAt).congr_of_eventuallyEq hev).hasDerivAt
  have key : ∀ L' : List (ℂ × List (Mat k r)), (∀ cw ∈ L', cw ∈ L) →
      HasDerivAt (fun t : ℝ => wsum L' f (g * NormedSpace.exp ((t : ℂ) • X)))
        (wsum (L'.map fun cw => (cw.1, X :: cw.2)) f g) 0 := by
    intro L'
    induction L' with
    | nil => intro _; simpa [wsum] using hasDerivAt_const (0 : ℝ) (0 : E)
    | cons cw L' ih =>
      intro hsub
      simp only [List.map_cons, wsum_cons]
      exact ((hword cw (hsub cw (by simp))).const_smul cw.1).add (ih (fun c hc => hsub c (by simp [hc])))
  have hcrv : ∀ t : ℝ, crv (false, X) g t = g * NormedSpace.exp ((t : ℂ) • X) := fun t => by simp [crv]
  simp only [hcrv]
  exact key L (fun _ h => h)

def stepL (k r : ℕ) (u : ℂ) (c d : Fin (2 * r + k + 1)) (L : List (ℂ × List (Mat k r))) :
    List (ℂ × List (Mat k r)) :=
  (if c = d then L.map (fun cw => (u * cw.1, cw.2)) else []) ++
    ((L.map fun cw => (cw.1, Xa k r c d :: cw.2)) ++
      (L.map fun cw => (cw.1, Xb k r c d :: cw.2)).map fun cw => (Complex.I * cw.1, cw.2))

theorem stepL_ok {u : ℂ} {c d : Fin (2 * r + k + 1)} {L : List (ℂ × List (Mat k r))} {j : ℕ} (hL : WOK L j) :
    WOK (stepL k r u c d L) (j + 1) := by
  intro cw hcw
  have hmem : cw ∈ (if c = d then L.map (fun cw => (u * cw.1, cw.2)) else []) ∨
      cw ∈ L.map (fun cw => (cw.1, Xa k r c d :: cw.2)) ∨
      cw ∈ (L.map fun cw => (cw.1, Xb k r c d :: cw.2)).map fun cw => (Complex.I * cw.1, cw.2) := by
    simpa only [stepL, List.mem_append, or_assoc] using hcw
  rcases hmem with h | h | h
  · by_cases hcd : c = d
    · rw [if_pos hcd] at h
      obtain ⟨cw', hcw', rfl⟩ := List.mem_map.1 h
      obtain ⟨h1, h2⟩ := hL cw' hcw'
      exact ⟨h1, Nat.le_succ_of_le h2⟩
    · rw [if_neg hcd] at h
      simp at h
  · obtain ⟨cw', hcw', rfl⟩ := List.mem_map.1 h
    obtain ⟨h1, h2⟩ := hL cw' hcw'
    refine ⟨?_, by simpa using h2⟩
    intro X hX
    rcases List.mem_cons.1 hX with rfl | hX
    · exact Xa_lie c d
    · exact h1 X hX
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
    obtain ⟨cw', hcw', rfl⟩ := List.mem_map.1 hx
    obtain ⟨h1, h2⟩ := hL cw' hcw'
    refine ⟨?_, by simpa using h2⟩
    intro X hX
    rcases List.mem_cons.1 hX with rfl | hX
    · exact Xb_lie c d
    · exact h1 X hX

theorem top_rep {O : Set (Mat k r)} (hO : IsOpen O) {L : List (ℂ × List (Mat k r))} {j N : ℕ} (hL : WOK L j)
    (hjN : j + 1 ≤ N) (op : (Mat k r → E) → (Mat k r → E))
    (hop : ∀ f : Mat k r → E, CkOn (N : ℕ∞) (O ∩ GV k r) f → ∀ g ∈ O, g ∈ GV k r → op f g = wsum L f g)
    (u : ℂ) (c d : Fin (2 * r + k + 1)) (f : Mat k r → E) (hf : CkOn (N : ℕ∞) (O ∩ GV k r) f)
    (g : Mat k r) (hgO : g ∈ O) (hgG : g ∈ GV k r) :
    Top (Q.EH k r) u c d (op f) g = wsum (stepL k r u c d L) f g := by
  have hf' : CkOn ((j + 1 : ℕ) : ℕ∞) (O ∩ GV k r) f := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf'', he⟩ := hf g₀ hg₀
    exact ⟨U, f', hU, hgU, hf''.of_le (WithTop.coe_le_coe.2 (by exact_mod_cast hjN)), he⟩
  have hcong : ∀ Y, inLie k r Y → RdV Y (op f) g = RdV Y (wsum L f) g := by
    intro Y hY
    have hγ := Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt g Y 0
    have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = g := by simp
    have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • Y) ∈ O :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hO.mem_nhds hgO)
    show deriv (fun t : ℝ => op f (g * NormedSpace.exp ((t : ℂ) • Y))) 0 =
      deriv (fun t : ℝ => wsum L f (g * NormedSpace.exp ((t : ℂ) • Y))) 0
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hmem] with t ht
    exact hop f hf _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hY t)
  have hder : ∀ Y, inLie k r Y → RdV Y (wsum L f) g = wsum (L.map fun cw => (cw.1, Y :: cw.2)) f g := by
    intro Y hY
    have h := wsum_hasDeriv (O := O) hL hf' hY hgO hgG
    have hcrv : (fun t : ℝ => wsum L f (crv (false, Y) g t)) =
        fun t : ℝ => wsum L f (g * NormedSpace.exp ((t : ℂ) • Y)) := by
      funext t
      simp [crv]
    rw [hcrv] at h
    exact h.deriv
  show (if c = d then u • op f g else 0) + Q.EH k r c d (op f) g = wsum (stepL k r u c d L) f g
  have hEH : Q.EH k r c d (op f) g =
      RdV (Xa k r c d) (op f) g + Complex.I • RdV (Xb k r c d) (op f) g := rfl
  rw [hEH, hcong _ (Xa_lie c d), hcong _ (Xb_lie c d), hder _ (Xa_lie c d), hder _ (Xb_lie c d),
    hop f hf g hgO hgG]
  simp only [stepL, wsum_append, wsum_scale]
  split_ifs with hcd
  · rw [wsum_scale]
  · rw [wsum_nil]

def foldL (k r : ℕ) (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) : List (ℂ × List (Mat k r)) :=
  ts.foldr (fun t L => stepL k r t.1 t.2.1 t.2.2 L) [(1, [])]

theorem foldL_ok (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) : WOK (foldL k r ts) ts.length := by
  induction ts with
  | nil =>
    intro cw hcw
    simp [foldL] at hcw
    subst hcw
    simp
  | cons t ts ih =>
    simpa [foldL, List.foldr_cons] using stepL_ok (u := t.1) (c := t.2.1) (d := t.2.2) ih

theorem fold_rep {O : Set (Mat k r)} (hO : IsOpen O) (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ {N : ℕ}, ts.length ≤ N → ∀ f : Mat k r → E, CkOn (N : ℕ∞) (O ∩ GV k r) f → ∀ g ∈ O, g ∈ GV k r →
      (ts.map fun t => Top (Q.EH k r) t.1 t.2.1 t.2.2).foldr (fun T h => T h) f g = wsum (foldL k r ts) f g := by
  induction ts with
  | nil =>
    intro N _ f _ g _ _
    simp [foldL, wsum, Rw]
  | cons t ts ih =>
    intro N hN f hf g hgO hgG
    have hN' : ts.length ≤ N := le_trans (Nat.le_succ _) hN
    have key := top_rep hO (foldL_ok (k := k) (r := r) ts) (by simpa using hN)
      (fun f => (ts.map fun t => Top (Q.EH k r) t.1 t.2.1 t.2.2).foldr (fun T h => T h) f)
      (fun f hf g hgO hgG => ih hN' f hf g hgO hgG) t.1 t.2.1 t.2.2 f hf g hgO hgG
    exact key

def tsOf {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (σ : Equiv.Perm (Fin t)) :
    List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) :=
  List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), p (σ j), q j)

def qmL (k r : ℕ) {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ) : List (ℂ × List (Mat k r)) :=
  (Finset.univ.toList : List (Equiv.Perm (Fin t))).flatMap fun σ =>
    (foldL k r (tsOf p q u σ)).map fun cw => ((((Equiv.Perm.sign σ : ℤ) : ℂ)) * cw.1, cw.2)


theorem qminor_rep {O : Set (Mat k r)} (hO : IsOpen O) {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    (f : Mat k r → E) (hf : CkOn (t : ℕ∞) (O ∩ GV k r) f) (g : Mat k r) (hgO : g ∈ O) (hgG : g ∈ GV k r) :
    qminorOp (Q.EH k r) p q u f g = wsum (qmL k r p q u) f g := by
  have hfold : ∀ σ : Equiv.Perm (Fin t),
      (List.ofFn fun j : Fin t => Top (Q.EH k r) (u - ((j : ℕ) : ℂ)) (p (σ j)) (q j)).foldr (fun T h => T h) f g =
        wsum (foldL k r (tsOf p q u σ)) f g := by
    intro σ
    have := fold_rep hO (tsOf p q u σ) (N := t) (by simp [tsOf]) f hf g hgO hgG
    simpa [tsOf, List.map_ofFn, Function.comp_def] using this
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply, hfold, qmL, wsum_flatMap, wsum_scale, Finset.sum_toList]
  first
  | exact (Finset.sum_toList _ _).symm
  | exact (Finset.sum_map_toList _ _).symm
  | simp [Finset.sum_toList]

def unitL (L : List (ℂ × List (Mat k r))) : List (ℂ × List (Mat k r)) :=
  L.map fun cw => ((((cw.2.map nz).prod : ℝ) : ℂ) * cw.1, cw.2.map nrm)



end WS

theorem mdim0 : Q.mdim k r 0 = 2 * r + k + 1 := by
  rfl




theorem glev0 {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Q.Glev k r 0 := by
  exact ⟨hg, fun a ha => by simp at ha⟩


end Formalism.FourierDecayAlt.P.JFxB








