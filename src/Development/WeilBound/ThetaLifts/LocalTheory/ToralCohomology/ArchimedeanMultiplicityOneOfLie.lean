import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreMain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreLM
import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ExistsTorus
import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLActs
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.EvIHalfTrace
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFock
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLines
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFrame
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLParity
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.PolRange

section
noncomputable section

open FockH1Action PositivityTheory.KReal

namespace PositivityTheory.ThKG.CayleyTransformDarboux

section Gen

variable {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M]

def Lie (act : A →ₗ[ℂ] Module.End ℂ M) : Prop := ∀ X Y, act X * act Y - act Y * act X = act (X * Y - Y * X)

def St (act : A →ₗ[ℂ] Module.End ℂ M) (g : Submodule ℂ A) (N : Submodule ℂ M) : Prop := ∀ Z ∈ g, ∀ x ∈ N, act Z x ∈ N

theorem Lie.comm {act : A →ₗ[ℂ] Module.End ℂ M} (h : Lie act) (X Y : A) (x : M) :
    act X (act Y x) = act Y (act X x) + act (X * Y - Y * X) x := by
  have := LinearMap.congr_fun (h X Y) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
  rw [← this]; abel

def filt (act : A →ₗ[ℂ] Module.End ℂ M) (l : Submodule ℂ A) (V : Submodule ℂ M) : ℕ → Submodule ℂ M
  | 0 => V
  | n + 1 => filt act l V n ⊔ ⨆ Z ∈ l, (filt act l V n).map (act Z)

theorem gen_le {act : A →ₗ[ℂ] Module.End ℂ M} (h : Lie act) {g q l : Submodule ℂ A}
    (hg : ∀ X ∈ g, ∀ Y ∈ g, X * Y - Y * X ∈ g) (hq : q ≤ g) (hl : l ≤ g) (hs : g ≤ q ⊔ l) {V N : Submodule ℂ M}
    (hV : St act q V) (hVN : V ≤ N) (hN : St act l N) : ∃ W, V ≤ W ∧ W ≤ N ∧ St act g W := by
  have up : ∀ n, ∀ Z ∈ l, ∀ x ∈ filt act l V n, act Z x ∈ filt act l V (n + 1) := fun n Z hZ x hx =>
    Submodule.mem_sup_right (Submodule.mem_iSup_of_mem Z (Submodule.mem_iSup_of_mem hZ (Submodule.mem_map_of_mem hx)))
  have mono : ∀ n, filt act l V n ≤ filt act l V (n + 1) := fun n => le_sup_left
  have Q : ∀ n, St act q (filt act l V n) → ∀ Z ∈ g, ∀ x ∈ filt act l V n, act Z x ∈ filt act l V (n + 1) := by
    intro n hn Z hZ x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hs hZ)
    rw [map_add, LinearMap.add_apply]
    exact add_mem (mono n (hn a ha x hx)) (up n b hb x hx)
  have P : ∀ n, St act q (filt act l V n) := by
    intro n
    induction n with
    | zero => exact hV
    | succ n ih =>
      intro Z hZ
      have : filt act l V (n + 1) ≤ (filt act l V (n + 1)).comap (act Z) := by
        refine sup_le (fun x hx => mono n (ih Z hZ x hx)) (iSup₂_le fun Y hY => ?_)
        rintro _ ⟨x, hx, rfl⟩
        rw [Submodule.mem_comap, h.comm]
        exact add_mem (up n Y hY _ (ih Z hZ x hx)) (Q n ih _ (hg Z (hq hZ) Y (hl hY)) x hx)
      exact fun x hx => this hx
  have le : ∀ n, filt act l V n ≤ N := by
    intro n
    induction n with
    | zero => exact hVN
    | succ n ih =>
      refine sup_le ih (iSup₂_le fun Y hY => ?_)
      rintro _ ⟨x, hx, rfl⟩
      exact hN Y hY x (ih hx)
  refine ⟨⨆ n, filt act l V n, le_iSup (filt act l V) 0, iSup_le le, fun Z hZ x hx => ?_⟩
  have : (⨆ n, filt act l V n) ≤ (⨆ n, filt act l V n).comap (act Z) :=
    iSup_le fun n y hy => Submodule.mem_iSup_of_mem (n + 1) (Q n (P n) Z hZ y hy)
  exact this hx

def low (T : Module.End ℂ M) (lam : ℂ) : Submodule ℂ M := ⨆ t : {t : ℝ // 0 < t}, T.eigenspace (lam - (t.1 : ℂ))

theorem shift_eig {act : A →ₗ[ℂ] Module.End ℂ M} (h : Lie act) {H Z : A} {k : ℂ} (hk : H * Z - Z * H = k • Z) {mu : ℂ} {x : M}
    (hx : x ∈ (act H).eigenspace mu) : act Z x ∈ (act H).eigenspace (mu + k) := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  rw [h.comm, hx, hk, map_smul, map_smul, LinearMap.smul_apply, add_smul]

theorem shift_low {act : A →ₗ[ℂ] Module.End ℂ M} (h : Lie act) {H Z : A} {k : ℝ} (h0 : 0 < k)
    (hk : H * Z - Z * H = (-(k : ℂ)) • Z) {lam : ℂ} {V : Submodule ℂ M} (hV : V ≤ (act H).eigenspace lam) :
    ∀ x ∈ V ⊔ low (act H) lam, act Z x ∈ V ⊔ low (act H) lam := by
  have : V ⊔ low (act H) lam ≤ (V ⊔ low (act H) lam).comap (act Z) := by
    refine sup_le (fun x hx => ?_) (iSup_le fun t x hx => ?_)
    · refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem ⟨k, h0⟩ ?_)
      have := shift_eig h hk (hV hx)
      rwa [← sub_eq_add_neg] at this
    · refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem ⟨t.1 + k, add_pos t.2 h0⟩ ?_)
      have := shift_eig h hk hx
      convert this using 2
      push_cast; ring
  exact fun x hx => this hx

theorem low_ker {M' : Type} [AddCommGroup M'] [Module ℂ M'] {T : Module.End ℂ M} {lam : ℂ} (D : M →ₗ[ℂ] M')
    (hD : ∀ x, D (T x) = lam • D x) : low T lam ≤ LinearMap.ker D := by
  refine iSup_le fun t x hx => ?_
  rw [Module.End.mem_eigenspace_iff] at hx
  have := hD x
  rw [hx, map_smul, sub_smul, sub_eq_self, smul_eq_zero] at this
  exact this.resolve_left (by exact_mod_cast t.2.ne')

theorem low_eig {T : Module.End ℂ M} {lam : ℂ} {x : M} (h1 : x ∈ low T lam) (h2 : x ∈ T.eigenspace lam) : x = 0 := by
  have hd := (Module.End.eigenspaces_iSupIndep T) lam
  refine (Submodule.disjoint_def.1 hd) x h2 ?_
  refine (iSup_le fun t => ?_ : low T lam ≤ _) h1
  refine le_iSup₂_of_le (f := fun j (_ : j ≠ lam) => T.eigenspace j) (lam - (t.1 : ℂ)) ?_ le_rfl
  intro e
  rw [sub_eq_self] at e
  exact t.2.ne' (by exact_mod_cast e)

theorem low_map {M' : Type} [AddCommGroup M'] [Module ℂ M'] {T : Module.End ℂ M} {T' : Module.End ℂ M'} {lam : ℂ}
    (φ : M →ₗ[ℂ] M') (hφ : ∀ x, φ (T x) = T' (φ x)) {x : M} (hx : x ∈ low T lam) : φ x ∈ low T' lam := by
  refine (iSup_le fun t y hy => ?_ : low T lam ≤ (low T' lam).comap φ) hx
  refine Submodule.mem_iSup_of_mem t ?_
  rw [Module.End.mem_eigenspace_iff] at hy ⊢
  rw [← hφ, hy, map_smul]

end Gen

section Units

variable {ι I M : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] [AddCommGroup M] [Module ℂ M]

def un (w : ι) (a b : I) : ι → Matrix I I ℂ := Pi.single w (Matrix.single a b 1)

def alg (ι : Type) (r : I → I → Prop) : Submodule ℂ (ι → Matrix I I ℂ) where
  carrier := {Z | ∀ w a b, ¬ r a b → Z w a b = 0}
  add_mem' := fun {x y} hx hy w a b h => by simp [hx w a b h, hy w a b h]
  zero_mem' := fun _ _ _ _ => rfl
  smul_mem' := fun c x hx w a b h => by simp [hx w a b h]

theorem eq_sum (Z : ι → Matrix I I ℂ) : Z = ∑ w, ∑ a, ∑ b, Z w a b • un w a b := by
  ext w a b
  simp only [un, Finset.sum_apply, Pi.smul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single w, Finset.sum_eq_single a, Finset.sum_eq_single b] <;>
    simp +contextual [Pi.single_apply, Matrix.single_apply, eq_comm]

theorem alg_le {r : I → I → Prop} {S : Submodule ℂ (ι → Matrix I I ℂ)} (h : ∀ w a b, r a b → un w a b ∈ S) : alg ι r ≤ S := by
  intro Z hZ
  rw [eq_sum Z]
  refine S.sum_mem fun w _ => S.sum_mem fun a _ => S.sum_mem fun b _ => ?_
  by_cases e : r a b
  · exact S.smul_mem _ (h w a b e)
  · rw [hZ w a b e, zero_smul]; exact S.zero_mem

theorem un_mem {r : I → I → Prop} (w : ι) {a b : I} (h : r a b) : un w a b ∈ alg ι r := by
  intro w' c d hcd
  by_cases e : w' = w
  · subst e
    simp only [un, Pi.single_eq_same, Matrix.single_apply]
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact hcd h
  · simp [un, Pi.single_eq_of_ne e]

theorem alg_br {r : I → I → Prop} (ht : ∀ a b c, r a b → r b c → r a c) :
    ∀ X ∈ alg ι r, ∀ Y ∈ alg ι r, X * Y - Y * X ∈ alg ι r := by
  have m : ∀ X ∈ alg ι r, ∀ Y ∈ alg ι r, X * Y ∈ alg ι r := fun X hX Y hY w a b h => by
    rw [Pi.mul_apply, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases e : r a c
    · rw [hY w c b fun e' => h (ht _ _ _ e e'), mul_zero]
    · rw [hX w a c e, zero_mul]
  exact fun X hX Y hY => sub_mem (m X hX Y hY) (m Y hY X hX)

theorem alg_mono {r r' : I → I → Prop} (h : ∀ a b, r a b → r' a b) : alg ι r ≤ alg ι r' :=
  alg_le fun w a b e => un_mem w (h a b e)

theorem alg_sup {r r₁ r₂ : I → I → Prop} (h : ∀ a b, r a b → r₁ a b ∨ r₂ a b) : alg ι r ≤ alg ι r₁ ⊔ alg ι r₂ :=
  alg_le fun w a b e => (h a b e).elim (fun e => Submodule.mem_sup_left (un_mem w e)) fun e =>
    Submodule.mem_sup_right (un_mem w e)

def stab (act : (ι → Matrix I I ℂ) →ₗ[ℂ] Module.End ℂ M) (N : Submodule ℂ M) : Submodule ℂ (ι → Matrix I I ℂ) where
  carrier := {Z | ∀ x ∈ N, act Z x ∈ N}
  add_mem' := fun {a b} ha hb x hx => by rw [map_add, LinearMap.add_apply]; exact add_mem (ha x hx) (hb x hx)
  zero_mem' := fun x _ => by simp
  smul_mem' := fun c a ha x hx => by rw [map_smul, LinearMap.smul_apply]; exact N.smul_mem c (ha x hx)

theorem st_alg {act : (ι → Matrix I I ℂ) →ₗ[ℂ] Module.End ℂ M} {r : I → I → Prop} {N : Submodule ℂ M}
    (h : ∀ w a b, r a b → ∀ x ∈ N, act (un w a b) x ∈ N) : St act (alg ι r) N :=
  fun _ hZ => (alg_le (S := stab act N) h) hZ

def dg (ι : Type) (h : I → ℝ) : ι → Matrix I I ℂ := fun _ => Matrix.diagonal fun a => (h a : ℂ)

theorem dg_br (h : I → ℝ) (w : ι) (a b : I) : dg ι h * un w a b - un w a b * dg ι h = ((h a - h b : ℝ) : ℂ) • un w a b := by
  ext w' c d
  by_cases e : w' = w
  · subst e
    simp only [un, dg, Pi.sub_apply, Pi.mul_apply, Pi.single_eq_same, Matrix.sub_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Pi.smul_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs with h1
    · obtain ⟨rfl, rfl⟩ := h1; push_cast; ring
    · simp
  · simp [un, Pi.single_eq_of_ne e]

theorem dg_eq (h : I → ℝ) : dg ι h = ∑ w, ∑ a, (h a : ℂ) • un w a a := by
  conv_lhs => rw [eq_sum (dg ι h)]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a] <;> simp +contextual [dg, Matrix.diagonal_apply, eq_comm]

theorem dg_hw {act : (ι → Matrix I I ℂ) →ₗ[ℂ] Module.End ℂ M} (h : I → ℝ) {Λ : ι → I → ℂ} {f : M}
    (hf : ∀ w a, act (un w a a) f = Λ w a • f) : f ∈ (act (dg ι h)).eigenspace (∑ w, ∑ a, h a * Λ w a) := by
  rw [Module.End.mem_eigenspace_iff, dg_eq]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hf, Finset.sum_smul, smul_smul]

theorem cyc_le {act : (ι → Matrix I I ℂ) →ₗ[ℂ] Module.End ℂ M} (hL : Lie act) {sb pos z : I → I → Prop}
    (sbt : ∀ a b c, sb a b → sb b c → sb a c) (sbr : ∀ a, sb a a) (psb : ∀ a b, pos a b → sb a b) (h : I → ℝ)
    (hp : ∀ a b, pos a b → h b ≤ h a) (hz : ∀ a b, z a b → sb a b ∧ h a = h b)
    (hc : ∀ a b, sb a b → h b ≤ h a → (a = b ∨ pos a b) ∨ z a b) {Λ : ι → I → ℂ} {f : M}
    (hf : ∀ w a, act (un w a a) f = Λ w a • f) (hf' : ∀ w a b, pos a b → act (un w a b) f = 0) {N : Submodule ℂ M}
    (hfN : f ∈ N) (hN : ∀ w a b, z a b → ∀ x ∈ N, act (un w a b) x ∈ N) :
    ∃ W, f ∈ W ∧ W ≤ N ⊔ low (act (dg ι h)) (∑ w, ∑ a, h a * Λ w a) ∧ St act (alg ι sb) W := by
  set lam : ℂ := ∑ w, ∑ a, h a * Λ w a
  obtain ⟨V, hV1, hV2, hV3⟩ := gen_le hL (g := alg ι fun a b => sb a b ∧ h b ≤ h a) (q := alg ι fun a b => a = b ∨ pos a b)
    (l := alg ι z) (alg_br fun a b c x y => ⟨sbt _ _ _ x.1 y.1, y.2.trans x.2⟩)
    (alg_mono fun a b e => e.elim (fun e => e ▸ ⟨sbr a, le_rfl⟩) fun e => ⟨psb _ _ e, hp _ _ e⟩)
    (alg_mono fun a b e => ⟨(hz _ _ e).1, (hz _ _ e).2.ge⟩) (alg_sup fun a b e => hc a b e.1 e.2)
    (V := Submodule.span ℂ {f}) (N := N ⊓ (act (dg ι h)).eigenspace lam)
    (st_alg fun w a b e x hx => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      rw [map_smul]
      refine Submodule.smul_mem _ _ ?_
      rcases e with rfl | e
      · rw [hf]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self f)
      · rw [hf' w a b e]; exact zero_mem _)
    ((Submodule.span_singleton_le_iff_mem _ _).2 ⟨hfN, dg_hw h hf⟩)
    (st_alg fun w a b e x hx => ⟨hN w a b e x hx.1, by
      have := shift_eig hL (dg_br h w a b) hx.2
      rwa [(hz _ _ e).2, sub_self, Complex.ofReal_zero, add_zero] at this⟩)
  obtain ⟨W, hW1, hW2, hW3⟩ := gen_le hL (g := alg ι sb) (q := alg ι fun a b => sb a b ∧ h b ≤ h a)
    (l := alg ι fun a b => sb a b ∧ h a < h b) (alg_br sbt) (alg_mono fun a b e => e.1) (alg_mono fun a b e => e.1)
    (alg_sup fun a b e => (le_or_gt (h b) (h a)).imp (fun x => ⟨e, x⟩) fun x => ⟨e, x⟩) hV3
    (N := V ⊔ low (act (dg ι h)) lam) le_sup_left
    (st_alg fun w a b e => shift_low hL (k := h b - h a) (sub_pos.2 e.2)
      (by rw [dg_br]; congr 1; push_cast; ring) (hV2.trans inf_le_right))
  exact ⟨W, hW1 (hV1 (Submodule.mem_span_singleton_self f)), hW2.trans (sup_le_sup_right (hV2.trans inf_le_left) _), hW3⟩

end Units

end PositivityTheory.ThKG.CayleyTransformDarboux

end
end

section
noncomputable section

open FockH1Action PositivityTheory.KReal Polynomial
open scoped TensorProduct

namespace PositivityTheory.ThKG.CayleyTransformDarboux

variable {r s : ℕ}

theorem poly_step {M : Type} [AddCommGroup M] [Module ℂ M] (C : Module.End ℂ M) (c : ℂ) (V : Submodule ℂ M)
    (hinj : ∀ x, C x - c • x ∈ V → x ∈ V) (x : M) :
    ∀ n (p : ℂ[X]), p.natDegree = n → p ≠ 0 → aeval C p x ∈ V → ∃ p' : ℂ[X], p'.eval c ≠ 0 ∧ aeval C p' x ∈ V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hn h0 hp
    by_cases e : p.eval c = 0
    · obtain ⟨p', rfl⟩ := dvd_iff_isRoot.2 e
      have h' : p' ≠ 0 := right_ne_zero_of_mul h0
      refine ih p'.natDegree ?_ p' rfl h' (hinj _ ?_)
      · rw [← hn, natDegree_mul (X_sub_C_ne_zero c) h', natDegree_X_sub_C]; omega
      · simpa [Algebra.algebraMap_eq_smul_one] using hp
    · exact ⟨p, e, hp⟩

theorem aeval_int {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] {C : Module.End ℂ M}
    {C' : Module.End ℂ M'} (φ : M →ₗ[ℂ] M') (h : ∀ x, φ (C x) = C' (φ x)) (p : ℂ[X]) (x : M) :
    φ (aeval C p x) = aeval C' p (φ x) := by
  induction p using Polynomial.induction_on generalizing x with
  | C a => simp [Algebra.algebraMap_eq_smul_one]
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul (aeval C'), aeval_X, aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih, h]

theorem aeval_mem {M : Type} [AddCommGroup M] [Module ℂ M] {C : Module.End ℂ M} {V : Submodule ℂ M} (h : ∀ x ∈ V, C x ∈ V)
    (p : ℂ[X]) {x : M} (hx : x ∈ V) : aeval C p x ∈ V := by
  have := aeval_int (C := C.restrict h) (C' := C) V.subtype (fun _ => rfl) p ⟨x, hx⟩
  rw [show aeval C p x = _ from this.symm]
  exact Subtype.mem _

def hD : Ix r s → ℝ
  | .inl i => -(i : ℝ)
  | .inr i => -(i : ℝ)

theorem hD_pos {a b : Ix r s} (h : posC a b) : hD b < hD a := by
  rcases a with i | i <;> rcases b with j | j <;> simp only [posC] at h <;> simp only [hD] <;>
    exact neg_lt_neg (by exact_mod_cast h)

def one {M : Type} [AddCommGroup M] [Module ℂ M] (act : Mat r s →ₗ[ℂ] Module.End ℂ M) :
    (Unit → Mat r s) →ₗ[ℂ] Module.End ℂ M := act ∘ₗ LinearMap.proj ()

theorem side_one {La : Ix r s → ℚ} {T : Type} [AddCommGroup T] [Module ℂ T] {act : Mat r s →ₗ[ℂ] Module.End ℂ T}
    (h : Side La T act) : ∃ f : T, HwK (units act) La f ∧ genG act (Submodule.span ℂ {f}) = ⊤ ∧
      ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (act' : Mat r s →ₗ[ℂ] Module.End ℂ M), IsLie act' →
        ∀ (J : Type) [Fintype J] (φ : J → T →ₗ[ℂ] M) (x : J → T), (∀ i Y y, φ i (act Y y) = act' Y (φ i y)) →
          HwK (units act') La (∑ i, φ i (x i)) → ∃ c : J → ℂ, ∑ i, φ i (x i) = ∑ i, c i • φ i f := by
  classical
  obtain ⟨hL, hT, A, _, _, _, ρ, ι, f, hadj, hgl, hw, hι, hgen, hs⟩ := h
  have hwf : HwK (units act) La (ι f) :=
    ⟨fun a => by rw [units, ← hι a a (sb_refl a), hw.1, map_smul],
      fun a b e => by rw [units, ← hι a b (sb_of_pos e), hw.2 a b e, map_zero]⟩
  refine ⟨ι f, hwf, hgen, fun M _ _ act' hL' J _ φ x hφ hu => ?_⟩
  let V : Submodule ℂ A := cycK ρ f
  let ρV : Ix r s → Ix r s → Module.End ℂ V := fun a b =>
    if h : sameBlock a b then (ρ a b).restrict (kSt_cycK ρ f a b h) else 0
  have hρV : ∀ a b, sameBlock a b → ∀ v : V, ((ρV a b v : V) : A) = ρ a b v := by
    intro a b h v
    simp only [ρV, dif_pos h]
    rfl
  let ιV : V →ₗ[ℂ] T := ι ∘ₗ V.subtype
  have hιV : ∀ a b, sameBlock a b → ∀ v, ιV (ρV a b v) = act (Eab a b) (ιV v) := by
    intro a b h v
    change ι ((ρV a b v : V) : A) = act (Eab a b) (ι (v : A))
    rw [hρV a b h, hι a b h]
  have hadjV : AdjK ρV := by
    intro a b h u v
    rw [Submodule.coe_inner, Submodule.coe_inner, hρV a b h, hρV b a (sameBlock_symm' h)]
    exact hadj a b h _ _
  set c0 : ℝ := ((casW La : ℚ) : ℝ) with hc0
  have hcc : (c0 : ℂ) = ((casW La : ℚ) : ℂ) := by simp [hc0]
  have hcV : casK ρV = (c0 : ℂ) • (1 : Module.End ℂ V) := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have h1 := casK_intertw (ρ := ρV) (ρ' := ρ) V.subtype (fun a b h v => hρV a b h v) v
    change ((casK ρV v : V) : A) = (c0 : ℂ) • (v : A)
    rw [hcc, ← cas_cyc hgl hw v v.2]
    exact h1
  have hsV : StarK act (LinearMap.range ιV) c0 := by
    intro t ht x hx
    refine hs t ht x (Submodule.span_mono ?_ hx)
    rintro y ⟨a, b, hab, v, ⟨w, rfl⟩, rfl⟩
    exact ⟨a, b, hab, _, ⟨(w : A), rfl⟩, rfl⟩
  obtain ⟨hinj, hfin⟩ := cas_bound_gl act hL ρV hadjV c0 hcV ιV hιV hsV
  have hfV : f ∈ V := self_mem_cycK ρ f
  have hG : genG act (LinearMap.range ιV) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine genG_le' ?_ (genG_stable' _ _)
    rw [Submodule.span_singleton_le_iff_mem]
    exact le_genG' _ _ ⟨⟨f, hfV⟩, rfl⟩
  rw [hG] at hinj hfin
  have hVK : KSt (units act) (LinearMap.range ιV) := by
    rintro a b e _ ⟨v, rfl⟩
    exact ⟨_, hιV a b e v⟩
  have hp : ∀ i, ∃ p : ℂ[X], p.eval (c0 : ℂ) ≠ 0 ∧ aeval (casK (units act)) p (x i) ∈ LinearMap.range ιV := fun i => by
    obtain ⟨F, hF, hxF, hFK⟩ := hfin (x i) trivial
    have hCF : ∀ y ∈ F, casK (units act) y ∈ F := fun y hy => casK_mem hFK hy
    obtain ⟨p, hp1, hp2⟩ := LinearMap.exists_monic_and_aeval_eq_zero ℂ ((casK (units act)).restrict hCF)
    refine poly_step _ _ _ (fun y => hinj y trivial) _ _ p rfl hp1.ne_zero ?_
    have := aeval_int (C := (casK (units act)).restrict hCF) (C' := casK (units act)) F.subtype (fun _ => rfl) p ⟨x i, hxF⟩
    rw [hp2] at this
    rw [show aeval (casK (units act)) p (x i) = _ from this.symm]
    simp
  choose p hp1 hp2 using hp
  have hP : ∀ i, aeval (casK (units act)) (∏ j, p j) (x i) ∈ LinearMap.range ιV := fun i => by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul, Module.End.mul_apply]
    exact aeval_mem (fun y hy => casK_mem hVK hy) _ (hp2 i)
  have hP0 : (∏ j, p j).eval (c0 : ℂ) ≠ 0 := by
    rw [eval_prod]; exact Finset.prod_ne_zero_iff.2 fun j _ => hp1 j
  set u := ∑ i, φ i (x i) with hu0
  have hcu : casK (units act') u = (c0 : ℂ) • u := by rw [hcc]; exact cas_hw (glK_of_lie hL') hu
  have e1 : (∏ j, p j).eval (c0 : ℂ) • u = ∑ i, φ i (aeval (casK (units act)) (∏ j, p j) (x i)) := by
    rw [← Module.End.aeval_apply_of_mem_apply_eq_smul hcu, hu0, map_sum]
    exact Finset.sum_congr rfl fun i _ =>
      (aeval_int (φ i) (casK_intertw (φ i) fun a b _ v => hφ i _ v) _ _).symm
  have hL1 : Lie (one act) := fun X Y => hL (X ()) (Y ())
  have hun : ∀ {N : Type} [AddCommGroup N] [Module ℂ N] (a' : Mat r s →ₗ[ℂ] Module.End ℂ N) (w : Unit) (a b : Ix r s),
      one a' (un w a b) = units a' a b := fun _ _ _ _ => rfl
  obtain ⟨W, hW1, hW2, hW3⟩ := cyc_le hL1 (sb := sameBlock) (pos := posC) (z := fun _ _ => False) (fun _ _ _ => sb_trans) sb_refl
    (fun _ _ => sb_of_pos) hD (fun _ _ e => (hD_pos e).le) (fun _ _ e => e.elim)
    (fun a b e e' => Or.inl ((sb_tri e).imp_right fun x => x.resolve_right fun y => (hD_pos y).not_ge e'))
    (Λ := fun _ a => (La a : ℂ)) (f := ι f) (fun _ a => hwf.1 a) (fun _ a b e => hwf.2 a b e)
    (Submodule.mem_span_singleton_self _) (fun _ _ _ e => e.elim)
  have hVW : LinearMap.range ιV ≤ W := by
    rintro _ ⟨v, rfl⟩
    have : V ≤ W.comap ι := sInf_le ⟨hW1, fun a b e y hy => by
      rw [Submodule.mem_comap, hι a b e]; exact hW3 _ (un_mem () e) _ hy⟩
    exact this v.2
  have hd := fun i => Submodule.mem_sup.1 (hW2 (hVW (hP i)))
  choose y hy z hz hyz using hd
  choose c hc using fun i => Submodule.mem_span_singleton.1 (hy i)
  set lam : ℂ := ∑ _w : Unit, ∑ a, hD a * (La a : ℂ)
  have e2 : (∏ j, p j).eval (c0 : ℂ) • u - ∑ i, c i • φ i (ι f) = ∑ i, φ i (z i) := by
    rw [e1, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← hyz i, ← hc i, map_add, map_smul, add_sub_cancel_left]
  have e3 : ∑ i, φ i (z i) = 0 := by
    refine low_eig (T := one act' (dg Unit hD)) (lam := lam)
      (Submodule.sum_mem _ fun i _ => low_map (φ i) (fun v => hφ i _ v) (hz i)) ?_
    rw [← e2]
    refine sub_mem (Submodule.smul_mem _ _ (dg_hw (act := one act') hD (Λ := fun _ a => (La a : ℂ)) fun _ a => hu.1 a))
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (dg_hw (act := one act') hD (Λ := fun _ a => (La a : ℂ)) fun _ a => ?_))
    change act' (Eab a a) _ = _
    rw [← hφ, show act (Eab a a) (ι f) = _ from hwf.1 a, map_smul]
  rw [e3, sub_eq_zero] at e2
  refine ⟨fun i => ((∏ j, p j).eval (c0 : ℂ))⁻¹ * c i, ?_⟩
  rw [Finset.sum_congr rfl fun i _ => mul_smul _ (c i) (φ i (ι f)), ← Finset.smul_sum, ← e2, inv_smul_smul₀ hP0]

structure HWMod {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (act : (ι → Mat r s) →ₗ[ℂ] Module.End ℂ M) (Λ : ι → Ix r s → ℂ) (f : M) : Prop where
  lie : Lie act
  wt : ∀ w a, act (un w a a) f = Λ w a • f
  pos : ∀ w a b, posC a b → act (un w a b) f = 0
  gen : ∀ W : Submodule ℂ M, f ∈ W → St act ⊤ W → W = ⊤
  one : ∀ u, (∀ w a, act (un w a a) u = Λ w a • u) → (∀ w a b, posC a b → act (un w a b) u = 0) → ∃ c : ℂ, u = c • f

open GlobalTheory.RealLift in
theorem atPl_tprod {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (w : ι) (L : Module.End ℂ (V w)) (y : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ y) = PiTensorProduct.tprod ℂ (Function.update y w (L (y w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases e : i = w
  · subst e; simp
  · simp [Function.update_of_ne e]

open GlobalTheory.RealLift in
theorem sumPl_single {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} [AddCommGroup P] [Module ℂ P]
    (aP : ι → Mat r s →ₗ[ℂ] Module.End ℂ P) (w : ι) (Y : Mat r s) (y : ι → P) :
    sumPl (V := fun _ => P) (fun i => aP i ((Pi.single w Y : ι → Mat r s) i)) (PiTensorProduct.tprod ℂ y) =
      PiTensorProduct.tprod ℂ (Function.update y w (aP w Y (y w))) := by
  rw [sumPl, LinearMap.sum_apply, Finset.sum_eq_single w, atPl_tprod, Pi.single_eq_same]
  · intro i _ e
    rw [atPl_tprod, Pi.single_eq_of_ne e, map_zero, LinearMap.zero_apply, MultilinearMap.map_update_zero]
  · simp

open GlobalTheory.RealLift in
theorem tens_hw {ι P M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup P] [Module ℂ P] [AddCommGroup M] [Module ℂ M]
    {T : ι → Type} [∀ w, AddCommGroup (T w)] [∀ w, Module ℂ (T w)] (La : ι → Ix r s → ℚ)
    (aT : ∀ w, Mat r s →ₗ[ℂ] Module.End ℂ (T w)) (hS : ∀ w, Side (La w) (T w) (aT w))
    (aP : ι → Mat r s →ₗ[ℂ] Module.End ℂ P) (hP : ∀ w, IsLie (aP w)) (mk : ∀ w, P →ₗ[ℂ] T w)
    (hmk : ∀ w, Function.Surjective (mk w)) (hmka : ∀ w Y y, mk w (aP w Y y) = aT w Y (mk w y))
    (q : (⨂[ℂ] _ : ι, P) →ₗ[ℂ] M) (hq : Function.Surjective q)
    (hk : ∀ w y x, mk w x = 0 → q (PiTensorProduct.tprod ℂ (Function.update y w x)) = 0)
    (act : (ι → Mat r s) →ₗ[ℂ] Module.End ℂ M)
    (ha : ∀ Y t, act Y (q t) = q (sumPl (V := fun _ => P) (fun i => aP i (Y i)) t)) :
    ∃ f, HWMod act (fun w a => (La w a : ℂ)) f := by
  classical
  choose f0 hf1 hf2 hf3 using fun w => side_one (hS w)
  choose f hf using fun w => hmk w (f0 w)
  have a1 : ∀ w Y y, act (Pi.single w Y) (q (PiTensorProduct.tprod ℂ y)) =
      q (PiTensorProduct.tprod ℂ (Function.update y w (aP w Y (y w)))) := fun w Y y => by rw [ha, sumPl_single]
  have ext : ∀ {A B : Module.End ℂ M}, (∀ y, A (q (PiTensorProduct.tprod ℂ y)) = B (q (PiTensorProduct.tprod ℂ y))) → A = B := by
    intro A B h
    have : A ∘ₗ q = B ∘ₗ q := PiTensorProduct.ext (MultilinearMap.ext h)
    refine LinearMap.ext fun m => ?_
    obtain ⟨t, rfl⟩ := hq m
    exact LinearMap.congr_fun this t
  have sl : ∀ w y, ∃ φ : T w →ₗ[ℂ] M, ∀ x, φ (mk w x) = q (PiTensorProduct.tprod ℂ (Function.update y w x)) := fun w y =>
    exists_factor (mk w) (hmk w) (q ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap y w) fun x hx => hk w y x hx
  choose φ hφ using sl
  have hφa : ∀ w y Y x, φ w y (aT w Y x) = act (Pi.single w Y) (φ w y x) := fun w y Y x => by
    obtain ⟨x, rfl⟩ := hmk w x
    rw [← hmka, hφ, hφ, a1, Function.update_idem, Function.update_self]
  have hφ0 : ∀ w y, q (PiTensorProduct.tprod ℂ y) = φ w y (mk w (y w)) := fun w y => by rw [hφ, Function.update_eq_self]
  have L1 : ∀ w w' X Y, act (Pi.single w X) * act (Pi.single w' Y) - act (Pi.single w' Y) * act (Pi.single w X) =
      act (Pi.single w X * Pi.single w' Y - Pi.single w' Y * Pi.single w X) := by
    intro w w' X Y
    refine ext fun y => ?_
    by_cases e : w = w'
    · subst e
      rw [← Pi.single_mul, ← Pi.single_mul, ← Pi.single_sub, hφ0 w y, ← hφa, ← (hS w).1 X Y]
      simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, hφa]
    · have z : ∀ {a b : ι} (U V : Mat r s), a ≠ b → (Pi.single a U * Pi.single b V : ι → Mat r s) = 0 := fun {a b} U V h => by
        funext i
        by_cases h' : i = a
        · subst h'; simp [Pi.single_eq_of_ne h]
        · simp [Pi.single_eq_of_ne h']
      rw [z _ _ e, z _ _ (Ne.symm e), sub_zero, map_zero, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
        a1, a1, a1, a1, Function.update_of_ne e, Function.update_of_ne (Ne.symm e), Function.update_comm e, sub_self,
        LinearMap.zero_apply]
  have hL : Lie act := by
    intro X Y
    rw [← Finset.univ_sum_single X, ← Finset.univ_sum_single Y]
    simp only [map_sum, Finset.sum_mul_sum, map_sub]
    rw [Finset.sum_comm (f := fun i j => act (Pi.single i (Y i)) * act (Pi.single j (X j))),
      Finset.sum_comm (f := fun i j => act ((Pi.single i (Y i) : ι → Mat r s) * (Pi.single j (X j) : ι → Mat r s))), ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [L1, map_sub]
  refine ⟨q (PiTensorProduct.tprod ℂ f), hL, fun w a => ?_, fun w a b e => ?_, fun W hW hs => ?_, fun u h1 h2 => ?_⟩
  · rw [hφ0 w, un, ← hφa, hf, show aT w (Matrix.single a a 1) (f0 w) = _ from (hf1 w).1 a, map_smul]
  · rw [hφ0 w, un, ← hφa, hf, show aT w (Matrix.single a b 1) (f0 w) = _ from (hf1 w).2 a b e, map_zero]
  · have key : ∀ S : Finset ι, ∀ y, (∀ i ∉ S, y i = f i) → q (PiTensorProduct.tprod ℂ y) ∈ W := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro y hy; rw [show y = f from funext fun i => hy i (by simp)]; exact hW
      | insert w S hw ih =>
        intro y hy
        have : genG (aT w) (Submodule.span ℂ {f0 w}) ≤ W.comap (φ w y) := by
          refine genG_le' ?_ fun Y x hx => ?_
          · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_comap, ← hf, hφ]
            refine ih _ fun i hi => ?_
            by_cases e : i = w
            · subst e; simp
            · rw [Function.update_of_ne e]; exact hy i (by simp [e, hi])
          · rw [Submodule.mem_comap, hφa]; exact hs _ trivial _ hx
        rw [hf2] at this
        rw [hφ0 w]
        exact this trivial
    rw [eq_top_iff]
    intro m _
    obtain ⟨t, rfl⟩ := hq m
    have : (⊤ : Submodule ℂ (⨂[ℂ] _ : ι, P)) ≤ W.comap q := by
      rw [← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      exact key Finset.univ y fun i hi => absurd (Finset.mem_univ i) hi
    exact this trivial
  · have key : ∀ S : Finset ι, u ∈ Submodule.span ℂ {m | ∃ y, (∀ i ∈ S, y i = f i) ∧ m = q (PiTensorProduct.tprod ℂ y)} := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        obtain ⟨t, rfl⟩ := hq u
        have : (⊤ : Submodule ℂ (⨂[ℂ] _ : ι, P)) ≤ (Submodule.span ℂ
            {m | ∃ y, (∀ i ∈ (∅ : Finset ι), y i = f i) ∧ m = q (PiTensorProduct.tprod ℂ y)}).comap q := by
          rw [← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
          rintro _ ⟨y, rfl⟩
          exact Submodule.subset_span ⟨y, by simp, rfl⟩
        exact this trivial
      | insert w S hw ih =>
        obtain ⟨n, c, g, e⟩ := Submodule.mem_span_set'.1 ih
        choose y hy hy' using fun i => (g i).2
        have e' : ∑ i, φ w (y i) (c i • mk w (y i w)) = u := by
          rw [← e]; exact Finset.sum_congr rfl fun i _ => by rw [map_smul, ← hφ0, hy']
        obtain ⟨c', hc'⟩ := hf3 w M (act ∘ₗ LinearMap.single ℂ (fun _ => Mat r s) w)
          (fun X Y => by
            have := L1 w w X Y
            rwa [← Pi.single_mul, ← Pi.single_mul, ← Pi.single_sub] at this)
          (Fin n) (fun i => φ w (y i)) (fun i => c i • mk w (y i w)) (fun i Y x => hφa w (y i) Y x)
          (by rw [e']; exact ⟨fun a => h1 w a, fun a b h => h2 w a b h⟩)
        rw [← e', hc']
        refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, by rw [← hf, hφ]⟩)
        intro j hj
        by_cases e : j = w
        · subst e; simp
        · rw [Function.update_of_ne e]; exact hy i j ((Finset.mem_insert.1 hj).resolve_left e)
    have : Submodule.span ℂ {m | ∃ y, (∀ i ∈ (Finset.univ : Finset ι), y i = f i) ∧ m = q (PiTensorProduct.tprod ℂ y)} ≤
        Submodule.span ℂ {q (PiTensorProduct.tprod ℂ f)} := Submodule.span_mono (by
      rintro _ ⟨y, hy, rfl⟩
      rw [show y = f from funext fun i => hy i (Finset.mem_univ i)]
      rfl)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (this (key Finset.univ))
    exact ⟨c, hc.symm⟩

end PositivityTheory.ThKG.CayleyTransformDarboux

end
end

section
noncomputable section

open FockH1Action PositivityTheory.KReal

namespace PositivityTheory.ThKG.CayleyTransformDarboux

variable {R S R₁ S₁ : ℕ}

structure Emb (R S R₁ S₁ : ℕ) where
  e : Ix R₁ S₁ → Ix R S
  i : Fin R
  j : Fin S
  ε : ℝ
  ε_ne : ε ≠ 0
  inj : Function.Injective e
  cover : ∀ a, a = .inl i ∨ a = .inr j ∨ ∃ b, e b = a
  ne_i : ∀ b, e b ≠ .inl i
  ne_j : ∀ b, e b ≠ .inr j
  sb : ∀ a b, sameBlock (e a) (e b) ↔ sameBlock a b
  pos : ∀ a b, posC a b → posC (e a) (e b)
  ext : ∀ a b, (a = .inl i ∨ a = .inr j) → sameBlock a (e b) → (0 < ε → posC a (e b)) ∧ (ε < 0 → posC (e b) a)

open Classical in

def Emb.h (m : Emb R S R₁ S₁) (a : Ix R S) : ℝ := if a = .inl m.i ∨ a = .inr m.j then m.ε else 0

theorem Emb.h_e (m : Emb R S R₁ S₁) (b) : m.h (m.e b) = 0 := if_neg (not_or.2 ⟨m.ne_i b, m.ne_j b⟩)

theorem Emb.h_s (m : Emb R S R₁ S₁) {a} (h : a = .inl m.i ∨ a = .inr m.j) : m.h a = m.ε := if_pos h

theorem Emb.cases (m : Emb R S R₁ S₁) (a : Ix R S) : (a = .inl m.i ∨ a = .inr m.j) ∨ ∃ b, m.e b = a := or_assoc.2 (m.cover a)

theorem Emb.eq_of (m : Emb R S R₁ S₁) {a b : Ix R S} (ha : a = .inl m.i ∨ a = .inr m.j) (hb : b = .inl m.i ∨ b = .inr m.j)
    (h : sameBlock a b) : a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> first | rfl | exact h.elim

theorem Emb.sum (m : Emb R S R₁ S₁) {N : Type} [AddCommMonoid N] (g : Ix R S → N) :
    ∑ a, g a = g (.inl m.i) + g (.inr m.j) + ∑ b, g (m.e b) := by
  classical
  have : (Finset.univ : Finset (Ix R S)) = insert (.inl m.i) (insert (.inr m.j) (Finset.univ.image m.e)) := by
    ext a; simpa using m.cover a
  rw [this, Finset.sum_insert, Finset.sum_insert, Finset.sum_image fun a _ b _ h => m.inj h, add_assoc]
  · simpa using m.ne_j
  · simpa using m.ne_i

variable {ι M M₁ : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] [AddCommGroup M₁] [Module ℂ M₁]

structure IsPar (m : Emb R S R₁ S₁) (act : (ι → Mat R S) →ₗ[ℂ] Module.End ℂ M) (act₁ : (ι → Mat R₁ S₁) →ₗ[ℂ] Module.End ℂ M₁)
    (c c' : ι → ℂ) (D : M →ₗ[ℂ] M₁) : Prop where
  levi : ∀ w a b x, D (act (un w (m.e a) (m.e b)) x) = act₁ (un w a b) (D x)
  cpt : ∀ w x, D (act (un w (.inl m.i) (.inl m.i) + un w (.inr m.j) (.inr m.j)) x) = c w • D x
  hyp : ∀ w x, D (act (un w (.inl m.i) (.inr m.j) + un w (.inr m.j) (.inl m.i)) x) = c' w • D x
  cen : ∀ w x, D (act (un w (.inl m.i) (.inl m.i) - un w (.inl m.i) (.inr m.j) + un w (.inr m.j) (.inl m.i) -
    un w (.inr m.j) (.inr m.j)) x) = 0
  n₁ : ∀ w b x, D (act (un w (m.e b) (.inl m.i) - un w (m.e b) (.inr m.j)) x) = 0
  n₂ : ∀ w b x, D (act (un w (.inl m.i) (m.e b) + un w (.inr m.j) (m.e b)) x) = 0

theorem IsPar.sub {m : Emb R S R₁ S₁} {act : (ι → Mat R S) →ₗ[ℂ] Module.End ℂ M}
    {act₁ : (ι → Mat R₁ S₁) →ₗ[ℂ] Module.End ℂ M₁} {c c' : ι → ℂ} {D D' : M →ₗ[ℂ] M₁} (h : IsPar m act act₁ c c' D)
    (h' : IsPar m act act₁ c c' D') (t : ℂ) : IsPar m act act₁ c c' (D' - t • D) := by
  refine ⟨fun w a b x => ?_, fun w x => ?_, fun w x => ?_, fun w x => ?_, fun w b x => ?_, fun w b x => ?_⟩ <;>
    rw [LinearMap.sub_apply, LinearMap.smul_apply]
  · rw [h.levi, h'.levi, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul]
  · rw [h.cpt, h'.cpt, LinearMap.sub_apply, LinearMap.smul_apply, smul_sub, smul_comm t]
  · rw [h.hyp, h'.hyp, LinearMap.sub_apply, LinearMap.smul_apply, smul_sub, smul_comm t]
  · rw [h.cen, h'.cen, smul_zero, sub_zero]
  · rw [h.n₁, h'.n₁, smul_zero, sub_zero]
  · rw [h.n₂, h'.n₂, smul_zero, sub_zero]

theorem HWMod.centre {act : (ι → Mat R S) →ₗ[ℂ] Module.End ℂ M} {Λ : ι → Ix R S → ℂ} {f : M} (h : HWMod act Λ f) (w : ι) (x : M) :
    ∑ a, act (un w a a) x = (∑ a, Λ w a) • x := by
  have e : ∑ a, un w a a = (Pi.single w 1 : ι → Mat R S) := by
    funext i
    by_cases h : i = w
    · subst h
      simp only [un, Finset.sum_apply, Pi.single_eq_same]
      ext a b
      simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
      split_ifs with e
      · subst e; simp
      · exact Finset.sum_eq_zero fun c _ => if_neg fun h => e (h.1.symm.trans h.2)
    · simp [un, Pi.single_eq_of_ne h]
  have : (act (Pi.single w 1)).eigenspace (∑ a, Λ w a) = ⊤ := by
    refine h.gen _ ?_ fun Z _ y hy => ?_
    · rw [Module.End.mem_eigenspace_iff, ← e]
      simp only [map_sum, LinearMap.sum_apply, h.wt, Finset.sum_smul]
    · have := shift_eig h.lie (H := Pi.single w 1) (Z := Z) (k := 0) (by
        funext i
        by_cases h : i = w
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]) hy
      rwa [add_zero] at this
  have hx : x ∈ (act (Pi.single w 1)).eigenspace (∑ a, Λ w a) := this ▸ Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff, ← e, map_sum, LinearMap.sum_apply] at hx
  exact hx

theorem par_zero {m : Emb R S R₁ S₁} {act : (ι → Mat R S) →ₗ[ℂ] Module.End ℂ M}
    {act₁ : (ι → Mat R₁ S₁) →ₗ[ℂ] Module.End ℂ M₁} {Λ : ι → Ix R S → ℂ} {f : M} (hM : HWMod act Λ f) {c c' : ι → ℂ}
    {D : M →ₗ[ℂ] M₁} (hD : IsPar m act act₁ c c' D) (hc : ∀ w, c w = Λ w (.inl m.i) + Λ w (.inr m.j)) (h0 : D f = 0) :
    D = 0 := by
  have hs : ∀ (g : Ix R S → ℂ), ∑ a, (m.h a : ℂ) * g a = m.ε * (g (.inl m.i) + g (.inr m.j)) := fun g => by
    rw [m.sum, m.h_s (.inl rfl), m.h_s (.inr rfl)]; simp [m.h_e, mul_add]
  have hlow : low (act (dg ι m.h)) (∑ w, ∑ a, m.h a * Λ w a) ≤ LinearMap.ker D := by
    refine low_ker D fun x => ?_
    rw [dg_eq]
    simp only [map_sum, LinearMap.sum_apply, Finset.sum_smul, hs]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← hc, mul_smul, ← hD.cpt, m.sum, m.h_s (.inl rfl), m.h_s (.inr rfl)]
    simp [m.h_e]
  obtain ⟨V, hV1, hV2, hV3⟩ := cyc_le hM.lie (sb := sameBlock) (pos := posC)
    (z := fun a b => sameBlock a b ∧ ∃ a' b', m.e a' = a ∧ m.e b' = b) (fun _ _ _ => sb_trans) sb_refl (fun _ _ => sb_of_pos) m.h
    (fun a b e => by
      rcases m.cases a with ha | ⟨a, rfl⟩ <;> rcases m.cases b with hb | ⟨b, rfl⟩
      · rw [m.h_s ha, m.h_s hb]
      · rw [m.h_s ha, m.h_e]
        exact not_lt.1 fun h => pos_asymm e ((m.ext a b ha (sb_of_pos e)).2 h)
      · rw [m.h_s hb, m.h_e]
        exact not_lt.1 fun h => pos_asymm e ((m.ext b a hb (sb_symm (sb_of_pos e))).1 h)
      · rw [m.h_e, m.h_e])
    (by rintro _ _ ⟨e, a, b, rfl, rfl⟩; exact ⟨e, by rw [m.h_e, m.h_e]⟩)
    (fun a b e e' => by
      rcases m.cases a with ha | ⟨a, rfl⟩ <;> rcases m.cases b with hb | ⟨b, rfl⟩
      · exact .inl (.inl (m.eq_of ha hb e))
      · rw [m.h_s ha, m.h_e] at e'
        exact .inl (.inr ((m.ext a b ha e).1 (e'.lt_of_ne m.ε_ne.symm)))
      · rw [m.h_s hb, m.h_e] at e'
        exact .inl (.inr ((m.ext b a hb (sb_symm e)).2 (e'.lt_of_ne m.ε_ne)))
      · exact .inr ⟨e, a, b, rfl, rfl⟩)
    hM.wt hM.pos (N := LinearMap.ker D) h0
    (by
      rintro w _ _ ⟨-, a, b, rfl, rfl⟩ x hx
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hD.levi, hx, map_zero])
  have hVk : V ≤ LinearMap.ker D := hV2.trans (sup_le le_rfl hlow)
  set K := alg ι (sameBlock (p := R) (q := S))
  set P := stab act (LinearMap.ker D)
  have mP : ∀ Z (t : ℂ), (∀ x, D (act Z x) = t • D x) → Z ∈ K ⊔ P := fun Z t h => Submodule.mem_sup_right fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢; rw [h, hx, smul_zero]
  have mK : ∀ w {a b : Ix R S}, sameBlock a b → un w a b ∈ K ⊔ P := fun w _ _ e => Submodule.mem_sup_left (un_mem w e)
  have hij : ∀ w, un w (.inl m.i) (.inr m.j) ∈ K ⊔ P ∧ un w (.inr m.j) (.inl m.i) ∈ K ⊔ P := fun w => by
    have a1 := mP _ _ (hD.hyp w)
    have a2 := mP _ 0 fun x => (hD.cen w x).trans (zero_smul _ _).symm
    have a3 := mK w (sb_refl (.inl m.i : Ix R S))
    have a4 := mK w (sb_refl (.inr m.j : Ix R S))
    constructor
    · convert Submodule.smul_mem _ (1 / 2 : ℂ) (sub_mem (add_mem (sub_mem a1 a2) a3) a4) using 1
      module
    · convert Submodule.smul_mem _ (1 / 2 : ℂ) (add_mem (sub_mem (add_mem a1 a2) a3) a4) using 1
      module
  have tri : ∀ b : Ix R S, sameBlock b (.inl m.i) ∨ sameBlock b (.inr m.j) := fun b => by cases b <;> simp [sameBlock]
  have hb : ∀ w b, (un w (m.e b) (.inl m.i) ∈ K ⊔ P ∧ un w (m.e b) (.inr m.j) ∈ K ⊔ P) ∧
      un w (.inl m.i) (m.e b) ∈ K ⊔ P ∧ un w (.inr m.j) (m.e b) ∈ K ⊔ P := fun w b => by
    have a1 := mP _ 0 fun x => (hD.n₁ w b x).trans (zero_smul _ _).symm
    have a2 := mP _ 0 fun x => (hD.n₂ w b x).trans (zero_smul _ _).symm
    rcases tri (m.e b) with e | e
    · have a3 := mK w e
      have a4 := mK w (sb_symm e)
      exact ⟨⟨a3, by simpa using sub_mem a3 a1⟩, a4, by simpa using sub_mem a2 a4⟩
    · have a3 := mK w e
      have a4 := mK w (sb_symm e)
      exact ⟨⟨by simpa using add_mem a1 a3, a3⟩, by simpa using sub_mem a2 a4, a4⟩
  have top : (⊤ : Submodule ℂ (ι → Mat R S)) ≤ K ⊔ P := by
    refine le_trans (fun Z _ => ?_ : _ ≤ alg ι fun _ _ => True) (alg_le fun w a b _ => ?_)
    · exact fun _ _ _ h => (h trivial).elim
    · rcases m.cover a with rfl | rfl | ⟨a, rfl⟩ <;> rcases m.cover b with rfl | rfl | ⟨b, rfl⟩
      exacts [mK w (sb_refl _), (hij w).1, (hb w b).2.1, (hij w).2, mK w (sb_refl _), (hb w b).2.2, (hb w a).1.1, (hb w a).1.2,
        Submodule.mem_sup_right fun x hx => by rw [LinearMap.mem_ker] at hx ⊢; rw [hD.levi, hx, map_zero]]
  obtain ⟨W, hW1, hW2, hW3⟩ := gen_le hM.lie (g := ⊤) (q := K) (l := P) (fun _ _ _ _ => trivial) le_top le_top top hV3 hVk
    fun Z hZ => hZ
  rw [hM.gen W (hW1 hV1) hW3] at hW2
  exact LinearMap.ker_eq_top.1 (top_le_iff.1 hW2)

theorem par_line {m : Emb R S R₁ S₁} {act : (ι → Mat R S) →ₗ[ℂ] Module.End ℂ M}
    {act₁ : (ι → Mat R₁ S₁) →ₗ[ℂ] Module.End ℂ M₁} {Λ : ι → Ix R S → ℂ} {Λ₁ : ι → Ix R₁ S₁ → ℂ} {f : M} {f₁ : M₁}
    (hM : HWMod act Λ f) (hM₁ : HWMod act₁ Λ₁ f₁) (hΛ : ∀ w b, Λ w (m.e b) = Λ₁ w b) {c c' : ι → ℂ}
    {D D' : M →ₗ[ℂ] M₁} (hD : IsPar m act act₁ c c' D) (hD' : IsPar m act act₁ c c' D') (h0 : D ≠ 0) :
    ∃ t : ℂ, D' = t • D := by
  obtain ⟨x, hx⟩ : ∃ x, D x ≠ 0 := by
    by_contra h
    exact h0 (LinearMap.ext fun x => not_not.1 fun e => h ⟨x, e⟩)
  have hc : ∀ w, c w = Λ w (.inl m.i) + Λ w (.inr m.j) := fun w => by
    have e := congrArg D (hM.centre w x)
    rw [m.sum, m.sum, map_add, ← LinearMap.add_apply, ← map_add act, hD.cpt, map_sum, map_smul] at e
    simp only [hD.levi, hM₁.centre, hΛ] at e
    rw [← add_smul] at e
    exact add_right_cancel (smul_left_injective ℂ hx e)
  have val : ∀ {E : M →ₗ[ℂ] M₁}, IsPar m act act₁ c c' E → ∃ t : ℂ, E f = t • f₁ := fun {E} hE =>
    hM₁.one _ (fun w a => by rw [← hE.levi, hM.wt, map_smul, hΛ]) fun w a b e => by
      rw [← hE.levi, hM.pos w _ _ (m.pos a b e), map_zero]
  obtain ⟨t, ht⟩ := val hD
  obtain ⟨t', ht'⟩ := val hD'
  have t0 : t ≠ 0 := fun e => h0 (par_zero hM hD hc (by rw [ht, e, zero_smul]))
  refine ⟨t' / t, sub_eq_zero.1 (par_zero hM (hD.sub hD' _) hc ?_)⟩
  rw [LinearMap.sub_apply, LinearMap.smul_apply, ht, ht', smul_smul, div_mul_cancel₀ _ t0, sub_self]

end PositivityTheory.ThKG.CayleyTransformDarboux

end
end

section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open FockH1Action (Mat Ix fockAct1 fockAct2 cPair)
open Formalism.BasicNotions.TH (upq Jm)
open PositivityTheory.KReal ReciprocityTheory.ChartRestriction.G.ThK.Real

namespace PositivityTheory.ThKG.CayleyTransformDarboux

structure Dic : Prop where
  laws : ActsLaws
  fock : FockEx
  range : PolRange
  fst : LieFirst
  snd : LieSecond
  line : LineEx
  frame : FrameEx
  even_im_hermitian_sub : Parity

theorem Jm_eq (r s : ℕ) : Jm r s = Matrix.diagonal (Sum.elim (fun _ => 1) fun _ => -1) := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> simp [Jm, Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply, neg_ite]

theorem Jm_sq (r s : ℕ) : Jm r s * Jm r s = 1 := by
  rw [Jm_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; cases a <;> simp

theorem Jm_star (r s : ℕ) : (Jm r s)ᴴ = Jm r s := by
  rw [Jm_eq, Matrix.diagonal_conjTranspose]
  congr 1; funext a; cases a <;> simp

theorem upq_split {r s : ℕ} (Y : Mat r s) : ∃ Y₁ ∈ upq r s, ∃ Y₂ ∈ upq r s, Y = Y₁ + Complex.I • Y₂ := by
  have e1 : ∀ Z : Mat r s, Z * Jm r s * Jm r s = Z := fun Z => by rw [Matrix.mul_assoc, Jm_sq, Matrix.mul_one]
  have e2 : ∀ Z : Mat r s, Jm r s * (Jm r s * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, Jm_sq, Matrix.one_mul]
  refine ⟨(1 / 2 : ℂ) • (Y - Jm r s * Yᴴ * Jm r s), ?_, (-Complex.I / 2) • (Y + Jm r s * Yᴴ * Jm r s), ?_, ?_⟩
  · simp only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Jm_star,
      Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_assoc, Jm_sq, Matrix.mul_one, e2]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp]
    module
  · simp only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Jm_star,
      Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc, Jm_sq, Matrix.mul_one, e2]
    rw [show star (-Complex.I / 2 : ℂ) = Complex.I / 2 by simp]
    module
  · rw [smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I]
    module

theorem zero_upq (r s : ℕ) : (0 : Mat r s) ∈ upq r s := by simp [upq]

theorem single_upq {ι : Type} [DecidableEq ι] {r s : ℕ} (w : ι) {Y : Mat r s} (h : Y ∈ upq r s) (i : ι) :
    (Pi.single w Y : ι → Mat r s) i ∈ upq r s := by
  by_cases e : i = w
  · subst e; simpa using h
  · simpa [Pi.single_eq_of_ne e] using zero_upq r s

def sumL {ι P : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup P] [Module ℂ P] {r s : ℕ}
    (aP : ι → Mat r s →ₗ[ℂ] Module.End ℂ P) : (ι → Mat r s) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] _ : ι, P) :=
  ∑ w, (PiTensorProduct.mapMultilinear ℂ (fun _ : ι => P) (fun _ => P)).toLinearMap (fun _ => LinearMap.id) w ∘ₗ aP w ∘ₗ
    LinearMap.proj w

theorem sumL_eq {ι P : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup P] [Module ℂ P] {r s : ℕ}
    (aP : ι → Mat r s →ₗ[ℂ] Module.End ℂ P) (Y : ι → Mat r s) :
    sumL aP Y = sumPl (V := fun _ => P) fun i => aP i (Y i) := by
  rw [sumL, LinearMap.sum_apply]; rfl

theorem ker_stable {ι V : Type} [AddCommGroup V] [Module ℂ V] {r s : ℕ} (L : (ι → Mat r s) →ₗ[ℂ] Module.End ℂ V)
    (N N' : Submodule ℂ V) (h : ∀ Y, (∀ w, Y w ∈ upq r s) → ∀ x ∈ N, L Y x ∈ N') (Y) : ∀ x ∈ N, L Y x ∈ N' := by
  choose Y₁ h₁ Y₂ h₂ e using fun w => upq_split (Y w)
  intro x hx
  rw [show Y = Y₁ + Complex.I • Y₂ from funext e, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  exact add_mem (h _ h₁ x hx) (N'.smul_mem _ (h _ h₂ x hx))

theorem exists_act {A V M : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    (L : A →ₗ[ℂ] Module.End ℂ V) (q : V →ₗ[ℂ] M) (hq : Function.Surjective q)
    (h : ∀ Y, ∀ x ∈ LinearMap.ker q, L Y x ∈ LinearMap.ker q) :
    ∃ act : A →ₗ[ℂ] Module.End ℂ M, ∀ Y t, act Y (q t) = q (L Y t) := by
  choose a ha using fun Y => exists_factor q hq (q ∘ₗ L Y) (h Y)
  refine ⟨⟨⟨a, fun X Y => LinearMap.ext fun m => ?_⟩, fun c X => LinearMap.ext fun m => ?_⟩, ha⟩
  · obtain ⟨t, rfl⟩ := hq m
    simp [ha]
  · obtain ⟨t, rfl⟩ := hq m
    simp [ha]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_map {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem piInf_unit_ne {w : InfinitePlace F} (τ : EmbOver E w) (z : (AE F E)ˣ) : piInf τ (z : AE F E) ≠ 0 := fun e => by
  have := congrArg (piInf τ) z.mul_inv
  rw [map_mul, e, zero_mul, map_one] at this
  exact zero_ne_one this

theorem hasExp_div (τ : ∀ w : InfinitePlace F, EmbOver E w) {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (fun w => m w - m' w) := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h0 := piInf_unit_ne (τ w) z
  rw [zpow_sub₀ (div_ne_zero h0 (by exact_mod_cast norm_ne_zero_iff.2 h0))]

theorem actsD_zero {κ κ' : Type} [Fintype κ] {G : Type} [Monoid G] (om : G →* Module.End ℂ ((κ → AF F) → ℂ)) (g : ℝ → G) :
    ActsD (evI F) (fun t => om (g t)) (0 : SInf F κ) (0 : SInf F κ) := by
  intro r _ x
  have : tens (evI F) (0 : SInf F κ) r = 0 := by funext y; simp [tens]
  simp only [this, map_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _

def lamW (B : Base F E) (P Q R S : ℕ) (w : InfinitePlace F) : Ix R S → ℚ
  | .inl k => (if (k : ℕ) < P then ((B.mα w - B.mβ w : ℤ) : ℚ) / 2 - cPair R S else 0) + cPair P Q + (B.mβ w : ℚ) / 2
  | .inr l => (if (l : ℕ) < Q then ((B.mα w - B.mβ w : ℤ) : ℚ) / 2 + cPair R S else 0) - cPair P Q + (B.mβ w : ℚ) / 2

theorem exists_mod (hD : Dic) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om om'} {Rm : RealMaps F a a'}
    (hT : IsTriple B G X om om') (hR : IsRealMaps B G om om' Rm) {R S : ℕ} (eR : R + G.p + G.q = a + a') (eS : S = G.p + G.q)
    (C : InfinitePlace F → Matrix (Fin (a + a')) (Ix R S) ℂ)
    (hC : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w)) (hCθ : ∀ w, G.W.θ w * C w = C w * Jm R S) :
    ∃ (act : (InfinitePlace F → Mat R S) →ₗ[ℂ] Module.End ℂ Rm.Pi) (f₀ : Rm.Pi),
      HWMod act (fun w c => (lamW B (a - G.p) G.p R S w c : ℂ)) f₀ ∧
      ∀ γ ∈ Lines σ G.W, ∀ Y, IsGen B.emb C γ Y → ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ : SInf F _,
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ Rm.p f₁ = act Y (Rm.p f) := by
  have par := hD.even_im_hermitian_sub F E σ B a a' G X om om' hT
  obtain ⟨hb, hg, hc, hw, -⟩ := hT
  have e1 := hg.eBig
  have e2 := hg.aBig
  obtain ⟨d2, hd2⟩ := hg.even
  choose A hA hAθ using fun w => hD.frame _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map, one_smul]; exact hA w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC⟩
  obtain ⟨Φ, hΦ⟩ := hD.fock F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hD.range F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hW2 := hD.snd F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1 hc.expβ
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := hD.fst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (hasExp_div B.emb hc.expβ hc.expα)
  have mem : ∀ T, Φ T ∈ G.M.Pol B.ψ B.emb := fun T => hr ▸ LinearMap.mem_range_self Φ T
  let q := Rm.p ∘ₗ Φ
  have hq : Function.Surjective q := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, hr]; exact hR.quot.onto
  let aP := fun w : InfinitePlace F => twAct (a - G.p) G.p R S ((B.mβ w : ℂ) / 2)
  let a1 : InfinitePlace F → Mat (a - G.p) G.p →ₗ[ℂ] Module.End ℂ (FockH1Action.Pol (a - G.p) G.p R S) := fun w =>
    fockAct1 _ _ _ _ + ((((B.mβ w - B.mα w : ℤ) : ℂ) / 2) • Matrix.traceLinearMap _ ℂ ℂ).smulRight 1
  have s2 : ∀ γ ∈ Lines σ G.W, ∀ Y, IsGen B.emb C γ Y → ∀ T,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T) (Φ (sumL aP Y T)) := fun γ hγ Y hY T => by
    rw [sumL_eq]
    exact (hD.laws F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) (hW2 γ hγ Y hY T)
  have s1 : ∀ Y T, q (sumL a1 Y T) = 0 := fun Y T => by
    refine ker_stable (sumL a1) ⊤ (LinearMap.ker q) (fun Y hY T _ => ?_) Y T trivial
    obtain ⟨γ, hγ, hgen⟩ := hD.line F E σ _ _ _ B.emb _ 1 A hb.cm hA1 Y hY
    rw [sumL_eq]
    exact hR.quot.lie γ hγ _ (mem T) _ ((hD.laws F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) (hW1 γ hγ Y hgen T))
  obtain ⟨act, ha⟩ := exists_act (sumL aP) q hq (ker_stable _ _ _ fun Y hY T hT => by
    obtain ⟨γ, hγ, hgen⟩ := hD.line F E σ _ _ _ B.emb _ Complex.I C hb.cm hC Y hY
    exact (hR.lie γ hγ _ (mem T) 0 (zero_mem _) _ 0 (s2 γ hγ Y hgen T) (actsD_zero (κ' := Unit) om' _)
      (hT.trans (map_zero _).symm)).trans (map_zero _))
  have side : ∀ w, Side (lamW B (a - G.p) G.p R S w) (ThC (a - G.p) G.p R S ((((B.mα w - B.mβ w : ℤ) : ℚ) / 2 : ℚ) : ℂ))
      (thAct _ _ _ _ _ ((B.mβ w : ℂ) / 2)) := fun w => by
    obtain ⟨k, hk⟩ := par w
    have hκ := hg.kappa w
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k - d2 + S by omega)
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k + d2 - S by omega)
    have hRq : (R : ℚ) + S = d2 + d2 := by exact_mod_cast (show R + S = d2 + d2 by omega)
    have hkq : ((B.mα w - B.mβ w : ℤ) : ℚ) / 2 = k := by rw [hk]; push_cast; ring
    have hn' : (k : ℚ) - d2 + S = n := by exact_mod_cast hn
    have hm' : (k : ℚ) + d2 - S = m := by exact_mod_cast hm
    have h1 : ((B.mα w - B.mβ w : ℤ) : ℚ) / 2 = n + cPair R S := by rw [hkq, cPair]; linarith
    have h2 : ((B.mα w - B.mβ w : ℤ) : ℚ) / 2 = m - cPair R S := by rw [hkq, cPair]; linarith
    have b1 : (G.p : ℚ) < ((a - G.p : ℕ) : ℚ) := by exact_mod_cast (show G.p < a - G.p by omega)
    have b2 : (((a - G.p : ℕ) : ℚ)) < m + G.p := by exact_mod_cast (show a - G.p < m + G.p by omega)
    have n0 : 0 < n := by omega
    have m0 : 0 < m := by omega
    have := side_of _ ((B.mβ w : ℂ) / 2) _ ((B.mβ w : ℚ) / 2) rfl (by push_cast; rfl) _
      (comb_pos (p := a - G.p) (q := G.p) (r := R) (s := S) (by omega) (by omega) n0 m0 _ _ h1 h2
        (by rw [cPair]; have : (0 : ℚ) ≤ n := by positivity
            linarith) (by rw [cPair]; linarith))
      (nontrivial_of_pair _ _ rfl (pair_pos (by omega) (by omega) n0 m0 _ h1 h2))
    convert this using 1
    funext c
    rcases c with c | c <;> simp only [lamW, laPos] <;> split_ifs <;> linarith
  obtain ⟨f₀, hf₀⟩ := tens_hw _ _ side aP (fun w => lie_tw _ _ _ _ _) (fun w => thMkC _ _ _ _ _)
    (fun w => Submodule.mkQ_surjective _) (fun w Y y => (thAct_mk _ _ _ _ _ _ Y y).symm) q hq
    (fun w y x hx => by
      have hx' := (Submodule.Quotient.mk_eq_zero _).1 hx
      refine (iSup_le ?_ : _ ≤ LinearMap.ker (q ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap y w)) hx'
      rintro Z _ ⟨x, rfl⟩
      have := s1 (Pi.single w Z) (PiTensorProduct.tprod ℂ (Function.update y w x))
      rw [sumL_eq, sumPl_single, Function.update_idem, Function.update_self] at this
      refine Eq.trans ?_ this
      simp only [LinearMap.comp_apply, MultilinearMap.toLinearMap_apply]
      congr 3
      simp only [a1, act1, chiTr, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
        LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, smul_eq_mul, sub_eq_add_neg, ← neg_smul]
      congr 2
      push_cast; ring)
    act (fun Y t => by rw [ha, sumL_eq])
  refine ⟨act, f₀, hf₀, fun γ hγ Y hY f hf => ?_⟩
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  exact ⟨_, s2 γ hγ Y hY T, (ha Y T).symm⟩

end PositivityTheory.ThKG.CayleyTransformDarboux

end
end

section
noncomputable section

open scoped Matrix Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open FockH1Action (Mat Ix sameBlock posC)
open Formalism.BasicNotions.TH (upq Jm)

namespace PositivityTheory.ThKG.CayleyTransformDarboux

section Exp

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem hasSum_exp (A : Matrix I I ℂ) (v : I → ℂ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • (A ^ n *ᵥ v)) (NormedSpace.exp A *ᵥ v) := by
  letI := Matrix.linftyOpNormedRing (n := I) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := I) (R := ℂ) (α := ℂ)
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  let L : Matrix I I ℂ →ₗ[ℂ] (I → ℂ) := (Matrix.mulVecBilin ℂ ℂ).flip v
  have := h.map L L.continuous_of_finiteDimensional
  convert this using 1
  · funext n
    exact (Matrix.smul_mulVec _ _ _).symm
  · rfl

theorem exp_int {A : Matrix I I ℂ} {B : Matrix J J ℂ} {P : Matrix I J ℂ} (h : A * P = P * B) (u : J → ℂ) :
    NormedSpace.exp A *ᵥ (P *ᵥ u) = P *ᵥ (NormedSpace.exp B *ᵥ u) := by
  have hn : ∀ n : ℕ, A ^ n * P = P * B ^ n := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, pow_succ, Matrix.mul_assoc]
  have h2 := (hasSum_exp B u).map P.mulVecLin P.mulVecLin.continuous_of_finiteDimensional
  refine (hasSum_exp A _).unique ?_
  simpa [Function.comp_def, hn, Matrix.mulVec_smul] using h2

theorem exp_eig {A : Matrix I I ℂ} {v : I → ℂ} {c : ℂ} (h : A *ᵥ v = c • v) : NormedSpace.exp A *ᵥ v = Complex.exp c • v := by
  have hn : ∀ n : ℕ, A ^ n *ᵥ v = c ^ n • v := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  refine (hasSum_exp A v).unique ?_
  have := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).smul_const v
  rw [← Complex.exp_eq_exp_ℂ] at this
  simpa [hn, smul_smul] using this

theorem exp_nil {A : Matrix I I ℂ} {v : I → ℂ} (h : A *ᵥ (A *ᵥ v) = 0) : NormedSpace.exp A *ᵥ v = v + A *ᵥ v := by
  refine (hasSum_exp A v).unique ?_
  have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (f := fun n : ℕ => ((n.factorial : ℂ))⁻¹ • (A ^ n *ᵥ v)) (s := Finset.range 2) (fun n hn => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show 2 ≤ n from not_lt.1 (mt Finset.mem_range.2 hn))
      rw [pow_succ, pow_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero, smul_zero])
  simpa [Finset.sum_range_succ] using this

end Exp

variable {R S R₁ S₁ : ℕ}

def sg : Ix R S → ℂ := Sum.elim (fun _ => 1) fun _ => -1

theorem Jm_sg (r s : ℕ) : Jm r s = Matrix.diagonal sg := Jm_eq r s

theorem star_sg (a : Ix R S) : star (sg a) = sg a := by cases a <;> simp [sg]

theorem sg_sq (a : Ix R S) : sg a * sg a = 1 := by cases a <;> simp [sg]

def Emb.P (m : Emb R S R₁ S₁) : Matrix (Ix R S) (Ix R₁ S₁) ℂ := fun a b => if a = m.e b then 1 else 0

def Emb.x (m : Emb R S R₁ S₁) : Ix R S → ℂ := Pi.single (.inl m.i) 1 + Pi.single (.inr m.j) 1

def Emb.y (m : Emb R S R₁ S₁) : Ix R S → ℂ := Pi.single (.inl m.i) 1 - Pi.single (.inr m.j) 1

def embA (R S : ℕ) : Emb (R + 1) (S + 1) R S where
  e := Sum.map Fin.succ Fin.succ
  i := 0
  j := 0
  ε := 1
  ε_ne := one_ne_zero
  inj := (Fin.succ_injective _).sumMap (Fin.succ_injective _)
  cover := by
    rintro (a | a) <;> refine Fin.cases ?_ (fun b => ?_) a
    exacts [.inl rfl, .inr (.inr ⟨.inl b, rfl⟩), .inr (.inl rfl), .inr (.inr ⟨.inr b, rfl⟩)]
  ne_i := by rintro (b | b) <;> simp [Fin.succ_ne_zero]
  ne_j := by rintro (b | b) <;> simp [Fin.succ_ne_zero]
  sb := by rintro (a | a) (b | b) <;> simp [sameBlock]
  pos := by rintro (a | a) (b | b) <;> simp [posC]
  ext := by rintro a (b | b) (rfl | rfl) <;> simp [posC, sameBlock] <;> norm_num

def embB (R S : ℕ) : Emb (R + 1) (S + 1) R S where
  e := Sum.map Fin.castSucc Fin.castSucc
  i := Fin.last R
  j := Fin.last S
  ε := -1
  ε_ne := by norm_num
  inj := (Fin.castSucc_injective _).sumMap (Fin.castSucc_injective _)
  cover := by
    rintro (a | a) <;> refine Fin.lastCases ?_ (fun b => ?_) a
    exacts [.inl rfl, .inr (.inr ⟨.inl b, rfl⟩), .inr (.inl rfl), .inr (.inr ⟨.inr b, rfl⟩)]
  ne_i := by rintro (b | b) <;> simp [Fin.castSucc_ne_last]
  ne_j := by rintro (b | b) <;> simp [Fin.castSucc_ne_last]
  sb := by rintro (a | a) (b | b) <;> simp [sameBlock]
  pos := by rintro (a | a) (b | b) <;> simp [posC]
  ext := by rintro a (b | b) (rfl | rfl) <;> simp [posC, sameBlock, Fin.castSucc_lt_last] <;> norm_num

theorem sg_embA (R S : ℕ) (b) : sg ((embA R S).e b) = sg b := by cases b <;> rfl

theorem sg_embB (R S : ℕ) (b) : sg ((embB R S).e b) = sg b := by cases b <;> rfl

theorem Emb.embeddingMatrix_mulVec (m : Emb R S R₁ S₁) (u : Ix R₁ S₁ → ℂ) :
    (m.P *ᵥ u) (.inl m.i) = 0 ∧ (m.P *ᵥ u) (.inr m.j) = 0 ∧ ∀ b, (m.P *ᵥ u) (m.e b) = u b := by
  refine ⟨?_, ?_, fun b => ?_⟩ <;> simp [Emb.P, Matrix.mulVec, dotProduct, (m.ne_i _).symm, (m.ne_j _).symm, m.inj.eq_iff]

theorem Emb.tP (m : Emb R S R₁ S₁) (v : Ix R S → ℂ) (b) : (m.Pᵀ *ᵥ v) b = v (m.e b) := by
  simp [Emb.P, Matrix.mulVec, dotProduct]

theorem Emb.embedding_transpose_vector_zero (m : Emb R S R₁ S₁) : m.Pᵀ *ᵥ m.x = 0 := by
  funext b; simp [m.tP, Emb.x, Pi.single_eq_of_ne (m.ne_i b), Pi.single_eq_of_ne (m.ne_j b)]

theorem Emb.transpose_mulVec_y_eq_zero (m : Emb R S R₁ S₁) : m.Pᵀ *ᵥ m.y = 0 := by
  funext b; simp [m.tP, Emb.y, Pi.single_eq_of_ne (m.ne_i b), Pi.single_eq_of_ne (m.ne_j b)]

theorem Emb.tPP (m : Emb R S R₁ S₁) : m.Pᵀ * m.P = 1 := by
  ext a b; simp [Emb.P, Matrix.mul_apply, m.inj.eq_iff, Matrix.one_apply, eq_comm]

theorem Emb.conj_single (m : Emb R S R₁ S₁) (a b) : m.P * Matrix.single a b (1 : ℂ) * m.Pᵀ = Matrix.single (m.e a) (m.e b) 1 := by
  ext c d
  simp only [Matrix.mul_apply, Matrix.single_apply, Emb.P, Matrix.transpose_apply]
  rw [Finset.sum_eq_single b, Finset.sum_eq_single a] <;> simp +contextual [eq_comm, ite_and]
  split_ifs <;> rfl

theorem Emb.JP (m : Emb R S R₁ S₁) (hs : ∀ b, sg (m.e b) = sg b) : Jm R S * m.P = m.P * Jm R₁ S₁ := by
  ext a b
  rw [Jm_sg, Jm_sg, Matrix.diagonal_mul, Matrix.mul_diagonal, Emb.P]
  split_ifs with h
  · rw [h, hs, mul_comm]
  · simp

theorem Emb.conj_upq (m : Emb R S R₁ S₁) (hs : ∀ b, sg (m.e b) = sg b) {Y : Mat R₁ S₁} (h : Y ∈ upq R₁ S₁) :
    m.P * Y * m.Pᵀ ∈ upq R S := by
  have h1 : m.Pᴴ = m.Pᵀ := by ext a b; simp [Emb.P]
  have h2 : m.Pᵀᴴ = m.P := by ext a b; simp [Emb.P]
  have h3 : m.Pᵀ * Jm R S = Jm R₁ S₁ * m.Pᵀ := by
    have := congrArg Matrix.conjTranspose (m.JP hs)
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_star, Jm_star, h1] at this
  have h4 : Yᴴ * Jm R₁ S₁ + Jm R₁ S₁ * Y = 0 := h
  change (m.P * Y * m.Pᵀ)ᴴ * _ + _ = 0
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, h1, h2]
  calc _ = m.P * (Yᴴ * Jm R₁ S₁ + Jm R₁ S₁ * Y) * m.Pᵀ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h3]
        rw [← Matrix.mul_assoc (Jm R S), m.JP hs, Matrix.mul_assoc]
    _ = 0 := by rw [h4]; simp

theorem single_mulVec' (a b : Ix R S) (v : Ix R S → ℂ) : Matrix.single a b (1 : ℂ) *ᵥ v = v b • Pi.single a 1 := by
  funext c
  by_cases e : c = a
  · subst e; simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Ne.symm e, Pi.single_eq_of_ne e]

theorem J_single (a b : Ix R S) : Jm R S * Matrix.single a b (1 : ℂ) = sg a • Matrix.single a b 1 := by
  ext c d; rw [Jm_sg, Matrix.diagonal_mul]; simp only [Matrix.smul_apply, Matrix.single_apply]; split_ifs with h <;> simp [h]

theorem single_J (a b : Ix R S) : Matrix.single a b (1 : ℂ) * Jm R S = sg b • Matrix.single a b 1 := by
  ext c d; rw [Jm_sg, Matrix.mul_diagonal]; simp only [Matrix.smul_apply, Matrix.single_apply]; split_ifs with h <;> simp [h]

theorem sg_l (i : Fin R) : sg (.inl i : Ix R S) = 1 := rfl

theorem sg_r (i : Fin S) : sg (.inr i : Ix R S) = -1 := rfl

def hf {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (u v : Fin d → ℂ) : ℂ := u ⬝ᵥ M *ᵥ star v

theorem gram_apply {d : ℕ} {I : Type} (M : Matrix (Fin d) (Fin d) ℂ) (C : Matrix (Fin d) I ℂ) (a b : I) :
    (Cᵀ * M * C.map star) a b = hf M (fun r => C r a) (fun r => C r b) := by
  rw [Matrix.mul_assoc]; rfl

theorem exists_frame (m : Emb R S R₁ S₁) (hs : ∀ b, sg (m.e b) = sg b) {d d₁ : ℕ} (hd : d = R + S)
    {M θ : Matrix (Fin d) (Fin d) ℂ} {M₁ θ₁ : Matrix (Fin d₁) (Fin d₁) ℂ} (hM : ∀ i j, M j i = star (M i j)) (hθ : IsCartan M θ)
    {x y : Fin d → ℂ} {ι : Matrix (Fin d) (Fin d₁) ℂ} (x0 : x ≠ 0) (xx : hf M x x = 0) {c : ℂ} (c0 : c ≠ 0) (hy : y = c • θ *ᵥ x)
    (ox : ∀ k, hf M (fun r => ι r k) x = 0) (oy : ∀ k, hf M (fun r => ι r k) y = 0) (hg : ιᵀ * M * ι.map star = M₁)
    (hθι : θ * ι = ι * θ₁) {C₁ : Matrix (Fin d₁) (Ix R₁ S₁) ℂ} (hC₁ : IsFrame M₁ C₁) (hθ₁ : θ₁ * C₁ = C₁ * Jm R₁ S₁) :
    ∃ (C : Matrix (Fin d) (Ix R S) ℂ) (n n' : ℂ), IsFrame M C ∧ θ * C = C * Jm R S ∧ n ≠ 0 ∧ x = n • C *ᵥ m.x ∧
      y = n' • C *ᵥ m.y ∧ C * m.P = ι * C₁ := by
  have herm : ∀ u v, hf M v u = star (hf M u v) := fun u v => by
    simp only [hf, dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum, ← hM]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have iso : ∀ u v, hf M (θ *ᵥ u) (θ *ᵥ v) = hf M u v := fun u v => by
    conv_rhs => rw [← hθ.2.1]
    rw [hf, hf, show star (θ *ᵥ v) = θ.map star *ᵥ star v by
      funext i; simp [Matrix.mulVec, dotProduct, star_sum], Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec u, Matrix.vecMul_transpose]
  have θθ : ∀ u, θ *ᵥ (θ *ᵥ u) = u := fun u => by rw [Matrix.mulVec_mulVec, hθ.1, Matrix.one_mulVec]
  have addl : ∀ u u' v (s : ℂ), hf M (u + s • u') v = hf M u v + s * hf M u' v := fun u u' v s => by simp [hf]
  have addr : ∀ u v v' (s : ℂ), hf M u (v + s • v') = hf M u v + star s * hf M u v' := fun u v v' s => by
    simp [hf, Matrix.mulVec_add, Matrix.mulVec_smul]
  have sml : ∀ u v (s : ℂ), hf M (s • u) v = s * hf M u v := fun u v s => by simp [hf]
  have smr : ∀ u v (s : ℂ), hf M u (s • v) = star s * hf M u v := fun u v s => by simp [hf, Matrix.mulVec_smul]
  set z := θ *ᵥ x with hz
  have zz : hf M z z = 0 := (iso x x).trans xx
  have zx : hf M x z = hf M z x := by rw [← iso x z, hz, θθ]
  set k := (hf M z x).re with hk
  have k0 : 0 < k := hθ.2.2 x x0
  have zk : hf M z x = k := by
    have := herm z x
    rw [zx] at this
    exact (Complex.conj_eq_iff_re.1 this.symm).symm
  set N : ℂ := (((Real.sqrt (2 * k))⁻¹ : ℝ) : ℂ) with hN
  have sN : star N = N := Complex.conj_ofReal _
  have NN : N * N * (2 * k) = 1 := by
    rw [hN]; norm_cast
    rw [← mul_inv, Real.mul_self_sqrt (by positivity), inv_mul_cancel₀ (by positivity)]
  have N0 : N ≠ 0 := fun e => by rw [e] at NN; simp at NN
  have oz : ∀ k, hf M (fun r => ι r k) z = 0 := fun k => by
    have := oy k
    rw [hy, smr, mul_eq_zero] at this
    exact this.resolve_left (star_ne_zero.2 c0)
  have col : ∀ (v) (b), (∀ k, hf M (fun r => ι r k) v = 0) → hf M (fun r => (ι * C₁) r b) v = 0 := fun v b h => by
    have : hf M (fun r => (ι * C₁) r b) v = ∑ k, C₁ k b * hf M (fun r => ι r k) v := by
      simp only [hf, dotProduct, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    simp [this, h]
  let cl : Ix R S → Fin d → ℂ := fun a => if a = .inl m.i then N • (x + (1 : ℂ) • z) else if a = .inr m.j then
    N • (x + (-1 : ℂ) • z) else Function.extend m.e (fun b r => (ι * C₁) r b) 0 a
  have ci : cl (.inl m.i) = N • (x + (1 : ℂ) • z) := if_pos rfl
  have cj : cl (.inr m.j) = N • (x + (-1 : ℂ) • z) := by simp [cl]
  have ce : ∀ b, cl (m.e b) = fun r => (ι * C₁) r b := fun b => by
    simp only [cl, if_neg (m.ne_i b), if_neg (m.ne_j b), m.inj.extend_apply]
  have o1 : ∀ b (s : ℂ), hf M (fun r => (ι * C₁) r b) (N • (x + s • z)) = 0 := fun b s => by
    rw [smr, addr, col _ b ox, col _ b oz]; simp
  have gram : (Matrix.of fun r a => cl a r)ᵀ * M * (Matrix.of fun r a => cl a r).map star = Jm R S := by
    ext a b
    rw [gram_apply, Jm_sg]
    change hf M (cl a) (cl b) = _
    rcases m.cover a with rfl | rfl | ⟨a, rfl⟩ <;> rcases m.cover b with rfl | rfl | ⟨b, rfl⟩ <;>
      simp only [ci, cj, ce]
    · simp only [sml, smr, addl, addr, xx, zz, zx, zk, sN, Matrix.diagonal_apply_eq, sg_l, star_one]
      linear_combination NN
    · simp only [sml, smr, addl, addr, xx, zz, zx, zk, sN, star_neg, star_one]
      rw [Matrix.diagonal_apply_ne _ (by simp)]; ring
    · rw [herm, o1, Matrix.diagonal_apply_ne _ (m.ne_i b).symm, star_zero]
    · simp only [sml, smr, addl, addr, xx, zz, zx, zk, sN, star_neg, star_one]
      rw [Matrix.diagonal_apply_ne _ (by simp)]; ring
    · simp only [sml, smr, addl, addr, xx, zz, zx, zk, sN, Matrix.diagonal_apply_eq, sg_r, star_neg, star_one]
      linear_combination -NN
    · rw [herm, o1, Matrix.diagonal_apply_ne _ (m.ne_j b).symm, star_zero]
    · rw [o1, Matrix.diagonal_apply_ne _ (m.ne_i a)]
    · rw [o1, Matrix.diagonal_apply_ne _ (m.ne_j a)]
    · rw [← gram_apply, Matrix.transpose_mul, show (ι * C₁).map star = ι.map star * C₁.map star from
        Matrix.map_mul (f := starRingEnd ℂ), show C₁ᵀ * ιᵀ * M * (ι.map star * C₁.map star) =
          C₁ᵀ * (ιᵀ * M * ι.map star) * C₁.map star by simp only [Matrix.mul_assoc], hg, hC₁.1, Jm_sg]
      by_cases e : a = b
      · subst e; simp [hs]
      · rw [Matrix.diagonal_apply_ne _ e, Matrix.diagonal_apply_ne _ (m.inj.ne e)]
  refine ⟨Matrix.of fun r a => cl a r, (2 * N)⁻¹, c * (2 * N)⁻¹, ⟨gram, ?_⟩, ?_, by simp [N0], ?_, ?_, ?_⟩
  · set C : Matrix (Fin d) (Ix R S) ℂ := Matrix.of fun r a => cl a r
    have h1 : (Jm R S * (Cᵀ * M)) * C.map star = 1 := by rw [Matrix.mul_assoc, gram, Jm_sq]
    have h2 := (Matrix.mul_eq_one_comm_of_card_eq _ _ ℂ (by simp [hd])).1 h1
    refine ⟨(Jm R S * (Cᵀ * M)).map star, ?_⟩
    have h3 := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => A.map (starRingEnd ℂ)) h2
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h3
    rw [← h3, ← Matrix.map_mul, ← Matrix.map_mul]
    congr 1
    ext; simp
  · ext r a
    rw [Jm_sg, Matrix.mul_diagonal]
    change (θ *ᵥ cl a) r = cl a r * sg a
    rcases m.cover a with rfl | rfl | ⟨a, rfl⟩
    · rw [ci, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, θθ]; simp only [sg_l, hz, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
    · rw [cj, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, θθ]; simp [sg_r, hz]; ring
    · rw [ce, hs]
      change (θ * (ι * C₁)) r a = _
      rw [← Matrix.mul_assoc, hθι, Matrix.mul_assoc, hθ₁, ← Matrix.mul_assoc, Jm_sg, Matrix.mul_diagonal]
  · funext r
    simp only [Emb.x, Matrix.mulVec_add, Matrix.mulVec_single_one, Pi.smul_apply, Pi.add_apply, Matrix.col_apply,
      Matrix.of_apply, ci, cj, smul_eq_mul]
    field_simp; ring
  · funext r
    simp only [hy, Emb.y, Matrix.mulVec_sub, Matrix.mulVec_single_one, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
      Matrix.col_apply, Matrix.of_apply, ci, cj, smul_eq_mul]
    field_simp; ring
  · ext r b
    simp [Matrix.mul_apply (M := Matrix.of _), Emb.P, ce]

end PositivityTheory.ThKG.CayleyTransformDarboux

end
end

section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.RealLift PositivityTheory.ThKG.Loc
open FockH1Action (Mat Ix cPair)
open Formalism.BasicNotions.TH (upq Jm)
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.ThKG.CayleyTransformDarboux

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {R S R₁ S₁ d d₁ : ℕ}

theorem piInf_incV {w : InfinitePlace F} (τ : EmbOver E w) {n : ℕ} (x : Fin n → E) :
    (piInf τ ∘ incV F x) = fun i => τ.1 (x i) := by
  funext i
  simp [incV, piInf, compInf, inclR, infEmb_tmul]

theorem map_mulVec' {w : InfinitePlace F} (τ : EmbOver E w) {n k : ℕ} (M : Matrix (Fin n) (Fin k) (AE F E)) (v : Fin k → AE F E) :
    piInf τ ∘ (M *ᵥ v) = M.map (piInf τ) *ᵥ (piInf τ ∘ v) := funext fun i => RingHom.map_mulVec _ M v i

theorem at_mulVec {n : ℕ} {M : Matrix (Fin n) (Fin n) (AE F E)} (h : At (evI F) (M - 1)) (z : Fin n → AE F E) (i : Fin n) :
    (M *ᵥ z) i - z i ∈ atI F E := by
  have : (M *ᵥ z) i - z i = ((M - 1) *ᵥ z) i := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
  rw [this]
  change ∑ j, (M - 1) i j * z j ∈ _
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (at_entry h i j)

structure FD (B : Base F E) (H' : Plane E d d₁) (m : Emb R S R₁ S₁) (C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ)
    (C₁ : InfinitePlace F → Matrix (Fin d₁) (Ix R₁ S₁) ℂ) (n n' : InfinitePlace F → ℂ) : Prop where
  cm : IsCMExt F E σ
  n0 : ∀ w, n w ≠ 0
  hx : ∀ w, (fun i => (B.emb w).1 (H'.x i)) = n w • C w *ᵥ m.x
  hy : ∀ w, (fun i => (B.emb w).1 (H'.y i)) = n' w • C w *ᵥ m.y
  hι : ∀ w, C w * m.P = H'.ι.map (B.emb w).1 * C₁ w
  inv : ∀ w, ∃ A : Matrix (Ix R₁ S₁) (Fin d₁) ℂ, C₁ w * A = 1

variable {B : Base F E} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {m : Emb R S R₁ S₁}
  {C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ} {C₁ : InfinitePlace F → Matrix (Fin d₁) (Ix R₁ S₁) ℂ}
  {n n' : InfinitePlace F → ℂ}

theorem gen_vec {γ : Multiplicative ℝ →* UA σ W.J} {Y} (h : IsGen B.emb C γ Y) (s : ℝ) (w) (v : Ix R S → ℂ) :
    (mat (γ (Multiplicative.ofAdd s))).map (piInf (B.emb w)) *ᵥ (C w *ᵥ v) = C w *ᵥ (NormedSpace.exp (s • Y w) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (· *ᵥ v) (h s w)

theorem real_mulVec (s : ℝ) (Y : Mat R S) (v : Ix R S → ℂ) : (s • Y) *ᵥ v = (s : ℂ) • (Y *ᵥ v) := by
  rw [Matrix.smul_mulVec]; rfl

theorem eig_vec (hc : IsCMExt F E σ) {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) {Y} (h : IsGen B.emb C γ Y) (s : ℝ)
    (x : Fin d → E) (k l : InfinitePlace F → ℂ) (v : Ix R S → ℂ) (hx : ∀ w, (fun i => (B.emb w).1 (x i)) = k w • C w *ᵥ v)
    (hY : ∀ w, Y w *ᵥ v = l w • v) (t : AE F E) (ht : t - 1 ∈ atI F E) (ht' : ∀ w, piInf (B.emb w) t = Complex.exp (s * l w)) :
    mat (γ (Multiplicative.ofAdd s)) *ᵥ incV F x = t • incV F x := by
  funext i
  refine eq_of_inf hc B.emb ?_ fun w => ?_
  · have := sub_mem (at_mulVec (hγ.2 (Multiplicative.ofAdd s)) (incV F x) i) (Ideal.mul_mem_right (incV F x i) _ ht)
    rwa [sub_mul, one_mul, sub_sub_sub_cancel_right] at this
  · have e := map_mulVec' (B.emb w) (mat (γ (Multiplicative.ofAdd s))) (incV F x)
    rw [piInf_incV, hx, Matrix.mulVec_smul, gen_vec h,
      exp_eig (c := s * l w) (by rw [real_mulVec, hY, smul_smul]), Matrix.mulVec_smul, smul_comm, ← hx] at e
    refine (congrFun e i).trans ?_
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, ht']
    exact congrArg _ (congrFun (piInf_incV (B.emb w) x) i).symm

theorem FD.iota (h : FD (σ := σ) B H' m C C₁ n n') (w) (z : Fin d₁ → ℂ) :
    ∃ u, z = C₁ w *ᵥ u ∧ H'.ι.map (B.emb w).1 *ᵥ z = C w *ᵥ (m.P *ᵥ u) := by
  obtain ⟨A, hA⟩ := h.inv w
  refine ⟨A *ᵥ z, by rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec], ?_⟩
  rw [Matrix.mulVec_mulVec, h.hι, Matrix.mulVec_mulVec, Matrix.mul_assoc, hA, Matrix.mul_one]

theorem FD.levi (h : FD (σ := σ) B H' m C C₁ n n') {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) {Y}
    (hg : IsGen B.emb C γ Y) {γ₁ : Multiplicative ℝ →* UA σ W₁.J} (hγ₁ : γ₁ ∈ Lines σ W₁) {Y₁} (hg₁ : IsGen B.emb C₁ γ₁ Y₁)
    {l : InfinitePlace F → ℂ} (h1 : ∀ w, Y w *ᵥ m.x = l w • m.x) (h2 : ∀ w, Y w *ᵥ m.y = (-star (l w)) • m.y)
    (h3 : ∀ w, Y w * m.P = m.P * Y₁ w) (s : ℝ) (t : (AE F E)ˣ) (ht : (t : AE F E) - 1 ∈ atI F E)
    (ht' : ∀ w, piInf (B.emb w) t = Complex.exp (s * l w)) :
    IsLevi H' t (γ₁ (Multiplicative.ofAdd s)) (γ (Multiplicative.ofAdd s)) := by
  refine ⟨eig_vec h.cm hγ hg s _ _ _ _ h.hx h1 _ ht ht', eig_vec h.cm hγ hg s _ _ _ _ h.hy h2 _ ?_ fun w => ?_, ?_⟩
  · have := at_cA (σ := σ) (inv_at ht)
    rwa [map_sub, map_one] at this
  · have h3 := congrArg (piInf (B.emb w)) t.mul_inv
    rw [map_mul, ht', map_one] at h3
    rw [piInf_cA h.cm, eq_inv_of_mul_eq_one_right h3, ← Complex.exp_neg]
    refine (Complex.exp_conj _).symm.trans ?_
    simp
  · refine Matrix.ext_iff_mulVec.2 fun z => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    funext i
    refine eq_of_inf h.cm B.emb ?_ fun w => ?_
    · have a1 := at_mulVec (hγ.2 (Multiplicative.ofAdd s)) (incM F H'.ι *ᵥ z) i
      have a2 : (incM F H'.ι *ᵥ (mat (γ₁ (Multiplicative.ofAdd s)) *ᵥ z - z)) i ∈ atI F E := by
        change ∑ j, incM F H'.ι i j * (mat (γ₁ (Multiplicative.ofAdd s)) *ᵥ z - z) j ∈ _
        exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (at_mulVec (hγ₁.2 (Multiplicative.ofAdd s)) z j)
      have := sub_mem a1 a2
      rwa [Matrix.mulVec_sub, Pi.sub_apply, sub_sub_sub_cancel_right] at this
    · refine congrFun (?_ : piInf (B.emb w) ∘ _ = piInf (B.emb w) ∘ _) i
      obtain ⟨u, e1, e2⟩ := h.iota w (piInf (B.emb w) ∘ z)
      rw [map_mulVec', map_mulVec', map_mulVec', map_mulVec', incM_map, e2, gen_vec hg, e1, gen_vec hg₁,
        exp_int (B := s • Y₁ w) (by rw [Matrix.smul_mul, h3, Matrix.mul_smul]), Matrix.mulVec_mulVec _ (C w), h.hι,
        ← Matrix.mulVec_mulVec]

theorem FD.unip (h : FD (σ := σ) B H' m C C₁ n n') {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) {Y}
    (hg : IsGen B.emb C γ Y) (h1 : ∀ w, Y w *ᵥ m.x = 0) (h2 : ∀ w u, ∃ a : ℂ, Y w *ᵥ (m.P *ᵥ u) = a • m.x) (s) :
    γ s ∈ unip σ W H' := by
  obtain ⟨s, rfl⟩ := Multiplicative.ofAdd.surjective s
  refine Subgroup.subset_closure ⟨?_, fun z => ?_⟩
  · have := eig_vec h.cm hγ hg s _ _ 0 m.x h.hx (fun w => by simp [h1]) 1 (by simp) fun w => by simp
    rwa [one_smul] at this
  · choose u e1 e2 using fun w => h.iota w (piInf (B.emb w) ∘ z)
    choose a ha using fun w => h2 w (u w)
    obtain ⟨b, hb, hb'⟩ := exists_inf h.cm B.emb fun w => s * a w / n w
    refine ⟨b, funext fun i => eq_of_inf h.cm B.emb ?_ fun w => ?_⟩
    · have := sub_mem (at_mulVec (hγ.2 (Multiplicative.ofAdd s)) (incM F H'.ι *ᵥ z) i)
        (Ideal.mul_mem_right (incV F H'.x i) (atI F E) hb)
      rwa [sub_sub] at this
    · have e3 := map_mulVec' (B.emb w) (mat (γ (Multiplicative.ofAdd s))) (incM F H'.ι *ᵥ z)
      have e4 := map_mulVec' (B.emb w) (incM F H'.ι) z
      rw [incM_map, e2] at e4
      rw [e4, gen_vec hg, exp_nil (by rw [real_mulVec, real_mulVec, ha, smul_smul, Matrix.mulVec_smul, h1]; simp), real_mulVec,
        ha, Matrix.mulVec_add, ← e4] at e3
      refine (congrFun e3 i).trans ?_
      have e5 := congrFun ((piInf_incV (B.emb w) H'.x).trans (h.hx w)) i
      have := h.n0 w
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at e5
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, hb', e5, Matrix.mulVec_smul, Function.comp_apply]
      field_simp

theorem single_prop {ι A A' : Type} [DecidableEq ι] [Zero A] [Zero A'] (P : A → A' → Prop) (w : ι) {a : A} {a' : A'} (h : P a a')
    (h0 : P 0 0) (i : ι) : P ((Pi.single w a : ι → A) i) ((Pi.single w a' : ι → A') i) := by
  by_cases e : i = w
  · subst e; simpa using h
  · simpa [Pi.single_eq_of_ne e] using h0

theorem core (hD : Dic) {a a' a₁ a₁' : ℕ} {G : Geo σ a a'} {G₁ : Geo σ a₁ a₁'} {X : Chars F E} {om om' om₁ om₁'}
    {Rm : RealMaps F a a'} {Rm₁ : RealMaps F a₁ a₁'} (hT : IsTriple B G X om om') (hR : IsRealMaps B G om om' Rm)
    (hT₁ : IsTriple B G₁ X om₁ om₁') (hR₁ : IsRealMaps B G₁ om₁ om₁' Rm₁) {H' : Plane E (a + a') (a₁ + a₁')} {i₀ i₁ : ℕ}
    (hH : H'.IsAdapted σ B G.W G₁.W i₀ i₁) (m : Emb (a₁ + a₁' - (G₁.p + G₁.q) + 1) (G₁.p + G₁.q + 1)
      (a₁ + a₁' - (G₁.p + G₁.q)) (G₁.p + G₁.q)) (hs : ∀ b, sg (m.e b) = sg b) (hy : G₁.p + G₁.q + 1 = G.p + G.q)
    (hΛ : ∀ w b, lamW B (a - G.p) G.p _ _ w (m.e b) = lamW B (a₁ - G₁.p) G₁.p _ _ w b) {χ : Chr F E} {k} (hχ : HasExp B.emb χ k)
    (r : ℝ) {lam lam' : Rm.Pi →ₗ[ℂ] Rm₁.Pi} (h : IsArchimedeanLocalEquivariantMap B G.M G₁.M om om₁ H' χ r Rm.p Rm₁.p lam)
    (h' : IsArchimedeanLocalEquivariantMap B G.M G₁.M om om₁ H' χ r Rm.p Rm₁.p lam') (h0 : lam ≠ 0) : ∃ c : ℂ, lam' = c • lam := by
  have hc := hT.base.cm
  have rk := hH.rank
  have b1 := hT₁.geo.aBig
  choose C₁ hC₁ hθ₁ using fun w => hD.frame _ _ _ _ _ (hT₁.geo.hW.sig w) (hT₁.geo.hW.cartan w)
  have fm : ∀ (w) (x y : Fin (a + a') → E), hf (Complex.I • G.W.J.map (B.emb w).1) (fun i => (B.emb w).1 (x i))
      (fun i => (B.emb w).1 (y i)) = Complex.I * (B.emb w).1 (form σ G.W.J x y) := fun w x y => by
    simp only [hf, form, dotProduct, Matrix.mulVec, map_sum, map_mul, hc.2.2.2, Finset.mul_sum, Matrix.smul_apply,
      Matrix.map_apply, Pi.star_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [Complex.star_def]; ring
  have col : ∀ j, H'.ι *ᵥ Pi.single j 1 = fun r => H'.ι r j := fun j => Matrix.mulVec_single_one _ _
  choose c' c0' hcy using fun w => (hH.cartan w).2
  have ex := fun w => exists_frame m hs (d := a + a') (by omega) (M := Complex.I • G.W.J.map (B.emb w).1)
      (fun i j => by
        simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul']
        rw [← hc.2.2.2, hT.geo.hW.skew, Complex.star_def, Complex.conj_I, map_neg, neg_mul_neg])
      (hT.geo.hW.cartan w) (x := fun i => (B.emb w).1 (H'.x i)) (y := fun i => (B.emb w).1 (H'.y i))
      (ι := H'.ι.map (B.emb w).1)
      (fun e => by
        have := fm w H'.x H'.y
        rw [e, hH.xy] at this
        rw [map_one, mul_one, hf, zero_dotProduct] at this
        exact Complex.I_ne_zero this.symm)
      (by rw [fm, hH.xx]; simp) (c0' w) (hcy w)
      (fun j => by
        have := fm w (H'.ι *ᵥ Pi.single j 1) H'.x
        rw [(hH.orth _).1, col] at this
        simpa using this)
      (fun j => by
        have := fm w (H'.ι *ᵥ Pi.single j 1) H'.y
        rw [(hH.orth _).2, col] at this
        simpa using this)
      (by
        rw [← hH.gram, Matrix.map_mul, Matrix.map_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_map]
        congr 2
        ext i j
        exact (hc.2.2.2 _ _).symm)
      (hH.cartan w).1 (hC₁ w) (hθ₁ w)
  choose C n n' hC hθ n0 hx hy' hι using ex
  have fd : FD (σ := σ) B H' m C C₁ n n' := ⟨hc, n0, hx, hy', hι, fun w => (hC₁ w).2⟩
  have hC' : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by rw [incM_map]; exact hC w
  have hC₁' : ∀ w, IsFrame (Complex.I • (incM F G₁.W.J).map (piInf (B.emb w))) (C₁ w) := fun w => by
    rw [incM_map]; exact hC₁ w
  obtain ⟨act, f, hM, ha⟩ := exists_mod hD hT hR (by omega) hy C hC' hθ
  obtain ⟨act₁, f₁, hM₁, ha₁⟩ := exists_mod hD hT₁ hR₁ (by omega) rfl C₁ hC₁' hθ₁
  have tor := fun l => exists_torus hc B.emb l χ hχ r
  choose t c ht hd using tor
  have onto : ∀ v : Rm.Pi, ∃ f ∈ G.M.Pol B.ψ B.emb, Rm.p f = v := fun v => (hR.quot.onto ▸ Submodule.mem_top : v ∈ _)
  have onto₁ : ∀ v : Rm₁.Pi, ∃ f ∈ G₁.M.Pol B.ψ B.emb, Rm₁.p f = v := fun v => (hR₁.quot.onto ▸ Submodule.mem_top : v ∈ _)
  have c0 : c 0 = 0 := by
    refine (hd 0).unique ?_
    have : ∀ s, t 0 s = 1 := fun s => Units.ext (eq_of_inf hc B.emb (ht 0 s).1 fun w => by simp [(ht 0 s).2])
    simp only [this]
    exact hasDerivAt_const _ _
  have ij : (Sum.inl m.i : Ix _ _) ≠ Sum.inr m.j := Sum.inl_ne_inr
  have par : ∀ D : Rm.Pi →ₗ[ℂ] Rm₁.Pi, IsArchimedeanLocalEquivariantMap B G.M G₁.M om om₁ H' χ r Rm.p Rm₁.p D →
      IsPar m act act₁ (fun w => -Complex.I * c (Pi.single w Complex.I)) (fun w => c (Pi.single w 1)) D := by
    intro D hP
    have L : ∀ Y Y₁ l, (∀ w, Y w ∈ upq _ _) → (∀ w, Y₁ w ∈ upq _ _) → (∀ w, Y w *ᵥ m.x = l w • m.x) →
        (∀ w, Y w *ᵥ m.y = (-star (l w)) • m.y) → (∀ w, Y w * m.P = m.P * Y₁ w) →
        ∀ v, D (act Y v) = c l • D v + act₁ Y₁ (D v) := by
      intro Y Y₁ l u1 u2 h1 h2 h3 v
      obtain ⟨γ, hγ, hg⟩ := hD.line F E σ _ _ _ B.emb _ Complex.I C hc hC' Y u1
      obtain ⟨γ₁, hγ₁, hg₁⟩ := hD.line F E σ _ _ _ B.emb _ Complex.I C₁ hc hC₁' Y₁ u2
      obtain ⟨g, hg0, rfl⟩ := onto v
      obtain ⟨g₁, hg₁0, e⟩ := onto₁ (D (Rm.p g))
      obtain ⟨g', q1, q2⟩ := ha γ hγ Y hg g hg0
      obtain ⟨g₁', q3, q4⟩ := ha₁ γ₁ hγ₁ Y₁ hg₁ g₁ hg₁0
      rw [← q2, ← e, ← q4]
      exact hP.levi γ hγ γ₁ hγ₁ (t l) (fun s => fd.levi hγ hg hγ₁ hg₁ h1 h2 h3 s _ (ht l s).1 (ht l s).2) _ (hd l) g hg0 g₁ hg₁0
        g' g₁' q1 q3 e.symm
    have U : ∀ w Y, Y ∈ upq _ _ → Y *ᵥ m.x = 0 → (∀ u, ∃ a : ℂ, Y *ᵥ (m.P *ᵥ u) = a • m.x) →
        ∀ v, D (act (Pi.single w Y) v) = 0 := by
      intro w Y u1 h1 h2 v
      obtain ⟨γ, hγ, hg⟩ := hD.line F E σ _ _ _ B.emb _ Complex.I C hc hC' _ (single_upq w u1)
      obtain ⟨g, hg0, rfl⟩ := onto v
      obtain ⟨g', q1, q2⟩ := ha γ hγ _ hg g hg0
      rw [← q2]
      exact hP.unip γ hγ (fd.unip hγ hg (single_prop (fun Z (_ : ℂ) => Z *ᵥ m.x = 0) w (a' := 0) h1 (by simp))
        (single_prop (fun Z (_ : ℂ) => ∀ u, ∃ a : ℂ, Z *ᵥ (m.P *ᵥ u) = a • m.x) w (a' := 0) h2 fun u => ⟨0, by simp⟩)) g hg0 g' q1
    have T : ∀ w Y (l : ℂ), Y ∈ upq _ _ → Y *ᵥ m.x = l • m.x → Y *ᵥ m.y = (-star l) • m.y → (∀ u, Y *ᵥ (m.P *ᵥ u) = 0) →
        ∀ v, D (act (Pi.single w Y) v) = c (Pi.single w l) • D v := by
      intro w Y l u1 h1 h2 h3 v
      have := L (Pi.single w Y) 0 (Pi.single w l) (single_upq w u1) (fun _ => zero_upq _ _)
        (single_prop (fun Z (l : ℂ) => Z *ᵥ m.x = l • m.x) w h1 (by simp))
        (single_prop (fun Z (l : ℂ) => Z *ᵥ m.y = (-star l) • m.y) w h2 (by simp))
        (fun i => Matrix.ext_iff_mulVec.2 fun u => by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Pi.zero_apply, Matrix.zero_mulVec, Matrix.mulVec_zero]
          exact single_prop (fun Z (_ : ℂ) => Z *ᵥ (m.P *ᵥ u) = 0) w (a' := 0) (h3 u) (Matrix.zero_mulVec _) i) v
      simpa using this
    have xi : m.x (.inl m.i) = 1 ∧ m.x (.inr m.j) = 1 ∧ m.y (.inl m.i) = 1 ∧ m.y (.inr m.j) = -1 ∧ ∀ b, m.x (m.e b) = 0 := by
      simp [Emb.x, Emb.y, Pi.single_eq_of_ne (m.ne_i _), Pi.single_eq_of_ne (m.ne_j _)]
    have N : ∀ w b (s : ℂ) v, s • D (act (un w (m.e b) (.inl m.i) - un w (m.e b) (.inr m.j)) v) -
        (star s * sg (m.e b)) • D (act (un w (.inl m.i) (m.e b) + un w (.inr m.j) (m.e b)) v) = 0 := fun w b s v => by
      have := U w (s • (Matrix.single (m.e b) (.inl m.i) 1 - Matrix.single (m.e b) (.inr m.j) 1) -
          (star s * sg (m.e b)) • (Matrix.single (.inl m.i) (m.e b) 1 + Matrix.single (.inr m.j) (m.e b) 1))
        (by
          simp only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
            Matrix.conjTranspose_single, star_one, star_mul', star_star, star_sg, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul,
            Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, J_single, single_J, sg_l, sg_r]
          module)
        (by simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, single_mulVec', xi]; simp)
        (fun u => ⟨-(star s * sg (m.e b) * u b), by
          simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, single_mulVec', m.embeddingMatrix_mulVec, Emb.x]
          module⟩) v
      simpa only [Pi.single_sub, Pi.single_smul, Pi.single_add, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        un, map_add, LinearMap.add_apply] using this
    have sg0 : ∀ b, sg (m.e b) ≠ 0 := fun b e => by simpa [e] using sg_sq (m.e b)
    refine ⟨fun w a b v => ?_, fun w v => ?_, fun w v => ?_, fun w v => ?_, fun w b v => ?_, fun w b v => ?_⟩
    · have key : ∀ Y : Mat _ _, D (act (Pi.single w (m.P * Y * m.Pᵀ)) v) = act₁ (Pi.single w Y) (D v) := by
        have k1 : ∀ Y ∈ upq _ _, D (act (Pi.single w (m.P * Y * m.Pᵀ)) v) = act₁ (Pi.single w Y) (D v) := fun Y hY => by
          have := L (Pi.single w (m.P * Y * m.Pᵀ)) (Pi.single w Y) 0 (single_upq w (m.conj_upq hs hY)) (single_upq w hY)
            (single_prop (fun Z (_ : ℂ) => Z *ᵥ m.x = (0 : ℂ) • m.x) w (a' := 0)
              (by rw [← Matrix.mulVec_mulVec, m.embedding_transpose_vector_zero]; simp) (by simp))
            (single_prop (fun Z (_ : ℂ) => Z *ᵥ m.y = (-star (0 : ℂ)) • m.y) w (a' := 0)
              (by rw [← Matrix.mulVec_mulVec, m.transpose_mulVec_y_eq_zero]; simp) (by simp))
            (single_prop (fun Z Z₁ => Z * m.P = m.P * Z₁) w (by rw [Matrix.mul_assoc, m.tPP, Matrix.mul_one]) (by simp)) v
          rwa [c0, zero_smul, zero_add] at this
        intro Y
        obtain ⟨Y₁, h₁, Y₂, h₂, rfl⟩ := upq_split Y
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Pi.single_add, Pi.single_smul, map_add,
          map_smul, LinearMap.add_apply, LinearMap.smul_apply, k1 _ h₁, k1 _ h₂]
      have := key (Matrix.single a b 1)
      rwa [m.conj_single] at this
    · have := T w (Complex.I • (Matrix.single (.inl m.i) (.inl m.i) 1 + Matrix.single (.inr m.j) (.inr m.j) 1)) Complex.I
        (by
          simp only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
            Matrix.conjTranspose_single, star_one, Complex.star_def, Complex.conj_I, Matrix.add_mul, Matrix.smul_mul,
            Matrix.mul_add, Matrix.mul_smul, J_single, single_J, sg_l, sg_r, map_one]
          module)
        (by simp only [Matrix.add_mulVec, Matrix.smul_mulVec, single_mulVec', xi]; simp [Emb.x])
        (by simp only [Matrix.add_mulVec, Matrix.smul_mulVec, single_mulVec', xi]; simp [Emb.y, sub_eq_add_neg])
        (fun u => by simp only [Matrix.add_mulVec, Matrix.smul_mulVec, single_mulVec', m.embeddingMatrix_mulVec]; simp) v
      rw [Pi.single_smul, map_smul, LinearMap.smul_apply, map_smul, Pi.single_add] at this
      rw [mul_smul, ← this, smul_smul]
      simp [un]
    · have := T w (Matrix.single (.inl m.i) (.inr m.j) 1 + Matrix.single (.inr m.j) (.inl m.i) 1) 1
        (by
          simp only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_add, Matrix.conjTranspose_single, star_one, Matrix.add_mul,
            Matrix.mul_add, J_single, single_J, sg_l, sg_r]
          module)
        (by simp only [Matrix.add_mulVec, single_mulVec', xi]; simp [Emb.x])
        (by simp only [Matrix.add_mulVec, single_mulVec', xi]; simp [Emb.y, neg_add_eq_sub])
        (fun u => by simp only [Matrix.add_mulVec, single_mulVec', m.embeddingMatrix_mulVec]; simp) v
      rwa [Pi.single_add] at this
    · have := U w (Complex.I • (Matrix.single (.inl m.i) (.inl m.i) 1 - Matrix.single (.inl m.i) (.inr m.j) 1 +
          Matrix.single (.inr m.j) (.inl m.i) 1 - Matrix.single (.inr m.j) (.inr m.j) 1))
        (by
          simp only [upq, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
            Matrix.conjTranspose_single, star_one, Complex.star_def, Complex.conj_I, Matrix.add_mul, Matrix.smul_mul,
            Matrix.mul_add, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, J_single, single_J, sg_l, sg_r, map_one]
          module)
        (by simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, single_mulVec', xi]; simp)
        (fun u => ⟨0, by simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, single_mulVec', m.embeddingMatrix_mulVec]; simp⟩) v
      rw [Pi.single_smul, map_smul, LinearMap.smul_apply, map_smul, Pi.single_sub, Pi.single_add, Pi.single_sub,
        smul_eq_zero] at this
      exact this.resolve_left Complex.I_ne_zero
    · have a1 := N w b 1 v
      have a2 := N w b Complex.I v
      rw [Complex.star_def, Complex.conj_I] at a2
      rw [star_one] at a1
      have : (2 * Complex.I) • D (act (un w (m.e b) (.inl m.i) - un w (m.e b) (.inr m.j)) v) = 0 := by
        linear_combination (norm := module) Complex.I • a1 + a2
      exact (smul_eq_zero.1 this).resolve_left (by simp)
    · have a1 := N w b 1 v
      have a2 := N w b Complex.I v
      rw [Complex.star_def, Complex.conj_I] at a2
      rw [star_one] at a1
      have : (2 * Complex.I * sg (m.e b)) • D (act (un w (.inl m.i) (m.e b) + un w (.inr m.j) (m.e b)) v) = 0 := by
        linear_combination (norm := module) a2 - Complex.I • a1
      exact (smul_eq_zero.1 this).resolve_left (by simp [sg0])
  exact par_line hM hM₁ (fun w b => congrArg _ (hΛ w b)) (par _ h) (par _ h') h0

theorem archimedean_multiplicity_one_of (hD : Dic) : ArchimedeanMultiplicityOne := by
  intro F E _ _ _ _ _ σ B a a' a₁ a₁' G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H' i₀ i₁ χ r hM hM₁ hS hH lam lam' h h' h0
  have b1 := hM₁.triple.geo.aBig
  have b2 := hM₁.triple.geo.eBig
  rcases hS with ⟨rfl, e1, e2, e3, rfl, rfl⟩ | ⟨e0, rfl, e2, e3, rfl, rfl⟩
  · refine core hD hM.triple hM.real hM₁.triple hM₁.real hH (embB _ _) (sg_embB _ _) (by omega) ?_ hM.triple.chars.expβ _ h h' h0
    rintro w (b | b) <;> simp [lamW, embB, e2, FockH1Action.cPair]
  · refine core hD hM.triple hM.real hM₁.triple hM₁.real hH (embA _ _) (sg_embA _ _) (by omega) ?_ hM.triple.chars.expα _ h h' h0
    have e4 : a - G.p = a₁ - G₁.p + 1 := by omega
    rw [e4, ← e2]
    rintro w (b | b) <;> simp [lamW, embA, FockH1Action.cPair]

end PositivityTheory.ThKG.CayleyTransformDarboux

end
end

section
namespace PositivityTheory.ThKG.CayleyTransformDarboux

theorem archimedean_multiplicity_one_of_lie (h1 : GlobalTheory.RealLift.LieFirst) (h2 : GlobalTheory.RealLift.LieSecond) : Loc.ArchimedeanMultiplicityOne :=
  archimedean_multiplicity_one_of ⟨PositivityTheory.RL.actsLaws, PositivityTheory.RL.fockEx PositivityTheory.RL.derEx,
    PositivityTheory.ThKEnd.Comp.PR.polRange_of PositivityTheory.RL.actsLaws PositivityTheory.RL.derEx (PositivityTheory.RL.vacLine PositivityTheory.RL.derEx), h1, h2,
    PositivityTheory.RL.lineEx, PositivityTheory.RL.frameEx, PositivityTheory.RL.even_im_hermitian_sub⟩

end PositivityTheory.ThKG.CayleyTransformDarboux
end
