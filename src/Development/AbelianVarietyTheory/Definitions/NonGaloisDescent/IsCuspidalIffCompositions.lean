module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

@[expose] public section

noncomputable section

open Matrix Formalism.L2.DIV GlobalTheory.FiniteGL GlobalTheory.PRep
open scoped TensorProduct

namespace GlobalTheory.Parabolic

section Groups

variable {k : Type} [Field k] {N : ℕ}

theorem blockDiag_iff {b : Fin N → ℕ} {M : Matrix (Fin N) (Fin N) k} :
    (∀ i j, b i ≠ b j → M i j = 0) ↔ M.BlockTriangular b ∧ M.BlockTriangular (OrderDual.toDual ∘ b) := by
  constructor
  · exact fun h => ⟨fun i j hij => h i j (ne_of_gt hij), fun i j hij => h i j (ne_of_lt (OrderDual.toDual_lt_toDual.1 hij))⟩
  · rintro ⟨h1, h2⟩ i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact h2 (OrderDual.toDual_lt_toDual.2 h)
    · exact h1 h

variable (k) in
def levi (b : Fin N → ℕ) : Subgroup (GL (Fin N) k) where
  carrier := {g | ∀ i j, b i ≠ b j → (g : Matrix (Fin N) (Fin N) k) i j = 0}
  one_mem' := fun i j hij => by
    rw [Units.val_one, Matrix.one_apply_ne (fun e => hij (congrArg b e))]
  mul_mem' := by
    intro x y hx hy
    have hx' := blockDiag_iff.1 hx
    have hy' := blockDiag_iff.1 hy
    refine blockDiag_iff.2 ?_
    rw [Units.val_mul]
    exact ⟨hx'.1.mul hy'.1, hx'.2.mul hy'.2⟩
  inv_mem' := by
    intro x hx
    have hx' := blockDiag_iff.1 hx
    letI := x.invertible
    refine blockDiag_iff.2 ?_
    rw [Matrix.coe_units_inv]
    exact ⟨blockTriangular_inv_of_blockTriangular hx'.1, blockTriangular_inv_of_blockTriangular hx'.2⟩

theorem mem_levi {b : Fin N → ℕ} {g : GL (Fin N) k} :
    g ∈ levi k b ↔ ∀ i j, b i ≠ b j → (g : Matrix (Fin N) (Fin N) k) i j = 0 := Iff.rfl

theorem levi_congr {b b' : Fin N → ℕ} (h : ∀ i j, b i = b j ↔ b' i = b' j) : levi k b = levi k b' := by
  ext g
  simp only [mem_levi, ne_eq, h]

theorem levi_le_blockTri (b : Fin N → ℕ) : levi k b ≤ blockTri b := fun _ hg i j hij => hg i j (ne_of_gt hij)

theorem unipRadical_le_blockTri (b : Fin N → ℕ) : unipRadical k b ≤ blockTri b :=
  fun _ hu => blockTriangular_of_sub_one hu

def diagPart (b : Fin N → ℕ) (M : Matrix (Fin N) (Fin N) k) : Matrix (Fin N) (Fin N) k :=
  Matrix.of fun i j => if b i = b j then M i j else 0

theorem diagPart_mul {b : Fin N → ℕ} {X Y : Matrix (Fin N) (Fin N) k} (hX : X.BlockTriangular b)
    (hY : Y.BlockTriangular b) : diagPart b (X * Y) = diagPart b X * diagPart b Y := by
  ext i j
  simp only [diagPart_apply, Matrix.mul_apply]
  split_ifs with hij
  · refine Finset.sum_congr rfl fun l _ => ?_
    rcases lt_trichotomy (b l) (b i) with h | h | h
    · rw [hX h, if_neg h.ne', zero_mul, zero_mul]
    · rw [if_pos h.symm, if_pos (h.trans hij)]
    · rw [hY (hij ▸ h), if_neg h.ne, mul_zero, zero_mul]
  · refine (Finset.sum_eq_zero fun l _ => ?_).symm
    by_cases h : b i = b l
    · rw [if_neg (fun h' : b l = b j => hij (h.trans h')), mul_zero]
    · rw [if_neg h, zero_mul]

def diagPartHom (b : Fin N → ℕ) : blockTri (κ := k) b →* Matrix (Fin N) (Fin N) k where
  toFun p := diagPart b ((p : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
  map_one' := by
    ext i j
    by_cases h : i = j
    · subst h; simp [diagPart_apply]
    · simp [diagPart_apply, Matrix.one_apply_ne h]
  map_mul' x y := diagPart_mul x.2 y.2

def leviProj (b : Fin N → ℕ) : blockTri (κ := k) b →* levi k b :=
  MonoidHom.codRestrict (diagPartHom (k := k) b).toHomUnits (levi k b) fun p i j hij =>
    (if_neg hij : diagPart b ((p : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = 0)

theorem leviProj_apply (b : Fin N → ℕ) (p : blockTri (κ := k) b) (i j : Fin N) :
    (((leviProj b p : levi k b) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      if b i = b j then ((p : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j else 0 := rfl

theorem leviProj_inclusion (b : Fin N → ℕ) (m : levi k b) :
    leviProj b (Subgroup.inclusion (levi_le_blockTri b) m) = m := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [leviProj_apply]
  split_ifs with h
  · rfl
  · exact (m.2 i j h).symm

theorem leviProj_eq_one_iff (b : Fin N → ℕ) (p : blockTri (κ := k) b) :
    leviProj b p = 1 ↔ (p : GL (Fin N) k) ∈ unipRadical k b := by
  rw [mem_unipRadical]
  constructor
  · intro h i j hij
    have e := leviProj_apply b p i j
    rw [h] at e
    rcases hij.eq_or_lt with h' | h'
    · rw [if_pos h'.symm] at e
      rw [Matrix.sub_apply, ← e]
      simp
    · rw [Matrix.sub_apply, p.2 h', Matrix.one_apply_ne (fun e => by rw [e] at h'; exact lt_irrefl _ h'), sub_zero]
  · intro h
    apply Subtype.ext
    apply Units.ext
    ext i j
    rw [leviProj_apply]
    split_ifs with h'
    · have := h i j h'.ge
      rw [Matrix.sub_apply, sub_eq_zero] at this
      simpa using this
    · simp [Matrix.one_apply_ne (fun e => h' (congrArg b e))]

theorem ker_leviProj (b : Fin N → ℕ) :
    (leviProj (k := k) b).ker = (unipRadical k b).subgroupOf (blockTri b) :=
  Subgroup.ext fun p => leviProj_eq_one_iff b p

theorem blockTri_le_normalizer (b : Fin N → ℕ) :
    blockTri b ≤ Subgroup.normalizer ((unipRadical k b : Subgroup (GL (Fin N) k)) : Set (GL (Fin N) k)) := by
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (unipRadical_le_blockTri b), ← ker_leviProj]
  infer_instance

variable (k) in
def permGL : Equiv.Perm (Fin N) →* GL (Fin N) k := (Matrix.permMatrixHom (R := k)).toHomUnits

theorem permGL_apply (w : Equiv.Perm (Fin N)) (i j : Fin N) :
    ((permGL k w : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = if i = w j then 1 else 0 := by
  show (w⁻¹.permMatrix k) i j = _
  simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Equiv.Perm.inv_eq_iff_eq]

theorem conj_permGL_apply (w : Equiv.Perm (Fin N)) (g : GL (Fin N) k) (i j : Fin N) :
    ((permGL k w * g * (permGL k w)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (w i) (w j) =
      (g : Matrix (Fin N) (Fin N) k) i j := by
  rw [← map_inv, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_apply, permGL_apply]
  simp

theorem conj_mem_iff {w : Equiv.Perm (Fin N)} {g : GL (Fin N) k} (R : Fin N → Fin N → Prop) (c : Matrix (Fin N) (Fin N) k)
    (hc : ∀ i j, c (w i) (w j) = c i j) :
    (∀ i j, R i j → ((permGL k w * g * (permGL k w)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = c i j) ↔
      ∀ i j, R (w i) (w j) → (g : Matrix (Fin N) (Fin N) k) i j = c i j := by
  constructor
  · intro h i j hij
    rw [← conj_permGL_apply w, h _ _ hij, hc]
  · intro h i j hij
    obtain ⟨i, rfl⟩ := w.surjective i
    obtain ⟨j, rfl⟩ := w.surjective j
    rw [conj_permGL_apply, h _ _ hij, hc]

theorem conj_mem_blockTri {b : Fin N → ℕ} {w : Equiv.Perm (Fin N)} {g : GL (Fin N) k} :
    permGL k w * g * (permGL k w)⁻¹ ∈ blockTri b ↔ g ∈ blockTri (b ∘ w) :=
  conj_mem_iff (fun i j => b j < b i) 0 fun _ _ => rfl

theorem conj_mem_levi {b : Fin N → ℕ} {w : Equiv.Perm (Fin N)} {g : GL (Fin N) k} :
    permGL k w * g * (permGL k w)⁻¹ ∈ levi k b ↔ g ∈ levi k (b ∘ w) :=
  conj_mem_iff (fun i j => b i ≠ b j) 0 fun _ _ => rfl

theorem conj_mem_unipRadical {b : Fin N → ℕ} {w : Equiv.Perm (Fin N)} {g : GL (Fin N) k} :
    permGL k w * g * (permGL k w)⁻¹ ∈ unipRadical k b ↔ g ∈ unipRadical k (b ∘ w) := by
  simp only [mem_unipRadical, Matrix.sub_apply, sub_eq_zero]
  exact conj_mem_iff (fun i j => b j ≤ b i) 1 fun i j => by simp [Matrix.one_apply]

def leviConj (b : Fin N → ℕ) (w : Equiv.Perm (Fin N)) : levi k (b ∘ w) ≃* levi k b where
  toFun x := ⟨permGL k w * x * (permGL k w)⁻¹, conj_mem_levi.2 x.2⟩
  invFun y := ⟨(permGL k w)⁻¹ * y * permGL k w, conj_mem_levi.1 (by simpa [mul_assoc] using y.2)⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

end Groups

section Blocks

variable {k : Type} [Field k] {N : ℕ}

def leviBlock (b : Fin N → ℕ) {n : ℕ} (f : Fin n → Fin N) (hf : Function.Injective f)
    (hr : ∀ i j, b (f i) = b j → j ∈ Set.range f) : levi k b →* GL (Fin n) k :=
  MonoidHom.toHomUnits
    { toFun := fun g => ((g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix f f
      map_one' := by
        ext i j
        simp [Matrix.one_apply, hf.eq_iff]
      map_mul' := by
        intro x y
        show ((x.1 * y.1 : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix _ _ = _
        rw [Units.val_mul]
        refine submatrix_mul_of_zero _ hf _ _ fun i j l hl => ?_
        rw [x.2 _ _ fun e => hl (hr i l e), zero_mul] }

variable {h : ℕ} {d : Fin h → ℕ}

def blockOf (e : (Σ a, Fin (d a)) ≃ Fin N) : Fin N → ℕ := fun i => ((e.symm i).1 : ℕ)

@[simp] theorem blockOf_apply (e : (Σ a, Fin (d a)) ≃ Fin N) (x : Σ a, Fin (d a)) : blockOf e (e x) = x.1 := by
  simp [blockOf]

variable {r t : ℕ}

def twoEquiv (hN : r + t = N) : Fin r ⊕ Fin t ≃ Fin N := finSumFinEquiv.trans (finCongr hN)

@[local simp] private theorem twoEquiv_inl_lt (hN : r + t = N) (i : Fin r) :
    (twoEquiv hN (Sum.inl i) : ℕ) < r := i.isLt

@[local simp] private theorem twoEquiv_inr_not_lt (hN : r + t = N) (i : Fin t) :
    ¬ (twoEquiv hN (Sum.inr i) : ℕ) < r :=
  Nat.not_lt.mpr (Nat.le_add_right r i.val)

end Blocks

section General

variable {G H : Type} [Group G] [Group H] {V W X : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

theorem mem_fixed {ρ : Representation ℂ G V} {U : Subgroup G} {v : V} : v ∈ fixed ρ U ↔ ∀ u ∈ U, ρ u v = v := by
  constructor
  · intro h u hu
    simpa using h ⟨u, hu⟩
  · intro h u
    simpa using h u u.2

def Embeds (ρ : Representation ℂ G V) (σ : Representation ℂ G W) : Prop :=
  ∃ f : ρ.IntertwiningMap σ, Function.Injective f

theorem isIrreducible_of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ)
    (h : ρ.IsIrreducible) : σ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule] at h ⊢
  exact IsSimpleModule.congr (LinearEquiv.ofBijective
    (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ e.symm.toIntertwiningMap) e.symm.toLinearEquiv.bijective)

@[simp] theorem extTensor_tprod {ι : Type} {Γ Y : ι → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℂ (Y a)] (ρ : ∀ a, Representation ℂ (Γ a) (Y a)) (x : ∀ a, Γ a) (v : ∀ a, Y a) :
    extTensor ρ x (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ fun a => ρ a (x a) (v a) :=
  PiTensorProduct.map_tprod _ _

end General

section Functors

variable {k : Type} [Field k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

@[simp] theorem toHcInd_apply (b : Fin N → ℕ) (ρ : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (levi k b) W)
    (L : V →ₗ[ℂ] W) (hL : ∀ (p : blockTri (κ := k) b) (v : V), L (ρ p v) = σ (leviProj b p) (L v)) (v : V)
    (x : GL (Fin N) k) : (toHcInd b ρ σ L hL v : GL (Fin N) k → W) x = L (ρ x v) := rfl

variable {h : ℕ} {d : Fin h → ℕ} {Y : Fin h → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]

@[simp] theorem leviTensor_tprod (e : (Σ a, Fin (d a)) ≃ Fin N) (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a))
    (m : levi k (blockOf e)) (v : ∀ a, Y a) :
    leviTensor e ρ m (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ fun a => ρ a (leviEquiv e m a) (v a) :=
  extTensor_tprod _ _ _

variable {r t : ℕ}

end Functors

section Cuspidal

variable {k : Type} [Field k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem fixed_eq_bot_iff {ρ : Representation ℂ (GL (Fin N) k) V} {U : Subgroup (GL (Fin N) k)} :
    fixed ρ U = ⊥ ↔ ∀ v : V, (∀ u ∈ U, ρ u v = v) → v = 0 := by
  simp only [Submodule.eq_bot_iff, mem_fixed]

theorem isCuspidal_iff_forall (ρ : Representation ℂ (GL (Fin N) k) V) :
    IsCuspidal ρ ↔ ∀ b : Fin N → ℕ, (∃ i j, b i ≠ b j) → fixed ρ (unipRadical k b) = ⊥ := by
  refine ⟨fun h b ⟨i, j, hij⟩ => fixed_eq_bot_iff.2 fun v hv => ?_, fun h b _ hb => fixed_eq_bot_iff.1 (h b hb)⟩
  set w := Tuple.sort b
  have h0 : ρ (permGL k w)⁻¹ v = 0 := by
    refine h (b ∘ w) (Tuple.monotone_sort b) ⟨w.symm i, w.symm j, by simpa using hij⟩ _ fun u hu => ?_
    conv_rhs => rw [← hv _ (conj_mem_unipRadical.2 hu)]
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  have h1 := congrArg (ρ (permGL k w)) h0
  rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_zero, Module.End.one_apply] at h1

end Cuspidal

end GlobalTheory.Parabolic
