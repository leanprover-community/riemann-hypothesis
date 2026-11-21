import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.Development
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.XflagEqMap
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.HTSpanLeft
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBCongruence

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

def RepM (f : Fin (r + 1) → S.V) (φ : S.V ≃ₗ[E] S.V) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  ∀ b, φ (f b) = ∑ c, A c b • f c

variable {f : Fin (r + 1) → S.V}



theorem sum_one (a : Fin (r + 1)) : ∑ d, (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) d a • f d = f a := by
  simp [Matrix.one_apply]


theorem exists_upUni {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) :
    ∃ N : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni N ∧ RepM (frame F) n N := by
  obtain ⟨-, h1, h2⟩ := hn
  have hzo : ∀ x ∈ Submodule.span E (Set.range F.fl.e), S.hT x F.fl.z = 0 := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨a, rfl⟩ := hy; exact F.fl.z_orth a
    | zero => simp
    | add y w _ _ hy hw => simp [hy, hw]
    | smul a y _ hy => simp [hy]
  have hzmem : F.fl.z ∈ orth S (Xsp F) := by
    simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
    exact fun x hx => hzo x hx
  have col : ∀ b : Fin (r + 1), ∃ v : Fin (r + 1) → E,
      (∀ c, b < c → v c = 0) ∧ v b = 1 ∧ n (frame F b) = ∑ c, v c • frame F c := by
    intro b
    cases b using Fin.lastCases with
    | last =>
      have hm : n F.fl.z - F.fl.z ∈ Submodule.span E (Set.range F.fl.e) := h2 _ hzmem
      obtain ⟨d, hd⟩ : ∃ d : Fin r → E, ∑ i, d i • F.fl.e i = n F.fl.z - F.fl.z := by
        rwa [Submodule.mem_span_range_iff_exists_fun] at hm
      refine ⟨Fin.snoc (α := fun _ => E) d 1, fun c hc => absurd hc (not_lt.2 (Fin.le_last c)), by simp, ?_⟩
      simp only [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_last, one_smul]
      rw [hd]
      abel
    | cast i =>
      have hi : F.fl.e i ∈ Submodule.span E (F.fl.e '' {k : Fin r | k.1 < i.1 + 1}) :=
        Submodule.subset_span ⟨i, by simp, rfl⟩
      have hm : n (F.fl.e i) - F.fl.e i ∈ Submodule.span E (F.fl.e '' {k : Fin r | k.1 < i.1}) := h1 i.1 _ hi
      obtain ⟨l, hl, hle⟩ : ∃ l ∈ Finsupp.supported E E {k : Fin r | k.1 < i.1},
          Finsupp.linearCombination E F.fl.e l = n (F.fl.e i) - F.fl.e i := by
        rw [← Finsupp.mem_span_image_iff_linearCombination]
        exact hm
      rw [Finsupp.mem_supported'] at hl
      have hli : l i = 0 := hl i (by simp)
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype l (fun k a => a • F.fl.e k) (fun k => zero_smul E _)] at hle
      refine ⟨Fin.snoc (α := fun _ => E) (fun k => if k = i then 1 else l k) 0, ?_, by simp, ?_⟩
      · intro c hc
        cases c using Fin.lastCases with
        | last => simp
        | cast k =>
          have hik : i < k := Fin.castSucc_lt_castSucc_iff.1 hc
          simp only [Fin.snoc_castSucc, if_neg (ne_of_gt hik)]
          exact hl k (by simp only [Set.mem_setOf_eq, not_lt]; exact Fin.le_iff_val_le_val.1 hik.le)
      · have key : ∀ k, (if k = i then (1 : E) else l k) = l k + if k = i then 1 else 0 := by
          intro k
          split_ifs with h
          · simp [h, hli]
          · simp
        simp only [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
          Fin.snoc_last, zero_smul, add_zero, key, add_smul, Finset.sum_add_distrib, ite_smul, one_smul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [hle]
        abel
  choose v hv0 hv1 hvn using col
  refine ⟨fun c b => v b c, ?_, ?_⟩
  · intro i j
    exact ⟨fun hji => hv0 j i hji, fun hij => by subst hij; exact hv1 i⟩
  · intro b
    exact hvn b

end Gen

end Formalism.L2.SG.Pf.RelativeIndexFlags
end
end

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {n : ℕ} {K : Type*} [Field K] [StarRing K]

theorem det_upUni {N : Matrix (Fin n) (Fin n) K} (h : IsUpUni N) : N.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => (h i j).1 hij)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

theorem det_loUni {L : Matrix (Fin n) (Fin n) K} (h : IsLoUni L) : L.det = 1 := by
  rw [Matrix.det_of_lowerTriangular L (fun i j hij => (h i j).1 (OrderDual.toDual_lt_toDual.1 hij))]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl


def unitOf (A : Matrix (Fin n) (Fin n) K) (h : A.det = 1) : Matrix.GeneralLinearGroup (Fin n) K :=
  Matrix.nonsingInvUnit A (by rw [h]; exact isUnit_one)

theorem conj_key (l1 l2 v : Matrix.GeneralLinearGroup (Fin n) K) (X : Matrix (Fin n) (Fin n) K) :
    ((l2⁻¹ * v⁻¹ * l1 : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((l1⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) * X * (l1 : Matrix (Fin n) (Fin n) K)) *
        (((l2⁻¹ * v⁻¹ * l1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (l2⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) *
        ((v⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) * X * (v : Matrix (Fin n) (Fin n) K)) *
        (l2 : Matrix (Fin n) (Fin n) K) := by
  simp [mul_inv_rev, mul_assoc]


end Mat

end Formalism.L2.SG.Pf.RelativeIndexFlags
end
end

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar


end Formalism.L2.SG.Pf.RelativeIndexFlags
end
end

section
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt

variable {n : ℕ} {K : Type*} [Field K]

def Bd (m : ℕ) (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ i j : Fin n, (i : ℕ) < j + m → A i j = 0

theorem Bd.mono {m m' : ℕ} {A : Matrix (Fin n) (Fin n) K} (h : m' ≤ m) (hA : Bd m A) : Bd m' A :=
  fun i j hij => hA i j (by omega)

theorem Bd.mul {m m' m'' : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : Bd m A) (hB : Bd m' B)
    (h : m'' ≤ m + m') : Bd m'' (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : (i : ℕ) < l + m
  · rw [hA i l hl, zero_mul]
  · rw [hB l j (by omega), mul_zero]

theorem Bd.add {m : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : Bd m A) (hB : Bd m B) : Bd m (A + B) :=
  fun i j h => by rw [Matrix.add_apply, hA i j h, hB i j h, add_zero]

theorem Bd.sub {m : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : Bd m A) (hB : Bd m B) : Bd m (A - B) :=
  fun i j h => by rw [Matrix.sub_apply, hA i j h, hB i j h, sub_zero]

theorem Bd.neg {m : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : Bd m A) : Bd m (-A) :=
  fun i j h => by rw [Matrix.neg_apply, hA i j h, neg_zero]

theorem Bd_zero (m : ℕ) : Bd m (0 : Matrix (Fin n) (Fin n) K) :=
  fun i j _ => by rw [Matrix.zero_apply]

theorem Bd_one : Bd 0 (1 : Matrix (Fin n) (Fin n) K) := by
  intro i j h
  rw [Matrix.one_apply_ne]
  intro e
  rw [e] at h
  omega

theorem Bd.pow {A : Matrix (Fin n) (Fin n) K} (hA : Bd 1 A) (k : ℕ) : Bd k (A ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact Bd_one
  | succ k ih => rw [pow_succ]; exact ih.mul hA le_rfl

theorem Bd.sum {ι : Type*} {m : ℕ} {s : Finset ι} {f : ι → Matrix (Fin n) (Fin n) K}
    (h : ∀ i ∈ s, Bd m (f i)) : Bd m (∑ i ∈ s, f i) :=
  fun i j hij => by
    rw [Matrix.sum_apply]
    exact Finset.sum_eq_zero fun l hl => h l hl i j hij

theorem Bd.eq_zero {A : Matrix (Fin n) (Fin n) K} (h : Bd n A) : A = 0 := by
  ext i j
  have := i.2
  exact h i j (by omega)

theorem inv_sub_one_bd (a : Matrix.GeneralLinearGroup (Fin n) K) (k : ℕ)
    (h : Bd (k + 1) ((a : Matrix (Fin n) (Fin n) K) - 1)) :
    Bd (k + 1) (((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) := by
  have hN1 : Bd 1 (-((a : Matrix (Fin n) (Fin n) K) - 1)) := (h.mono (by omega)).neg
  have hpow : (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ n = 0 := (hN1.pow n).eq_zero
  have hba : (∑ i ∈ Finset.range n, (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ i) *
      (a : Matrix (Fin n) (Fin n) K) = 1 := by
    have e := geom_sum_mul_neg (-((a : Matrix (Fin n) (Fin n) K) - 1)) n
    rw [hpow, sub_zero, sub_neg_eq_add, add_sub_cancel] at e
    exact e
  have hinv : ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ∑ i ∈ Finset.range n, (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ i := by
    calc ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
        = (∑ i ∈ Finset.range n, (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ i) *
            (a : Matrix (Fin n) (Fin n) K) *
            ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [hba, one_mul]
      _ = _ := by rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hb0 : Bd 0 (∑ i ∈ Finset.range n, (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ i) :=
    Bd.sum fun i _ => (hN1.pow i).mono (Nat.zero_le _)
  have e2 : (∑ i ∈ Finset.range n, (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ i) - 1 =
      -((∑ i ∈ Finset.range n, (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ i) *
        ((a : Matrix (Fin n) (Fin n) K) - 1)) := by
    rw [mul_sub, hba, mul_one]; abel
  rw [hinv, e2]
  exact (hb0.mul h (by omega)).neg

def FG (n : ℕ) (K : Type*) [Field K] (k : ℕ) : Subgroup (Matrix.GeneralLinearGroup (Fin n) K) where
  carrier := {a | Bd (k + 1) ((a : Matrix (Fin n) (Fin n) K) - 1)}
  one_mem' := by
    show Bd _ (((1 : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1)
    rw [Units.val_one, sub_self]; exact Bd_zero _
  mul_mem' := by
    intro a b ha hb
    show Bd _ (((a * b : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1)
    have e : ((a * b : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 =
        ((a : Matrix (Fin n) (Fin n) K) - 1) * ((b : Matrix (Fin n) (Fin n) K) - 1) +
          ((a : Matrix (Fin n) (Fin n) K) - 1) + ((b : Matrix (Fin n) (Fin n) K) - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [e]; exact ((Bd.mul ha hb (by omega)).add ha).add hb
  inv_mem' := fun {a} ha => inv_sub_one_bd a k ha


theorem FG_mono (k : ℕ) : FG n K (k + 1) ≤ FG n K k := fun _ ha => Bd.mono (by omega) ha




end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
end

section
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt

variable {G : Type*} [Group G]

theorem relIndex_eq_index_of_mul (A R : Subgroup G)
    (h : ∀ y : G, ∃ r ∈ R, ∃ a ∈ A, y = r * a) : A.relIndex R = A.index := by
  have hs : MulAction.stabilizer R (((1 : G) : G ⧸ A)) = A.subgroupOf R := by
    ext r
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change ((((r : G) * 1 : G)) : G ⧸ A) = ((1 : G) : G ⧸ A) ↔ _
    rw [mul_one, QuotientGroup.eq]
    simp
  have ho : MulAction.orbit R (((1 : G) : G ⧸ A)) = Set.univ := by
    ext q
    simp only [Set.mem_univ, iff_true]
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨r, hr, a, ha, rfl⟩ := h y
      refine ⟨⟨r, hr⟩, ?_⟩
      change ((((r : G) * 1 : G)) : G ⧸ A) = ((r * a : G) : G ⧸ A)
      rw [mul_one, QuotientGroup.eq]
      simpa using ha
  rw [Subgroup.relIndex, ← hs, MulAction.index_stabilizer, ho, Set.ncard_univ,
    Subgroup.index_eq_card]

theorem relIndex_eq_of_mul (A B B' : Subgroup G) (hBB : B ≤ B')
    (h : ∀ y ∈ B', ∃ b ∈ B, ∃ a ∈ A, y = b * a) : A.relIndex B = A.relIndex B' := by
  rw [← Subgroup.relIndex_subgroupOf hBB]
  refine relIndex_eq_index_of_mul (A.subgroupOf B') (B.subgroupOf B') ?_
  intro y
  obtain ⟨b, hb, a, ha, hy⟩ := h y.1 y.2
  have haB : a ∈ B' := by
    have : a = b⁻¹ * y.1 := by rw [hy]; group
    rw [this]; exact B'.mul_mem (B'.inv_mem (hBB hb)) y.2
  refine ⟨⟨b, hBB hb⟩, ?_, ⟨a, haB⟩, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]; exact hb
  · rw [Subgroup.mem_subgroupOf]; exact ha
  · apply Subtype.ext; simp [hy]

theorem inf_relIndex_of_le (H N L : Subgroup G) (hL : L ≤ N) :
    (H ⊓ N).relIndex L = H.relIndex L := by
  unfold Subgroup.relIndex
  congr 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, hL x.2⟩⟩

theorem relIndex_split (N : Subgroup G) [hN : N.Normal] (H X : Subgroup G) (hHX : H ≤ X) :
    H.relIndex X = (H ⊓ N).relIndex (X ⊓ N) * (H ⊔ N).relIndex (X ⊔ N) := by
  have e1 := Subgroup.relIndex_inf_mul_relIndex H (H ⊔ N) X
  rw [show H ⊓ (H ⊔ N) = H from inf_of_le_left le_sup_left] at e1
  have e2 : (H ⊔ N).relIndex X = (H ⊔ N).relIndex (X ⊔ N) := by
    refine relIndex_eq_of_mul _ _ _ le_sup_left ?_
    intro y hy
    obtain ⟨x, hx, z, hz, rfl⟩ := (Subgroup.mem_sup_of_normal_right).1 hy
    exact ⟨x, hx, z, Subgroup.mem_sup_right hz, rfl⟩
  have e3 : H.relIndex (X ⊓ N) = H.relIndex ((H ⊔ N) ⊓ X) := by
    refine relIndex_eq_of_mul _ _ _ ?_ ?_
    · intro y hy
      exact ⟨Subgroup.mem_sup_right hy.2, hy.1⟩
    · intro y hy
      obtain ⟨h, hh, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_right).1 hy.1
      refine ⟨y * h⁻¹, ⟨X.mul_mem hy.2 (X.inv_mem (hHX hh)), ?_⟩, h, hh, by group⟩
      rw [← hyz]
      have : h * z * h⁻¹ ∈ N := hN.conj_mem z hz h
      simpa [mul_assoc] using this
  rw [← e1, ← e3, e2, inf_relIndex_of_le H N (X ⊓ N) inf_le_right]

abbrev cj (g : G) (A : Subgroup G) : Subgroup G := A.map (MulAut.conj g).toMonoidHom

theorem mem_cj (g : G) (A : Subgroup G) (y : G) : y ∈ cj g A ↔ ∃ x ∈ A, g * x * g⁻¹ = y := by
  simp [cj, Subgroup.mem_map, MulAut.conj_apply]

end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
end

section
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt

variable {G : Type*} [Group G]


end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
end

section
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt

variable {n : ℕ} {K : Type*} [Field K] (L : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))

theorem sub_mono (k : ℕ) : (FG n K (k + 1)).subgroupOf L ≤ (FG n K k).subgroupOf L := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact FG_mono k hx






end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
end

section
namespace Formalism.L2.SG.Pf.RelativeIndexFlags


end Formalism.L2.SG.Pf.RelativeIndexFlags
end

section
open Formalism.L2.SG.Pf.RelativeIndexFlags

attribute [local instance] Formalism.BasicNotions.Host.cmStar
end
