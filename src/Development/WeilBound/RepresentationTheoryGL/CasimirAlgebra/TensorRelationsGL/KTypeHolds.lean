import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGl
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PStepFormula
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.QdetFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.RowCol
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.Central
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSpectrum
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PHeight
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PChain
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PColAnti
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransFin
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransAll
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PWallAlg
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGK
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PLieInv
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSWStart
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PContract
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PYoung
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PKType

section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace CurryingSwaps

variable {α : Type*} {m k : ℕ}

theorem upd_castAdd (I : Fin m → α) (J : Fin k → α) (i : Fin m) (v : α) :
    Function.update (Fin.append I J) (Fin.castAdd k i) v = Fin.append (Function.update I i v) J := by
  funext x
  refine Fin.addCases (fun i' => ?_) (fun j' => ?_) x
  · by_cases h : i' = i
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (Fin.castAdd_injective _ _ e)), Fin.append_left, Fin.append_left,
        Function.update_of_ne h]
  · rw [Function.update_of_ne (fun e => by simp [Fin.ext_iff] at e; omega), Fin.append_right, Fin.append_right]

theorem upd_natAdd (I : Fin m → α) (J : Fin k → α) (j : Fin k) (v : α) :
    Function.update (Fin.append I J) (Fin.natAdd m j) v = Fin.append I (Function.update J j v) := by
  funext x
  refine Fin.addCases (fun i' => ?_) (fun j' => ?_) x
  · rw [Function.update_of_ne (fun e => by simp [Fin.ext_iff] at e; omega), Fin.append_left, Fin.append_left]
  · by_cases h : j' = j
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (Fin.natAdd_injective _ _ e)), Fin.append_right, Fin.append_right,
        Function.update_of_ne h]

theorem swap_castAdd (I : Fin m → α) (J : Fin k → α) (i i' : Fin m) :
    Fin.append I J ∘ Equiv.swap (Fin.castAdd k i) (Fin.castAdd k i') = Fin.append (I ∘ Equiv.swap i i') J := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x
  · simp only [Function.comp_apply, Fin.append_left, Equiv.swap_apply_def, Fin.castAdd_inj]
    split_ifs <;> simp
  · have h1 : Fin.natAdd m b ≠ Fin.castAdd k i := fun e => by simp [Fin.ext_iff] at e; omega
    have h2 : Fin.natAdd m b ≠ Fin.castAdd k i' := fun e => by simp [Fin.ext_iff] at e; omega
    simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_right]

theorem swap_natAdd (I : Fin m → α) (J : Fin k → α) (j j' : Fin k) :
    Fin.append I J ∘ Equiv.swap (Fin.natAdd m j) (Fin.natAdd m j') = Fin.append I (J ∘ Equiv.swap j j') := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x
  · have h1 : Fin.castAdd k a ≠ Fin.natAdd m j := fun e => by simp [Fin.ext_iff] at e; omega
    have h2 : Fin.castAdd k a ≠ Fin.natAdd m j' := fun e => by simp [Fin.ext_iff] at e; omega
    simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_left]
  · simp only [Function.comp_apply, Fin.append_right, Equiv.swap_apply_def, Fin.natAdd_inj]
    split_ifs <;> simp

theorem swap_mixed (I : Fin m → α) (J : Fin k → α) (i : Fin m) (j : Fin k) :
    Fin.append I J ∘ Equiv.swap (Fin.castAdd k i) (Fin.natAdd m j) =
      Fin.append (Function.update I i (J j)) (Function.update J j (I i)) := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x
  · have h2 : Fin.castAdd k a ≠ Fin.natAdd m j := fun e => by simp [Fin.ext_iff] at e; omega
    by_cases h : a = i
    · subst h; simp
    · have h1 : Fin.castAdd k a ≠ Fin.castAdd k i := fun e => h (Fin.castAdd_injective _ _ e)
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_left,
        Function.update_of_ne h]
  · have h1 : Fin.natAdd m b ≠ Fin.castAdd k i := fun e => by simp [Fin.ext_iff] at e; omega
    by_cases h : b = j
    · subst h; simp
    · have h2 : Fin.natAdd m b ≠ Fin.natAdd m j := fun e => h (Fin.natAdd_injective _ _ e)
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_right,
        Function.update_of_ne h]

theorem iteApp {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (p : Prop) [Decidable p]
    (g : V →ₗ[ℂ] W) (x : V) : (if p then g else 0) x = if p then g x else 0 := by
  split_ifs <;> rfl

end CurryingSwaps

open CurryingSwaps in
theorem curry_holds : Curry := by
  intro n M _ _ E m k
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g h
    funext K
    have := congrFun (congrFun (congrArg (fun x => x) h) (fun j => K (Fin.natAdd m j))) (fun i => K (Fin.castAdd k i))
    simpa only [curF_apply, Fin.append_castAdd_natAdd] using this
  · intro g
    refine ⟨fun K => g (fun j => K (Fin.natAdd m j)) (fun i => K (Fin.castAdd k i)), ?_⟩
    funext J I
    simp only [curF_apply, Fin.append_left, Fin.append_right]
  · intro a b
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    simp only [LinearMap.comp_apply, curF_apply, tE_apply, Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply,
      Fin.sum_univ_add, Fin.append_left, Fin.append_right, upd_castAdd, upd_natAdd, add_assoc]
  · intro i
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    have hz : ∀ b : Fin k, ¬ (Fin.natAdd m b < Fin.castAdd k i) := fun b h => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] at h <;> omega
    have hc : ∀ x : Fin m, Fin.castAdd k x < Fin.castAdd k i ↔ x < i := fun x => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] <;> omega
    simp only [xJ, LinearMap.comp_apply, LinearMap.add_apply, Pi.add_apply, Om_apply, LinearMap.sum_apply,
      Finset.sum_apply, pm_apply, iteApp, ite_apply, Pi.zero_apply, lift_apply, curF_apply, Fin.append_left, upd_castAdd, Finset.sum_filter,
      Fin.sum_univ_add, swap_castAdd, hz, hc, if_false, Finset.sum_const_zero, add_zero]
  · intro j
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    have hz : ∀ x : Fin m, Fin.castAdd k x < Fin.natAdd m j := fun x => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] <;> omega
    have hc : ∀ b : Fin k, Fin.natAdd m b < Fin.natAdd m j ↔ b < j := fun b => by
      simp only [Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd] <;> omega
    simp only [xJ, LinearMap.comp_apply, LinearMap.add_apply, Pi.add_apply, Om_apply, LinearMap.sum_apply,
      Finset.sum_apply, pm_apply, iteApp, ite_apply, Pi.zero_apply, curF_apply, tE_apply, Fin.append_right, upd_natAdd, upd_castAdd,
      Finset.sum_filter, Fin.sum_univ_add, swap_natAdd, swap_mixed, hz, hc, if_true, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun x p => if I p = x then
      f (Fin.append (Function.update I p (J j)) (Function.update J j x)) else 0)]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, add_assoc]
  · intro B
    rfl
  · intro i i'
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    simp only [LinearMap.comp_apply, curF_apply, pm_apply, lift_apply, swap_castAdd]
  · intro j j'
    refine LinearMap.ext fun f => funext fun J => funext fun I => ?_
    simp only [LinearMap.comp_apply, curF_apply, pm_apply, swap_natAdd]

end PositivityTheory.Rg.Cz

end
end

section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace JMA

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem comp_swap {P : Type} [DecidableEq P] (I : P → Fin n) (p j : P) (_h : p ≠ j) :
    I ∘ Equiv.swap p j = Function.update (Function.update I p (I j)) j (I p) := by
  funext q
  simp only [Function.comp_apply, Function.update_apply, Equiv.swap_apply_def]
  split_ifs <;> subst_vars <;> simp_all

theorem pm_swap_eq {P : Type} [DecidableEq P] (p j : P) (h : p ≠ j) :
    (pm (Equiv.swap p j) : Module.End ℂ (TV n M P)) = ∑ a, ∑ b, eAt p a b * eAt j b a := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [pm_apply, comp_swap I p j h]
  simp only [LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, eAt_apply,
    Function.update_apply, if_neg (Ne.symm h)]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem xJ_eq {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (j : Fin m) :
    xJ E j = ∑ a, ∑ b, tE (Finset.univ.filter (· < j)) E a b * eAt j b a := by
  have hs : ∀ i ∈ Finset.univ.filter (· < j),
      pm (Equiv.swap i j) = ∑ a, ∑ b, (eAt i a b * eAt j b a : Module.End ℂ (TV n M (Fin m))) :=
    fun i hi => pm_swap_eq i j (ne_of_lt (Finset.mem_filter.1 hi).2)
  show Om E j + ∑ i ∈ Finset.univ.filter (· < j), pm (Equiv.swap i j) = _
  rw [Finset.sum_congr rfl hs]
  simp only [tE, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

theorem eAt_eq_sub {P : Type} [DecidableEq P] (S : Finset P) (j : P) (hj : j ∉ S)
    (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    (eAt j a b : Module.End ℂ (TV n M P)) = tE (insert j S) E a b - tE S E a b := by
  simp only [tE, Finset.sum_insert hj]
  abel

theorem comm_xJ {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (j : Fin m) (X : Module.End ℂ (TV n M (Fin m)))
    (h1 : ∀ a b, Commute X (tE (Finset.univ.filter (· < j)) E a b))
    (h2 : ∀ a b, Commute X (tE (insert j (Finset.univ.filter (· < j))) E a b)) : Commute X (xJ E j) := by
  rw [xJ_eq]
  refine Commute.sum_right _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ => (h1 a b).mul_right ?_
  rw [eAt_eq_sub (Finset.univ.filter (· < j)) j (by simp) E]
  exact (h2 b a).sub_right (h1 b a)

theorem swap_pres {P : Type} [DecidableEq P] (S : Finset P) (i j : P) (h : i ∈ S ↔ j ∈ S) (q : P) :
    Equiv.swap i j q ∈ S ↔ q ∈ S := by
  rcases eq_or_ne q i with rfl | hi
  · rw [Equiv.swap_apply_left]
    exact h.symm
  rcases eq_or_ne q j with rfl | hj
  · rw [Equiv.swap_apply_right]
    exact h
  · rw [Equiv.swap_apply_of_ne_of_ne hi hj]

theorem swap_comm_xJ (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (k i j : Fin m)
    (h1 : i < k ↔ j < k) (h2 : (i = k ∨ i < k) ↔ (j = k ∨ j < k)) :
    Commute (pm (Equiv.swap i j)) (xJ E k) :=
  comm_xJ E k _ (fun a b => (hT n M (Fin m) E hE _).2.2.1 _ (swap_pres _ i j (by simpa using h1)) a b)
    (fun a b => (hT n M (Fin m) E hE _).2.2.1 _ (swap_pres _ i j (by simpa using h2)) a b)

theorem om_comm_xJ (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (h : i < j) : Commute (Om E i) (xJ E j) :=
  comm_xJ E j _ (fun a b => (hT n M (Fin m) E hE _).2.1 i (by simpa using h) a b)
    (fun a b => (hT n M (Fin m) E hE _).2.1 i (by simp [h]) a b)

theorem xJ_comm_lt (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (h : i < j) : Commute (xJ E i) (xJ E j) := by
  show Commute (Om E i + ∑ l ∈ Finset.univ.filter (· < i), pm (Equiv.swap l i)) (xJ E j)
  refine (om_comm_xJ hT hE i j h).add_left (Commute.sum_left _ _ _ fun l hl => ?_)
  have hl' : l < i := (Finset.mem_filter.1 hl).2
  exact swap_comm_xJ hT hE j l i (iff_of_true (hl'.trans h) h)
    (iff_of_true (Or.inr (hl'.trans h)) (Or.inr h))

theorem xJ_comm (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m) :
    Commute (xJ E i) (xJ E j) := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact xJ_comm_lt hT hE i j h
  · exact Commute.refl _
  · exact (xJ_comm_lt hT hE j i h).symm

theorem pm_swap_sq {P : Type} (i j : P) [DecidableEq P] :
    (pm (Equiv.swap i j) : Module.End ℂ (TV n M P)) * pm (Equiv.swap i j) = 1 := by
  rw [← pm_mul, Equiv.swap_mul_self, pm_one]

theorem xJ_succ (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (hij : (i : ℕ) + 1 = j) :
    xJ E j = pm (Equiv.swap i j) * xJ E i * pm (Equiv.swap i j) + pm (Equiv.swap i j) := by
  have hOm : pm (Equiv.swap i j) * Om E i * pm (Equiv.swap i j) = Om E j := by
    rw [(hT n M (Fin m) E hE (∅ : Finset (Fin m))).2.2.2, mul_assoc, pm_swap_sq, mul_one,
      Equiv.swap_apply_left]
  have hsum : ∀ l ∈ Finset.univ.filter (· < i),
      pm (Equiv.swap i j) * pm (Equiv.swap l i) * pm (Equiv.swap i j) =
        (pm (Equiv.swap l j) : Module.End ℂ (TV n M (Fin m))) := by
    intro l hl
    have hl' : (l : ℕ) < i := (Finset.mem_filter.1 hl).2
    rw [← pm_mul, ← pm_mul]
    congr 1
    refine Equiv.ext fun x => ?_
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff] <;> omega
  have hset : Finset.univ.filter (· < j) = insert i (Finset.univ.filter (· < i)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.lt_iff_val_lt_val, Fin.ext_iff]
    omega
  show Om E j + ∑ l ∈ Finset.univ.filter (· < j), pm (Equiv.swap l j) =
    pm (Equiv.swap i j) * (Om E i + ∑ l ∈ Finset.univ.filter (· < i), pm (Equiv.swap l i)) *
      pm (Equiv.swap i j) + pm (Equiv.swap i j)
  rw [hset, Finset.sum_insert (by simp), mul_add, add_mul, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_congr rfl hsum, hOm]
  abel

theorem xJ_mul_swap (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (hij : (i : ℕ) + 1 = j) : xJ E j * pm (Equiv.swap i j) = pm (Equiv.swap i j) * xJ E i + 1 := by
  rw [xJ_succ hT hE i j hij]
  simp only [add_mul, mul_assoc, pm_swap_sq, mul_one]

theorem swap_mul_xJ (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (hij : (i : ℕ) + 1 = j) : pm (Equiv.swap i j) * xJ E j = xJ E i * pm (Equiv.swap i j) + 1 := by
  rw [xJ_succ hT hE i j hij]
  simp only [mul_add, ← mul_assoc, pm_swap_sq, one_mul]

theorem list_prod_comm {A : Type} [Monoid A] (x : A) : ∀ (L : List A) (k : ℕ) (hk : k + 1 < L.length),
    (∀ t (ht : t < L.length), t ≠ k → t ≠ k + 1 → Commute L[t] x) → Commute (L[k] * L[k + 1]) x →
      Commute L.prod x
  | [], k, hk, _, _ => by simp at hk
  | [a], k, hk, _, _ => by simp at hk
  | a :: b :: L, 0, hk, h1, h2 => by
    rw [List.prod_cons, List.prod_cons, ← mul_assoc]
    refine h2.mul_left (Commute.list_prod_left _ _ fun y hy => ?_)
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hy
    exact h1 (t + 2) (by simp; omega) (by omega) (by omega)
  | a :: L, k + 1, hk, h1, h2 => by
    rw [List.prod_cons]
    exact (h1 0 (by simp) (by omega) (by omega)).mul_left (list_prod_comm x L k (by simpa using hk)
      (fun t ht h h' => h1 (t + 1) (by simpa using ht) (by omega) (by omega)) h2)

theorem pair_comm {A : Type} [Ring A] [Algebra ℂ A] (u : ℂ) (a b p : A) (hab : Commute a b)
    (h1 : b * p = p * a + 1) (h2 : p * b = a * p + 1) :
    Commute ((algebraMap ℂ A u + a) * (algebraMap ℂ A u + b)) p := by
  have hU : ∀ z : A, Commute (algebraMap ℂ A u) z := fun z => Algebra.commutes u z
  have hs : Commute (a + b) p := by
    show (a + b) * p = p * (a + b)
    rw [add_mul, mul_add, h1, h2]
    abel
  have hp : Commute (a * b) p := by
    show a * b * p = p * (a * b)
    calc a * b * p = a * (p * a + 1) := by rw [mul_assoc, h1]
      _ = (a * p + 1) * a := by noncomm_ring
      _ = p * b * a := by rw [h2]
      _ = p * (a * b) := by rw [mul_assoc, hab.eq]
  have he : (algebraMap ℂ A u + a) * (algebraMap ℂ A u + b) =
      algebraMap ℂ A u * algebraMap ℂ A u + algebraMap ℂ A u * (a + b) + a * b := by
    rw [add_mul, mul_add, mul_add, ← (hU a).eq, mul_add]
    abel
  rw [he]
  exact (((hU p).mul_left (hU p)).add_left ((hU p).mul_left hs)).add_left hp

theorem piJ_comm_adj (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (u : ℂ)
    (i : Fin m) : Commute (PiJ (m + 1) E u) (pm (Equiv.swap i.castSucc i.succ)) := by
  have hij : ((i.castSucc : Fin (m + 1)) : ℕ) + 1 = i.succ := by simp
  show Commute (List.ofFn fun j : Fin (m + 1) => algebraMap ℂ (Module.End ℂ (TV n M (Fin (m + 1)))) u + xJ E j).prod _
  apply list_prod_comm _ _ i (by simp)
  · intro t ht h1 h2
    rw [List.getElem_ofFn]
    refine Commute.add_left (Algebra.commutes u _) ?_
    refine (swap_comm_xJ hT hE ⟨t, by simpa using ht⟩ i.castSucc i.succ ?_ ?_).symm
    · simp only [Fin.lt_iff_val_lt_val, Fin.coe_castSucc, Fin.val_succ]
      omega
    · simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]
      omega
  · simp only [List.getElem_ofFn]
    exact pair_comm u _ _ _ (xJ_comm hT hE _ _) (xJ_mul_swap hT hE _ _ hij) (swap_mul_xJ hT hE _ _ hij)

theorem piJ_comm (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) (m : ℕ) (u : ℂ)
    (σ : Equiv.Perm (Fin m)) : Commute (PiJ m E u) (pm σ) := by
  cases m with
  | zero =>
    rw [Subsingleton.elim σ 1, pm_one]
    exact Commute.one_right _
  | succ m =>
    have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    induction hσ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact piJ_comm_adj hT hE u i
    | one =>
      rw [pm_one]
      exact Commute.one_right _
    | mul x y _ _ hx hy =>
      rw [pm_mul]
      exact hx.mul_right hy

end JMA

theorem jmComm_of : TensorGl → JMComm := by
  intro hT n M _ _ E hE m
  refine ⟨JMA.xJ_comm hT hE, fun i j h => ⟨JMA.xJ_mul_swap hT hE i j h, fun k hk1 hk2 => ?_⟩,
    fun u σ => JMA.piJ_comm hT hE m u σ⟩
  have e1 := Fin.val_ne_of_ne hk1
  have e2 := Fin.val_ne_of_ne hk2
  refine (JMA.swap_comm_xJ hT hE k i j ?_ ?_).symm
  · simp only [Fin.lt_iff_val_lt_val]
    omega
  · simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff]
    omega

end PositivityTheory.Rg.Cz

end
end

section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace QuantumDeterminantProducts

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def sg (σ : Equiv.Perm (Fin n)) : ℂ := ((Equiv.Perm.sign σ : ℤ) : ℂ)

theorem sg_swap {i j : Fin n} (h : i ≠ j) : sg (Equiv.swap i j) = -1 := by
  simp [sg, Equiv.Perm.sign_swap h]

def IsAnti (g : TV n M (Fin n)) : Prop := ∀ σ : Equiv.Perm (Fin n), pm σ g = sg σ • g

theorem anti_apply {g : TV n M (Fin n)} (hg : IsAnti g) (σ : Equiv.Perm (Fin n)) (I : Fin n → Fin n) :
    g (I ∘ σ) = sg σ • g I := by
  have h := congrFun (hg σ) I
  simpa [pm] using h

theorem anti_zero {g : TV n M (Fin n)} (hg : IsAnti g) {I : Fin n → Fin n} (hI : ¬ Function.Injective I) :
    g I = 0 := by
  simp only [Function.Injective] at hI
  push_neg at hI
  obtain ⟨i, j, hij, hne⟩ := hI
  have hIs : I ∘ Equiv.swap i j = I := by
    funext k
    simp only [Function.comp_apply]
    rcases eq_or_ne k i with rfl | hki
    · simp [Equiv.swap_apply_left, hij]
    rcases eq_or_ne k j with rfl | hkj
    · simp [Equiv.swap_apply_right, hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have h := anti_apply hg (Equiv.swap i j) I
  rw [hIs, sg_swap hne] at h
  have h2 : (2 : ℂ) • g I = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    simp
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem anti_ext {g : TV n M (Fin n)} (hg : IsAnti g) (h0 : g id = 0) : g = 0 := by
  funext I
  by_cases hI : Function.Injective I
  · have hb : Function.Bijective I := Finite.injective_iff_bijective.mp hI
    have h := anti_apply hg (Equiv.ofBijective I hb) id
    have hc : (id ∘ ⇑(Equiv.ofBijective I hb)) = I := by
      funext k
      rfl
    rw [hc, h0, smul_zero] at h
    simpa using h
  · simpa using anti_zero hg hI

theorem alt_anti (f : TV n M (Fin n)) : IsAnti (alt Finset.univ f) := by
  intro σ
  funext I
  have key : ∀ J : Fin n → Fin n, alt Finset.univ f J = ∑ τ : Equiv.Perm (Fin n), sg τ • f (J ∘ ⇑τ) := by
    intro J
    simp [alt, pm, sg]
  have hp : pm σ (alt Finset.univ f) I = alt Finset.univ f (I ∘ σ) := by
    simp [pm]
  rw [hp]
  show alt Finset.univ f (I ∘ σ) = sg σ • alt Finset.univ f I
  rw [key (I ∘ σ), key I, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft σ) _ _ ?_
  intro τ
  have hs : sg σ * sg (σ * τ) = sg τ := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [sg, Equiv.Perm.sign_mul, h]
  simp only [Equiv.coe_mulLeft]
  rw [smul_smul, hs]
  rfl

def X (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (j : Fin n) : Module.End ℂ (TV n M (Fin n)) :=
  algebraMap ℂ _ u + xJ E j

def T (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (j : Fin n) : Module.End ℂ (TV n M (Fin n)) :=
  algebraMap ℂ _ (u - (j : ℂ)) + Om E j

theorem X_eq_T_of_antisymm_below (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (j : Fin n) (w : TV n M (Fin n))
    (hw : ∀ i, i < j → pm (Equiv.swap i j) w = -w) : X E u j w = T E u j w := by
  have hs : (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < j), pm (Equiv.swap i j)) w = -(((j : ℕ) : ℂ) • w) := by
    rw [LinearMap.sum_apply]
    rw [Finset.sum_congr rfl (fun i hi => hw i (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_neg_distrib, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio, Nat.cast_smul_eq_nsmul]
  simp only [X, T, xJ, LinearMap.add_apply]
  rw [hs, Module.algebraMap_end_apply, Module.algebraMap_end_apply, sub_smul]
  abel

theorem T_comm (hT : TensorGl) (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) (u : ℂ) (σ : Equiv.Perm (Fin n))
    (j : Fin n) (hj : σ j = j) : Commute (pm σ) (T E u j) := by
  refine Commute.add_right (Algebra.commutes _ _).symm ?_
  have := (hT n M (Fin n) E hE ∅).2.2.2 σ j
  rw [hj] at this
  exact this

theorem step1 (hT : TensorGl) (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) (u : ℂ) (g : TV n M (Fin n))
    (hg : IsAnti g) (l : List (Fin n)) (hl : l.Pairwise (· < ·)) :
    (l.map (X E u)).prod g = (l.map (T E u)).prod g := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    rw [List.pairwise_cons] at hl
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [ih hl.2]
    apply X_eq_T_of_antisymm_below
    intro i hi
    have hc : Commute (pm (Equiv.swap i k)) (l.map (T E u)).prod := by
      apply Commute.list_prod_right
      intro b hb
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
      have hkj := hl.1 j hj
      apply T_comm hT E hE u
      apply Equiv.swap_apply_of_ne_of_ne
      · exact ne_of_gt (lt_trans hi hkj)
      · exact ne_of_gt hkj
    rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply]
    rw [hg (Equiv.swap i k), sg_swap (ne_of_lt hi)]
    simp

def ev (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) : List (Fin n) → (Fin n → Fin n) → TV n M (Fin n) → M
  | [], I, h => h I
  | k :: l, I, h => ∑ a, Tm E (u - (k : ℂ)) a (I k) (ev E u l (Function.update I k a) h)

theorem T_apply (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (k : Fin n) (h : TV n M (Fin n)) (I : Fin n → Fin n) :
    T E u k h I = ∑ a, Tm E (u - (k : ℂ)) a (I k) (h (Function.update I k a)) := by
  simp [T, Om, lift, eAt, Tm, Finset.sum_add_distrib, LinearMap.add_apply]
  congr 1
  · rw [Finset.sum_eq_single (I k)]
    · simp [sub_smul]
    · intro b _ hb
      simp [hb]
    · simp
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (I k)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp

theorem evA (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (h : TV n M (Fin n)) (l : List (Fin n)) (I : Fin n → Fin n) :
    (l.map (T E u)).prod h I = ev E u l I h := by
  induction l generalizing I with
  | nil => rfl
  | cons k l ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ev, T_apply, ih]

theorem evB (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (h : TV n M (Fin n)) (l : List (Fin n)) (hl : l.Nodup)
    (I : Fin n → Fin n) :
    ev E u l I h = ∑ c ∈ Finset.univ.filter (fun c : Fin n → Fin n => ∀ p, p ∉ l → c p = I p),
      (l.map fun k : Fin n => Tm E (u - (k : ℂ)) (c k) (I k)).prod (h c) := by
  induction l generalizing I with
  | nil =>
    rw [Finset.sum_eq_single I]
    · simp [ev]
    · intro c hc hne
      exfalso
      apply hne
      funext p
      exact (Finset.mem_filter.mp hc).2 p (by simp)
    · intro hI
      exfalso
      apply hI
      simp
  | cons k l ih =>
    have hk : k ∉ l := (List.nodup_cons.mp hl).1
    have hl' := (List.nodup_cons.mp hl).2
    simp only [ev, ih hl']
    conv_rhs => rw [← Finset.sum_fiberwise _ (fun c : Fin n → Fin n => c k)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr ?_ fun c hc => ?_
    · ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons, not_or]
      constructor
      · intro H
        refine ⟨fun p hp => ?_, ?_⟩
        · rw [H p hp.2, Function.update_of_ne hp.1]
        · rw [H k hk, Function.update_self]
      · rintro ⟨H, hca⟩ p hp
        by_cases hpk : p = k
        · subst hpk
          rw [hca, Function.update_self]
        · rw [H p ⟨hpk, hp⟩, Function.update_of_ne hpk]
    · simp only [Finset.mem_filter] at hc
      have hca : c k = a := hc.2
      have hm : l.map (fun k' : Fin n => Tm E (u - (k' : ℂ)) (c k') (Function.update I k a k'))
          = l.map (fun k' : Fin n => Tm E (u - (k' : ℂ)) (c k') (I k')) := by
        apply List.map_congr_left
        intro x hx
        have hxk : x ≠ k := by
          rintro rfl
          exact hk hx
        rw [Function.update_of_ne hxk]
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, hca, hm]

theorem evQ (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (g : TV n M (Fin n)) (hg : IsAnti g) :
    ev E u (List.finRange n) id g = qdet E u (g id) := by
  rw [evB E u g _ (List.nodup_finRange n) id]
  have hfilt : Finset.univ.filter (fun c : Fin n → Fin n => ∀ p, p ∉ List.finRange n → c p = id p) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro c _ p hp
    exact absurd (List.mem_finRange p) hp
  rw [hfilt]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨fun σ : Equiv.Perm (Fin n) => ⇑σ, DFunLike.coe_injective⟩)), Finset.sum_map]
  · simp only [qdet, qminor, LinearMap.sum_apply, Function.Embedding.coeFn_mk]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have ha := anti_apply hg σ id
    simp only [Function.id_comp] at ha
    rw [ha, map_smul, Module.End.mul_apply, Module.End.intCast_apply, List.ofFn_eq_map, sg, Int.cast_smul_eq_zsmul]
    rfl
  · intro c _ hc
    have hnc : ¬ Function.Injective c := by
      intro hinj
      apply hc
      rw [Finset.mem_map]
      exact ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩
    rw [anti_zero hg hnc, map_zero]

end QuantumDeterminantProducts

open QuantumDeterminantProducts in
theorem piQdet_of : TensorGl → JMComm → PiQdet := by
  intro hT hJ n M _ _ E hE u
  apply LinearMap.ext
  intro f
  set g := alt Finset.univ f with hgdef
  have hg : IsAnti g := alt_anti f
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have hPX : PiJ n E u = ((List.finRange n).map (X E u)).prod := by
    unfold PiJ
    rw [List.ofFn_eq_map]
    rfl
  have hA : IsAnti (PiJ n E u g) := by
    intro σ
    have hc := ((hJ n M E hE n).2.2 u σ).eq
    calc pm σ (PiJ n E u g) = ((pm σ * PiJ n E u : Module.End ℂ (TV n M (Fin n))) g) := rfl
      _ = ((PiJ n E u * pm σ : Module.End ℂ (TV n M (Fin n))) g) := by rw [hc]
      _ = PiJ n E u (pm σ g) := rfl
      _ = sg σ • PiJ n E u g := by rw [hg σ, map_smul]
  have hB : IsAnti (lift (qdet E u) g) := by
    intro σ
    have hl : pm σ (lift (qdet E u) g) = lift (qdet E u) (pm σ g) := by
      funext I
      simp [pm, lift]
    rw [hl, hg σ, map_smul]
  have hD : IsAnti (PiJ n E u g - lift (qdet E u) g) := by
    intro σ
    rw [map_sub, hA σ, hB σ, smul_sub]
  have h0 : (PiJ n E u g - lift (qdet E u) g) id = 0 := by
    rw [Pi.sub_apply, hPX, step1 hT E hE u g hg _ (List.pairwise_lt_finRange n), evA, evQ E u g hg]
    simp [lift]
  exact sub_eq_zero.mp (anti_ext hD h0)

end PositivityTheory.Rg.Cz

end
end

section
noncomputable section

open Polynomial Formalism.REAL

namespace PositivityTheory.Rg.Cz

namespace QF

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem qdet_eq_capelliC {n : ℕ} (E : Fin n → Fin n → A) (x : ℂ) : qdet E x = capelliC E x := by
  simp only [qdet, capelliC, cminor, qminor, Tm, capEntry, id]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [zsmul_eq_mul]
  congr 3
  funext k
  rw [add_comm]

theorem capelliC_negT {n : ℕ} (E : Fin n → Fin n → A) (x : ℂ) :
    capelliC (fun a b => -E b a) x = (-1) ^ n * rminor E id id ((n : ℂ) - 1 - x) := by
  simp only [capelliC, cminor, rminor, id]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h : (List.ofFn fun j : Fin n => capEntry (fun a b => -E b a) (x - ((j : ℕ) : ℂ)) (σ j) j) =
      (List.ofFn fun j : Fin n => capEntry E ((n : ℂ) - 1 - x - (n : ℂ) + 1 + ((j : ℕ) : ℂ)) j (σ j)).map Neg.neg := by
    rw [List.map_ofFn]
    congr 1
    funext j
    simp only [Function.comp, capEntry]
    by_cases hj : σ j = j
    · rw [if_pos hj, if_pos hj.symm, neg_add, ← map_neg]
      congr 2
      ring
    · rw [if_neg hj, if_neg (Ne.symm hj), neg_add, neg_zero]
  rw [h, List.prod_map_neg, List.length_ofFn, zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← mul_assoc,
    ((Commute.neg_one_left _).pow_left n).eq]

theorem qdet_negT {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (u : ℂ) :
    qdet (fun a b => -E b a) u = (-1) ^ n * qdet E ((n : ℂ) - 1 - u) := by
  rw [qdet_eq_capelliC, capelliC_negT, qdet_eq_capelliC, capelliC, cminor_eq_rminor E hE]

def tmPoly {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) : A[X] :=
  (if a = b then X - C (algebraMap ℂ A (k : ℂ)) else 0) + C (E a b)

def qdetPoly {n : ℕ} (E : Fin n → Fin n → A) : A[X] :=
  ∑ σ : Equiv.Perm (Fin n), C ((Equiv.Perm.sign σ : ℤ) : A) *
    (List.ofFn fun k : Fin n => tmPoly E k (σ k) k).prod

def evU (u : ℂ) : A[X] →+* A :=
  eval₂RingHom' (RingHom.id A) (algebraMap ℂ A u) (fun a => (Algebra.commutes u a).symm)

theorem evU_apply (u : ℂ) (p : A[X]) : evU u p = eval₂ (RingHom.id A) (algebraMap ℂ A u) p := rfl

theorem evU_tmPoly {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) (k : ℕ) (a b : Fin n) :
    evU u (tmPoly E k a b) = Tm E (u - (k : ℂ)) a b := by
  rw [evU_apply, tmPoly, Tm]
  split_ifs <;> simp [eval₂_add, eval₂_sub, map_sub]

theorem evU_qdetPoly {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) : evU u (qdetPoly E) = qdet E u := by
  simp only [qdetPoly, qdet, qminor, id, map_sum, map_mul, map_list_prod, List.map_ofFn, Function.comp_def,
    evU_tmPoly]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [evU_apply, eval₂_C]
  rfl

theorem natDegree_tmPoly_le {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) :
    (tmPoly E k a b).natDegree ≤ if a = b then 1 else 0 := by
  rw [tmPoly]
  split_ifs with h
  · exact (natDegree_add_le _ _).trans (max_le (natDegree_X_sub_C_le _) (by rw [natDegree_C]; exact zero_le_one))
  · rw [zero_add, natDegree_C]

theorem natDegree_prod_le {n : ℕ} (E : Fin n → Fin n → A) (σ : Equiv.Perm (Fin n)) :
    (List.ofFn fun k : Fin n => tmPoly E k (σ k) k).prod.natDegree ≤
      ∑ k : Fin n, if σ k = k then 1 else 0 := by
  refine (natDegree_list_prod_le _).trans ?_
  rw [List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_le_sum fun k _ => natDegree_tmPoly_le E k (σ k) k

theorem fixed_add_support {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (∑ k : Fin n, if σ k = k then 1 else 0) + σ.support.card = n := by
  rw [Finset.sum_boole, Nat.cast_id]
  have hs : σ.support = Finset.univ.filter (fun k => ¬ σ k = k) := by
    ext k
    simp [Equiv.Perm.mem_support]
  rw [hs, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]

theorem natDegree_prod_ne_one {n : ℕ} (E : Fin n → Fin n → A) {σ : Equiv.Perm (Fin n)} (hσ : σ ≠ 1) :
    (List.ofFn fun k : Fin n => tmPoly E k (σ k) k).prod.natDegree + 2 ≤ n := by
  have h1 := natDegree_prod_le E σ
  have h2 := fixed_add_support σ
  have h3 := Equiv.Perm.two_le_card_support_of_ne_one hσ
  omega

omit [Algebra ℂ A] in
theorem prod_linear (m : ℕ) (c : Fin m → A) :
    (List.ofFn fun k : Fin m => X + C (c k)).prod.natDegree ≤ m ∧
      (List.ofFn fun k : Fin m => X + C (c k)).prod.coeff m = 1 ∧
      ∀ j, j + 1 = m → (List.ofFn fun k : Fin m => X + C (c k)).prod.coeff j = ∑ k, c k := by
  induction m with
  | zero =>
    refine ⟨by simp, by simp, fun j hj => by omega⟩
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun k => c k.castSucc)
    have e : (List.ofFn fun k : Fin (m + 1) => X + C (c k)).prod =
        (List.ofFn fun k : Fin m => X + C (c k.castSucc)).prod * (X + C (c (Fin.last m))) := by
      rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
    rw [e]
    have hP : (List.ofFn fun k : Fin m => X + C (c k.castSucc)).prod.coeff (m + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    refine ⟨?_, ?_, ?_⟩
    · refine natDegree_mul_le.trans (add_le_add h1 ?_)
      exact (natDegree_add_le _ _).trans (max_le natDegree_X_le (by rw [natDegree_C]; exact zero_le_one))
    · rw [mul_add, coeff_add, coeff_mul_C, coeff_mul_X, h2, hP, zero_mul, add_zero]
    · intro j hj
      obtain rfl : j = m := by omega
      rw [Fin.sum_univ_castSucc, mul_add, coeff_add, coeff_mul_C, h2, one_mul]
      congr 1
      rcases j with _ | j
      · simp
      · rw [coeff_mul_X]
        exact h3 j rfl

theorem tmPoly_diag {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a : Fin n) :
    tmPoly E k a a = X + C (E a a - algebraMap ℂ A (k : ℂ)) := by
  rw [tmPoly, if_pos rfl, C_sub]
  abel

theorem sum_fin_cast (n : ℕ) : ∑ k : Fin n, ((k : ℕ) : ℂ) = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (i : ℂ)) n]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem natDegree_qdetPoly_le {n : ℕ} (E : Fin n → Fin n → A) : (qdetPoly E).natDegree ≤ n := by
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le E σ).trans ?_)
  have := fixed_add_support σ
  omega

theorem coeff_qdetPoly_top {n : ℕ} (E : Fin n → Fin n → A) (j : ℕ) (hj : n ≤ j + 1) :
    (qdetPoly E).coeff j = (List.ofFn fun k : Fin n => X + C (E k k - algebraMap ℂ A ((k : ℕ) : ℂ))).prod.coeff j := by
  rw [qdetPoly, finset_sum_coeff, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, C_1, one_mul, Equiv.Perm.one_apply, tmPoly_diag]
  · intro σ _ hσ
    rw [coeff_C_mul]
    have := natDegree_prod_ne_one E hσ
    rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Alg

section Op

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem coeff_eq_zero_of_evU (r : (Module.End ℂ M)[X]) (h : ∀ u : ℂ, evU u r = 0) (i : ℕ) : r.coeff i = 0 := by
  by_cases hi : i ∈ r.support
  swap
  · exact notMem_support_iff.mp hi
  ext m
  rw [LinearMap.zero_apply]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun φ => ?_
  have hq0 : (∑ e ∈ r.support, monomial e (φ (r.coeff e m))) = 0 := by
    refine Polynomial.funext fun u => ?_
    rw [eval_zero, eval_finset_sum]
    have hu := congrArg (fun T : Module.End ℂ M => φ (T m)) (h u)
    simp only [evU_apply, eval₂_eq_sum, Polynomial.sum_def, LinearMap.zero_apply, map_zero, RingHom.id_apply,
      LinearMap.sum_apply, Module.End.mul_apply, ← map_pow, Module.algebraMap_end_apply,
      map_smul, map_sum, smul_eq_mul] at hu
    rw [← hu]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [eval_monomial, mul_comm]
  have hc := congrArg (fun p : ℂ[X] => p.coeff i) hq0
  simp only [finset_sum_coeff, coeff_monomial, coeff_zero, Finset.sum_ite_eq', if_pos hi] at hc
  exact hc

end Op

end QF

open QF ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

theorem qdetFacts_holds : QdetFacts := by
  intro n M _ _ E hE
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u a b
    rw [qdet_eq_capelliC]
    exact (capelliC_central E hE u a b).symm
  · refine ⟨fun i => (qdetPoly E).coeff i, fun u => ?_⟩
    rw [← evU_qdetPoly, evU_apply, eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_qdetPoly_le E))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RingHom.id_apply, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
  · intro l hl
    have key : ∀ i, (qdetPoly E).coeff i =
        algebraMap ℂ (Module.End ℂ M) ((∏ k : Fin n, (X + C (l k))).coeff i) := by
      intro i
      rw [← coeff_map, ← sub_eq_zero, ← coeff_sub]
      refine coeff_eq_zero_of_evU _ (fun u => ?_) i
      rw [map_sub, evU_qdetPoly, hl u, evU_apply, eval₂_map, RingHom.id_comp, eval₂_at_apply, eval_prod]
      simp only [eval_add, eval_X, eval_C, sub_self]
    cases n with
    | zero => simp
    | succ m =>
      have h1 := key m
      have h2 := (prod_linear (m + 1) fun k => E k k - algebraMap ℂ (Module.End ℂ M) ((k : ℕ) : ℂ)).2.2 m rfl
      have h3 := (prod_linear (m + 1) l).2.2 m rfl
      rw [List.prod_ofFn] at h3
      rw [coeff_qdetPoly_top E m le_rfl, h2, h3, Finset.sum_sub_distrib, sub_eq_iff_eq_add, ← map_sum] at h1
      rw [h1, ← map_add, sum_fin_cast]
  · unfold GlRel
    intro a b c d
    have h := hE d c b a
    simp only [@eq_comm _ c b, @eq_comm _ a d] at h
    simp only [neg_mul_neg]
    rw [← neg_sub, h]
    split_ifs <;> abel
  · intro l hl u
    rw [qdet_negT E hE, hl]
    have hp : ∏ k : Fin n, (u + (-((n : ℂ) - 1) - l k)) = (-1) ^ n * ∏ k : Fin n, ((n : ℂ) - 1 - u + l k) := by
      rw [show (-1 : ℂ) ^ n = ∏ _k : Fin n, (-1 : ℂ) by simp, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by ring
    rw [hp, map_mul, map_pow, map_neg, map_one]

end PositivityTheory.Rg.Cz

end
end

section
noncomputable section

open Formalism.REAL

namespace PositivityTheory.Rg.Cz

namespace WQ

section Alg

variable {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]

theorem qdet_map (f : A →ₐ[ℂ] B) {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) :
    f (qdet E u) = qdet (fun a b => f (E a b)) u := by
  unfold qdet qminor
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
  simp only [Function.comp, Tm, map_add, apply_ite f, map_zero, AlgHom.commutes]

theorem glRel_map (f : A →ₐ[ℂ] B) {n : ℕ} {E : Fin n → Fin n → A} (h : GlRel E) : GlRel fun a b => f (E a b) := by
  intro a b c d
  have := congrArg f (h a b c d)
  simpa [map_sub, map_mul, apply_ite f] using this

theorem glRel_of_inj (f : A →ₐ[ℂ] B) (hf : Function.Injective f) {n : ℕ} {E : Fin n → Fin n → A}
    (h : GlRel fun a b => f (E a b)) : GlRel E := by
  intro a b c d
  apply hf
  simpa [map_sub, map_mul, apply_ite f] using h a b c d

theorem comm_qdet {n : ℕ} (E : Fin n → Fin n → A) (x : A) (h : ∀ a b, Commute x (E a b)) (u : ℂ) :
    Commute x (qdet E u) := by
  unfold qdet qminor
  refine Commute.sum_right _ _ _ fun σ _ => ?_
  refine Commute.mul_right (Int.cast_commute _ _).symm ?_
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
  unfold Tm
  refine Commute.add_right ?_ (h _ _)
  split_ifs
  · exact Algebra.commute_algebraMap_right _ _
  · exact Commute.zero_right _

end Alg

section Quot

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def stab (N : Submodule ℂ M) : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {X | ∀ y ∈ N, X y ∈ N}
  mul_mem' hX hY y hy := hX _ (hY y hy)
  add_mem' hX hY y hy := N.add_mem (hX y hy) (hY y hy)
  algebraMap_mem' c y hy := by simpa [Module.algebraMap_end_apply] using N.smul_mem c hy

def qmap (N : Submodule ℂ M) : stab N →ₐ[ℂ] Module.End ℂ (M ⧸ N) where
  toFun X := N.mapQ N X.1 (fun y hy => X.2 y hy)
  map_one' := by ext y; simp
  map_mul' X Y := by ext y; simp
  map_zero' := by ext y; simp
  map_add' X Y := by ext y; simp
  commutes' c := by ext y; simp [Module.algebraMap_end_apply]

end Quot

end WQ

open WQ

theorem wallQuot_of (hQ : QdetFacts) : WallQuot := by
  intro n M _ _ ι E hgl hcomm l φ hφ
  let N : Submodule ℂ M :=
    { carrier := {y | ∀ w ∈ envAlg E, φ (w y) = 0}
      add_mem' := fun {x y} hx hy w hw => by
        show φ (w (x + y)) = 0
        rw [map_add, map_add, hx w hw, hy w hw, add_zero]
      zero_mem' := fun w _ => by simp
      smul_mem' := fun c y hy w hw => by
        show φ (w (c • y)) = 0
        rw [map_smul, map_smul, hy w hw, smul_zero] }
  have hgen : ∀ τ a b, E τ a b ∈ envAlg E := fun τ a b => Algebra.subset_adjoin ⟨τ, a, b, rfl⟩
  have hstab : ∀ τ a b, E τ a b ∈ stab N := fun τ a b y hy w hw =>
    hy (w * E τ a b) (Subalgebra.mul_mem _ hw (hgen τ a b))
  let E' : ι → Fin n → Fin n → stab N := fun τ a b => ⟨E τ a b, hstab τ a b⟩
  let F : ι → Fin n → Fin n → Module.End ℂ (M ⧸ N) := fun τ a b => qmap N (E' τ a b)
  have hgl' : ∀ τ, GlRel (E' τ) := fun τ => glRel_of_inj (stab N).val Subtype.val_injective (hgl τ)
  have hcent : ∀ τ (u : ℂ), ∀ w ∈ envAlg E, Commute w (qdet (E τ) u) := by
    intro τ u w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨τ', a, b, rfl⟩ := hx
      by_cases h : τ' = τ
      · subst h
        exact ((hQ n M (E τ') (hgl τ')).1 u a b).symm
      · exact comm_qdet _ _ (fun c d => hcomm τ' τ h a b c d) u
    | algebraMap c => exact Algebra.commute_algebraMap_left _ _
    | add x y _ _ hx hy => exact hx.add_left hy
    | mul x y _ _ hx hy => exact hx.mul_left hy
  have hq : ∀ τ (u : ℂ) y, qdet (F τ) u (N.mkQ y) = N.mkQ (qdet (E τ) u y) := by
    intro τ u y
    rw [show qdet (F τ) u = qmap N (qdet (E' τ) u) from (qdet_map _ _ _).symm,
      show qdet (E τ) u = (stab N).val (qdet (E' τ) u) from (qdet_map (stab N).val (E' τ) u).symm]
    rfl
  refine ⟨N, F, fun τ => glRel_map (qmap N) (hgl' τ), fun τ τ' h a b c d => ?_, fun τ u => ?_,
    fun τ a b => LinearMap.ext fun y => rfl, fun y => Iff.rfl⟩
  · exact (show Commute (E' τ a b) (E' τ' c d) from Subtype.ext (hcomm τ τ' h a b c d).eq).map (qmap N)
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hq, Module.algebraMap_end_apply, ← N.mkQ.map_smul,
      Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    intro w hw
    show φ (w (qdet (E τ) u y - (∏ k, (u + l τ k)) • y)) = 0
    have hc := congrArg (fun T : Module.End ℂ M => φ (T y)) (hcent τ u w hw).eq
    simp only [Module.End.mul_apply] at hc
    have h2 := LinearMap.congr_fun (hφ τ u) (w y)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h2
    rw [map_sub, map_sub, map_smul, map_smul, hc, h2, sub_self]

end PositivityTheory.Rg.Cz

end
end

section
noncomputable section

open Formalism.REAL Polynomial

namespace PositivityTheory.Rg.Cz

namespace CharacterRelations

section poly

variable {A : Type*} [Ring A] [Algebra ℂ A]

set_option linter.unusedSectionVars false

theorem comm_alg (y : A) (u : ℂ) : Commute y (algebraMap ℂ A u) := (Algebra.commutes u y).symm

theorem eval_mul_nc (p q : A[X]) (x : A) (h : ∀ k, Commute (q.coeff k) x) :
    (p * q).eval x = p.eval x * q.eval x := by
  exact Polynomial.eval₂_mul_noncomm (RingHom.id A) x h

theorem eval_sumMono (d : ℕ → A) (N : ℕ) (u : ℂ) :
    (∑ i ∈ Finset.range N, monomial i (d i)).eval (algebraMap ℂ A u) = ∑ i ∈ Finset.range N, u ^ i • d i := by
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_monomial, ← map_pow, Algebra.smul_def,
    Algebra.commutes]

theorem vanish (D : A[X]) (a : ℂ) (h : ∀ u : ℂ, u ≠ a → D.eval (algebraMap ℂ A u) = 0) : D = 0 := by
  ext i
  rw [Polynomial.coeff_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (D.coeff i)).1 (fun φ => ?_)
  let q : ℂ[X] := ∑ j ∈ Finset.range (D.natDegree + 1), monomial j (φ (D.coeff j))
  have hq : ∀ u : ℂ, u ≠ a → q.eval u = 0 := by
    intro u hu
    have e := congrArg φ (h u hu)
    rw [Polynomial.eval_eq_sum_range, map_zero, map_sum] at e
    simp only [q, Polynomial.eval_finset_sum, Polynomial.eval_monomial]
    rw [← e]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have q0 : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := {a}ᶜ) (fun u hu => hq u hu) ?_
    exact (Set.finite_singleton a).infinite_compl
  by_cases hi : i < D.natDegree + 1
  · have e := congrArg (fun p => p.coeff i) q0
    simpa [q, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, hi] using e
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

theorem prod_neg_zero (L : List A) (h : (L.map fun x => -x).prod = 0) : L.prod = 0 := by
  rw [List.prod_map_neg] at h
  have hu : IsUnit ((-1 : A) ^ L.length) := (isUnit_one.neg).pow _
  exact hu.mul_right_eq_zero.1 h

end poly

section rel

variable {V N : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup N] [Module ℂ N]
  (W : Submodule ℂ V) (q : W →ₗ[ℂ] N)

def Rel (X : Module.End ℂ V) (Y : Module.End ℂ N) : Prop := ∀ w : W, ∃ h : X w ∈ W, q ⟨X w, h⟩ = Y (q w)

variable {W q}

theorem rel_add {X X' Y Y'} (h : Rel W q X Y) (h' : Rel W q X' Y') : Rel W q (X + X') (Y + Y') := by
  intro w
  obtain ⟨h1, e1⟩ := h w
  obtain ⟨h2, e2⟩ := h' w
  refine ⟨W.add_mem h1 h2, ?_⟩
  show q (⟨X w, h1⟩ + ⟨X' w, h2⟩) = Y (q w) + Y' (q w)
  rw [map_add, e1, e2]

theorem rel_sub {X X' Y Y'} (h : Rel W q X Y) (h' : Rel W q X' Y') : Rel W q (X - X') (Y - Y') := by
  intro w
  obtain ⟨h1, e1⟩ := h w
  obtain ⟨h2, e2⟩ := h' w
  refine ⟨W.sub_mem h1 h2, ?_⟩
  show q (⟨X w, h1⟩ - ⟨X' w, h2⟩) = Y (q w) - Y' (q w)
  rw [map_sub, e1, e2]

theorem rel_mul {X X' Y Y'} (h : Rel W q X Y) (h' : Rel W q X' Y') : Rel W q (X * X') (Y * Y') := by
  intro w
  obtain ⟨h2, e2⟩ := h' w
  obtain ⟨h1, e1⟩ := h ⟨X' w, h2⟩
  exact ⟨h1, e1.trans (congrArg Y e2)⟩

theorem rel_alg (c : ℂ) : Rel W q (algebraMap ℂ _ c) (algebraMap ℂ _ c) := by
  intro w
  refine ⟨by rw [Module.algebraMap_end_apply]; exact W.smul_mem c w.2, ?_⟩
  have e : (⟨algebraMap ℂ (Module.End ℂ V) c w, by rw [Module.algebraMap_end_apply]; exact W.smul_mem c w.2⟩ : W) = c • w :=
    Subtype.ext (by simp [Module.algebraMap_end_apply])
  rw [e, map_smul, Module.algebraMap_end_apply]

theorem rel_zero : Rel W q 0 0 := by
  simpa using rel_alg (W := W) (q := q) 0

theorem rel_intCast (z : ℤ) : Rel W q (z : Module.End ℂ V) (z : Module.End ℂ N) := by
  simpa [map_intCast] using rel_alg (W := W) (q := q) (z : ℂ)

theorem rel_sum {ι : Type*} (s : Finset ι) (X : ι → Module.End ℂ V) (Y : ι → Module.End ℂ N)
    (h : ∀ i, Rel W q (X i) (Y i)) : Rel W q (∑ i ∈ s, X i) (∑ i ∈ s, Y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rel_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha]; exact rel_add (h a) ih

theorem rel_prod {t : ℕ} (X : Fin t → Module.End ℂ V) (Y : Fin t → Module.End ℂ N)
    (h : ∀ i, Rel W q (X i) (Y i)) : Rel W q (List.ofFn X).prod (List.ofFn Y).prod := by
  induction t with
  | zero => simpa using rel_alg (W := W) (q := q) 1
  | succ t ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact rel_mul (h 0) (ih _ _ fun i => h i.succ)

theorem rel_uniq (hq : Function.Surjective q) {X Y Y'} (h : Rel W q X Y) (h' : Rel W q X Y') : Y = Y' := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨w, rfl⟩ := hq y
  obtain ⟨h1, e1⟩ := h w
  obtain ⟨h2, e2⟩ := h' w
  rw [← e1, ← e2]

variable {n : ℕ}

theorem rel_qdet (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ N)
    (h : ∀ a b, Rel W q (E a b) (F a b)) (u : ℂ) : Rel W q (qdet E u) (qdet F u) := by
  simp only [qdet, qminor]
  refine rel_sum _ _ _ fun σ => rel_mul (rel_intCast _) (rel_prod _ _ fun k => ?_)
  unfold Tm
  refine rel_add ?_ (h _ _)
  split_ifs
  · exact rel_alg _
  · exact rel_zero

theorem rel_gl (hq : Function.Surjective q) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ N)
    (hE : GlRel E) (h : ∀ a b, Rel W q (E a b) (F a b)) : GlRel F := by
  intro a b c d
  have h1 := rel_sub (rel_mul (h a b) (h c d)) (rel_mul (h c d) (h a b))
  rw [hE a b c d] at h1
  have h2 : Rel W q ((if b = c then E a d else 0) - if d = a then E c b else 0)
      ((if b = c then F a d else 0) - if d = a then F c b else 0) := by
    refine rel_sub ?_ ?_
    · split_ifs
      · exact h _ _
      · exact rel_zero
    · split_ifs
      · exact h _ _
      · exact rel_zero
  exact rel_uniq hq h1 h2

end rel

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem piJ_one (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) :
    PiJ 1 E u = algebraMap ℂ _ u + Om E (0 : Fin 1) := by
  simp [PiJ, xJ]

theorem lift_alg {P : Type} (c : ℂ) :
    (lift (algebraMap ℂ (Module.End ℂ M) c) : Module.End ℂ (TV n M P)) = algebraMap ℂ _ c := by
  ext f I
  simp [lift, Module.algebraMap_end_apply]

theorem qdet_comm {A : Type*} [Ring A] [Algebra ℂ A] (T : A) (E : Fin n → Fin n → A)
    (h : ∀ a b, Commute T (E a b)) (u : ℂ) : Commute T (qdet E u) := by
  simp only [qdet, qminor]
  refine Commute.sum_right _ _ _ fun σ _ => ?_
  refine Commute.mul_right Commute.intCast_right (Commute.list_prod_right _ _ ?_)
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨k, rfl⟩ := hx
  unfold Tm
  refine Commute.add_right ?_ (h _ _)
  split_ifs
  · exact comm_alg _ _
  · exact Commute.zero_right _

theorem part1 (hT : TensorGl) (hS : StepFormula) (hQ : QdetFacts) (E : Fin n → Fin n → Module.End ℂ M)
    (hE : GlRel E) (l : Fin n → ℂ) (hl : HasChar E l) :
    (List.ofFn fun k => Om E (0 : Fin 1) - algebraMap ℂ _ (l k)).prod = 0 := by
  classical
  have hG := hT n M (Fin 1) E hE Finset.univ
  obtain ⟨c, hc⟩ := (hQ n (TV n M (Fin 1)) (tE Finset.univ E) hG.1).2.1
  have hcomm : ∀ u, Commute (Om E (0 : Fin 1)) (qdet (tE Finset.univ E) u) := fun u =>
    qdet_comm _ _ (fun a b => hG.2.1 0 (Finset.mem_univ _) a b) u
  have hid : ∀ u : ℂ, qdet (tE Finset.univ E) u * (algebraMap ℂ (Module.End ℂ (TV n M (Fin 1))) u + Om E 0) =
      algebraMap ℂ _ (∏ k, (u + l k)) * (algebraMap ℂ _ u + (1 + Om E 0)) := by
    intro u
    have e := hS n M E hE 1 u
    rw [piJ_one, piJ_one, hl u, lift_alg] at e
    rw [← ((comm_alg _ u).symm.add_left (hcomm u)).eq, e, map_add, map_one, add_assoc]
  have hP : (∑ i ∈ Finset.range (n + 1), monomial i (c i)) * (X + C (Om E (0 : Fin 1))) -
      (∏ k, (X + C (l k))).map (algebraMap ℂ (Module.End ℂ (TV n M (Fin 1)))) * (X + C (1 + Om E 0)) = 0 := by
    apply vanish _ 0
    intro u _
    rw [Polynomial.eval_sub, eval_mul_nc _ _ _ (fun k => comm_alg _ _), eval_mul_nc _ _ _ (fun k => comm_alg _ _),
      eval_sumMono, ← hc, Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval_prod]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    rw [hid, sub_self]
  have hc' : ∀ a : Module.End ℂ (TV n M (Fin 1)), Commute a (Om E 0) →
      ∀ k, Commute ((X + C a).coeff k) (-Om E (0 : Fin 1)) := by
    intro a ha k
    rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
    refine Commute.add_left ?_ ?_ <;> split_ifs <;> simp [ha.neg_right]
  have e := congrArg (Polynomial.eval (-Om E (0 : Fin 1))) hP
  rw [Polynomial.eval_sub, eval_mul_nc _ _ _ (hc' _ (Commute.refl _)),
    eval_mul_nc _ _ _ (hc' _ ((Commute.one_left _).add_left (Commute.refl _))), Polynomial.eval_zero] at e
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at e
  rw [neg_add_cancel, mul_zero, zero_sub, show -Om E (0 : Fin 1) + (1 + Om E 0) = 1 by abel, mul_one,
    neg_eq_zero, Polynomial.eval_map, ← Polynomial.aeval_def, ← List.prod_ofFn, map_list_prod,
    List.map_ofFn] at e
  apply prod_neg_zero
  rw [List.map_ofFn]
  refine Eq.trans (congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))) e
  simp only [Function.comp_apply, map_add, Polynomial.aeval_X, Polynomial.aeval_C, neg_sub]
  abel

theorem part2 (hT : TensorGl) (hS : StepFormula) (hQ : QdetFacts) (E : Fin n → Fin n → Module.End ℂ M)
    (hE : GlRel E) (l : Fin n → ℂ) (hl : HasChar E l)
    (W : Submodule ℂ (TV n M (Fin 1))) (N : Type) [AddCommGroup N] [Module ℂ N] (F : Fin n → Fin n → Module.End ℂ N)
    (q : W →ₗ[ℂ] N) (hW : ∀ a b, ∀ w ∈ W, tE Finset.univ E a b w ∈ W) (hO : ∀ w ∈ W, Om E 0 w ∈ W) (k : Fin n)
    (hq : Function.Surjective q) (hqF : ∀ a b (w : W), q ⟨_, hW a b w w.2⟩ = F a b (q w))
    (hqO : ∀ w : W, q ⟨_, hO w w.2⟩ = l k • q w) : HasChar F (Function.update l k (l k + 1)) := by
  classical
  have hG := hT n M (Fin 1) E hE Finset.univ
  have hrelT : ∀ a b, Rel W q (tE Finset.univ E a b) (F a b) := fun a b w => ⟨hW a b w w.2, hqF a b w⟩
  have hrelO : Rel W q (Om E 0) (algebraMap ℂ (Module.End ℂ N) (l k)) := fun w =>
    ⟨hO w w.2, by rw [Module.algebraMap_end_apply]; exact hqO w⟩
  have hFG : GlRel F := rel_gl hq _ F hG.1 hrelT
  obtain ⟨c, hc⟩ := (hQ n N F hFG).2.1
  have key : ∀ u : ℂ, u ≠ -l k →
      qdet F u = algebraMap ℂ _ (∏ j, (u + Function.update l k (l k + 1) j)) := by
    intro u hu
    have hu' : u + l k ≠ 0 := fun h0 => hu (eq_neg_of_add_eq_zero_left h0)
    have hL := rel_mul (rel_add (rel_alg (W := W) (q := q) u) hrelO) (rel_qdet _ _ hrelT u)
    have e := hS n M E hE 1 u
    rw [piJ_one, piJ_one, hl u, lift_alg] at e
    rw [e] at hL
    have hR := rel_mul (rel_alg (W := W) (q := q) (∏ j, (u + l j)))
      (rel_add (rel_alg (W := W) (q := q) (u + 1)) hrelO)
    have h3 := rel_uniq hq hL hR
    rw [← map_add (algebraMap ℂ (Module.End ℂ N)), ← map_add (algebraMap ℂ (Module.End ℂ N)),
      ← map_mul (algebraMap ℂ (Module.End ℂ N))] at h3
    have hs : (∏ j, (u + l j)) * (u + 1 + l k) = (u + l k) * ∏ j, (u + Function.update l k (l k + 1) j) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
        Function.update_self]
      have hj : ∀ j ∈ Finset.univ.erase k, u + Function.update l k (l k + 1) j = u + l j := fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [Finset.prod_congr rfl hj]
      ring
    rw [hs, map_mul] at h3
    calc qdet F u = algebraMap ℂ (Module.End ℂ N) (u + l k)⁻¹ * (algebraMap ℂ _ (u + l k) * qdet F u) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hu', map_one, one_mul]
      _ = _ := by rw [h3, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hu', map_one, one_mul]
  have hD := vanish ((∑ i ∈ Finset.range (n + 1), monomial i (c i)) -
      (∏ j, (X + C (Function.update l k (l k + 1) j))).map (algebraMap ℂ (Module.End ℂ N))) (-l k) (by
    intro u hu
    rw [Polynomial.eval_sub, eval_sumMono, ← hc, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      Polynomial.eval_prod, key u hu]
    simp)
  intro u
  have e := congrArg (Polynomial.eval (algebraMap ℂ (Module.End ℂ N) u)) hD
  rw [Polynomial.eval_sub, eval_sumMono, ← hc, Polynomial.eval_map, Polynomial.eval₂_at_apply,
    Polynomial.eval_prod, Polynomial.eval_zero, sub_eq_zero] at e
  simpa using e

end CharacterRelations

theorem stepChar_of : TensorGl → StepFormula → QdetFacts → StepChar := by
  intro hT hS hQ n M _ _ E hE l hl
  refine ⟨CharacterRelations.part1 hT hS hQ E hE l hl, ?_⟩
  intro W N _ _ F q hW hO k hq hqF hqO
  exact CharacterRelations.part2 hT hS hQ E hE l hl W N F q hW hO k hq hqF hqO

end PositivityTheory.Rg.Cz

end
end

section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace TrOf

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem qdet_map {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B)
    (E : Fin n → Fin n → A) (u : ℂ) : φ (qdet E u) = qdet (fun a b => φ (E a b)) u := by
  simp only [qdet, qminor, Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def,
    map_add, apply_ite φ, map_zero, AlgHom.commutes]

variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

def rl (e : P ≃ Q) : TV n M P ≃ₗ[ℂ] TV n M Q :=
  LinearEquiv.funCongrLeft ℂ M (e.symm.arrowCongr (Equiv.refl (Fin n)))

omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] in
theorem rl_apply (e : P ≃ Q) (f : TV n M P) (J : Q → Fin n) : rl e f J = f (J ∘ e) := rfl

theorem tE_rl (e : P ≃ Q) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : TV n M P) :
    tE Finset.univ E a b (rl e f) = rl e (tE Finset.univ E a b f) := by
  funext J
  simp only [tE_apply, rl_apply]
  congr 1
  refine (Fintype.sum_equiv e.symm _ _ fun q => ?_)
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [← Function.update_comp_eq_of_injective J e.injective (e.symm q) b, Equiv.apply_symm_apply]

theorem conj_tE (e : P ≃ Q) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    (rl (n := n) (M := M) e).conjAlgEquiv ℂ (tE Finset.univ E a b) = tE Finset.univ E a b := by
  refine LinearMap.ext fun g => ?_
  simp only [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← tE_rl, LinearEquiv.apply_symm_apply]

theorem cA_rl {C : Type} [DecidableEq C] (e : P ≃ Q) (col : P → C) (b : P → Fin n) (f : TV n M P) :
    cA (col ∘ e.symm) (b ∘ e.symm) (rl e f) = cA col b f := by
  simp only [cA_apply, alt_apply, rl_apply]
  symm
  refine Finset.sum_equiv (Equiv.permCongr e) (fun σ => ?_) (fun σ _ => ?_)
  · simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply, Equiv.permCongr_apply,
      Equiv.symm_apply_apply]
    exact ⟨fun h q => h _, fun h p => by simpa using h (e p)⟩
  · rw [Equiv.Perm.sign_permCongr]
    congr 2
    funext x
    simp [Equiv.permCongr_apply]

theorem cA_congr {C C' : Type} [DecidableEq C] [DecidableEq C'] (c1 : Q → C) (c2 : Q → C')
    (h : ∀ p q, c1 p = c1 q ↔ c2 p = c2 q) (b : Q → Fin n) : (cA c1 b : TV n M Q →ₗ[ℂ] M) = cA c2 b := by
  have : colG c1 = colG c2 := by
    ext σ
    simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and, h]
  simp only [cA, this]

theorem transfer (e : P ≃ Q) (E : Fin n → Fin n → Module.End ℂ M) (l : Fin n → ℤ) (ℓ : M →ₗ[ℂ] ℂ)
    {C C' : Type} [DecidableEq C] [DecidableEq C'] (col : P → C) (col' : Q → C')
    (hcol : ∀ q q', col' q = col' q' ↔ col (e.symm q) = col (e.symm q')) (b co : P → Fin n)
    (h : ∃ S ∈ envAlg (fun _ : Unit => tE (Finset.univ : Finset Q) E), ℓ ∘ₗ cA col' (b ∘ e.symm) ∘ₗ S ≠ 0 ∧
      ∀ u : ℂ, (ℓ ∘ₗ cA col' (b ∘ e.symm) ∘ₗ S) ∘ₗ qdet (tE (Finset.univ : Finset Q) E) u =
        (∏ k, (u + l k + ((Finset.univ.filter fun p => co (e.symm p) = k).card : ℂ))) •
          (ℓ ∘ₗ cA col' (b ∘ e.symm) ∘ₗ S)) :
    ∃ S ∈ envAlg (fun _ : Unit => tE (Finset.univ : Finset P) E), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ u : ℂ,
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (Finset.univ : Finset P) E) u =
        (∏ k, (u + l k + ((Finset.univ.filter fun p => co p = k).card : ℂ))) • (ℓ ∘ₗ cA col b ∘ₗ S) := by
  obtain ⟨S', hS', hne, heig⟩ := h
  set φ := (rl (n := n) (M := M) e).conjAlgEquiv ℂ with hφdef
  set K := ℓ ∘ₗ cA col' (b ∘ e.symm) ∘ₗ S' with hK
  have hsymm : ∀ T f, φ.symm T f = (rl e).symm (T (rl e f)) := fun T f => rfl
  have key : ∀ f, ℓ (cA col b (φ.symm S' f)) = K (rl e f) := by
    intro f
    simp only [hK, LinearMap.comp_apply, hsymm]
    rw [← cA_rl e col b, LinearEquiv.apply_symm_apply, cA_congr col' (col ∘ e.symm) hcol]
  have hq : ∀ u f, rl e (qdet (tE (Finset.univ : Finset P) E) u f) = qdet (tE (Finset.univ : Finset Q) E) u (rl e f) := by
    intro u f
    have h1 : φ (qdet (tE (Finset.univ : Finset P) E) u) = qdet (tE (Finset.univ : Finset Q) E) u := by
      have := qdet_map (φ : Module.End ℂ (TV n M P) →ₐ[ℂ] Module.End ℂ (TV n M Q)) (tE (Finset.univ : Finset P) E) u
      simpa [conj_tE, hφdef] using this
    rw [← h1]
    simp only [hφdef, LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  have hcard : ∀ k, (Finset.univ.filter fun p => co (e.symm p) = k).card = (Finset.univ.filter fun p => co p = k).card :=
    fun k => Finset.card_equiv e.symm (by simp)
  refine ⟨φ.symm S', ?_, ?_, ?_⟩
  · have hle : envAlg (fun _ : Unit => tE (Finset.univ : Finset Q) E) ≤
        (envAlg (fun _ : Unit => tE (Finset.univ : Finset P) E)).comap φ.symm.toAlgHom := by
      refine Algebra.adjoin_le ?_
      rintro T ⟨_, a, c, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_comap]
      change φ.symm (tE Finset.univ E a c) ∈ _
      rw [φ.symm_apply_eq.mpr (conj_tE e E a c).symm]
      exact Algebra.subset_adjoin ⟨(), a, c, rfl⟩
    exact hle hS'
  · intro h0
    apply hne
    refine LinearMap.ext fun g => ?_
    have := LinearMap.congr_fun h0 ((rl e).symm g)
    simp only [LinearMap.comp_apply] at this
    rw [key, LinearEquiv.apply_symm_apply] at this
    simpa using this
  · intro u
    refine LinearMap.ext fun f => ?_
    have := LinearMap.congr_fun (heig u) (rl e f)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at this ⊢
    rw [key, key, hq, this]
    simp only [hK, LinearMap.comp_apply, hcard]

theorem zero_case (E : Fin 0 → Fin 0 → Module.End ℂ M) (l : Fin 0 → ℤ) (ℓ : M →ₗ[ℂ] ℂ) (hℓ : ℓ ≠ 0)
    {C : Type} [DecidableEq C] (col : P → C) (b co : P → Fin 0) :
    ∃ S ∈ envAlg (fun _ : Unit => tE (Finset.univ : Finset P) E), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ u : ℂ,
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (Finset.univ : Finset P) E) u =
        (∏ k, (u + l k + ((Finset.univ.filter fun p => co p = k).card : ℂ))) • (ℓ ∘ₗ cA col b ∘ₗ S) := by
  have : IsEmpty P := ⟨fun p => (b p).elim0⟩
  have hσ : ∀ σ : Equiv.Perm P, σ = 1 := fun σ => Equiv.ext fun p => isEmptyElim p
  have hG : colG col = {1} := by
    ext σ
    simp [colG, hσ σ]
  have hqd : ∀ u, qdet (tE (Finset.univ : Finset P) E) u = 1 := by
    intro u
    simp [qdet, qminor]
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hℓ (LinearMap.ext h)
  refine ⟨1, Subalgebra.one_mem _, fun h0 => hv ?_, fun u => ?_⟩
  · have := LinearMap.congr_fun h0 (fun _ => v)
    simpa [cA_apply, alt_apply, hG] using this
  · rw [hqd]
    refine LinearMap.ext fun x => ?_
    simp

def cI {C : Type} [DecidableEq C] (col : P → C) (p : P) : ℕ :=
  (Fintype.equivFin (Set.range col) ⟨col p, p, rfl⟩ : ℕ)

theorem cI_eq {C : Type} [DecidableEq C] (col : P → C) (p q : P) : cI col p = cI col q ↔ col p = col q := by
  simp only [cI, Fin.val_inj, Equiv.apply_eq_iff_eq, Subtype.ext_iff]

omit [DecidableEq P] in
theorem exists_sort {α : Type} [LinearOrder α] (key : P → α) :
    ∃ e : P ≃ Fin (Fintype.card P), Monotone (key ∘ e.symm) :=
  ⟨(Fintype.equivFin P).trans (Tuple.sort (key ∘ (Fintype.equivFin P).symm)).symm,
    Tuple.monotone_sort (key ∘ (Fintype.equivFin P).symm)⟩

end TrOf

theorem trans_of (hT : TransFin) : Trans := by
  intro n M _ _ E hE l hl ℓ hℓ hW P _ _ C _ col b co hb hco
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact TrOf.zero_case E l ℓ hℓ col b co
  set a : P → ℕ := TrOf.cI col with ha
  set v : P → ℤ := fun p => l (co p) + ((Finset.univ.filter fun q => a q < a p ∧ co q = co p).card : ℤ) with hv
  obtain ⟨e, he⟩ := TrOf.exists_sort (fun p => toLex (a p, OrderDual.toDual (v p)))
  have hle : ∀ i j : Fin (Fintype.card P), i ≤ j → a (e.symm i) ≤ a (e.symm j) ∧
      (a (e.symm i) = a (e.symm j) → v (e.symm j) ≤ v (e.symm i)) := by
    intro i j hij
    have := he hij
    simp only [Function.comp_apply, Prod.Lex.toLex_le_toLex, OrderDual.toDual_le_toDual] at this
    rcases this with h | ⟨h1, h2⟩
    · exact ⟨h.le, fun h' => absurd h' h.ne⟩
    · exact ⟨h1.le, fun _ => h2⟩
  have hmono : Monotone (a ∘ e.symm) := fun i j hij => (hle i j hij).1
  have hainj : ∀ p q, a p = a q ↔ col p = col q := TrOf.cI_eq col
  have htab : IsTab (a ∘ e.symm) (b ∘ e.symm) := by
    refine ⟨fun i j h1 h2 => e.symm.injective (hb.1 _ _ ((hainj _ _).1 h1) h2), fun i k hk => ?_⟩
    obtain ⟨q, hq1, hq2⟩ := hb.2 (e.symm i) k hk
    exact ⟨e q, by simp [(hainj _ _).2 hq1], by simpa using hq2⟩
  have hco' : ∀ i j : Fin (Fintype.card P), a (e.symm i) = a (e.symm j) → co (e.symm i) = co (e.symm j) → i = j :=
    fun i j h1 h2 => e.symm.injective (hco _ _ ((hainj _ _).1 h1) h2)
  have hcnt : ∀ j : Fin (Fintype.card P), (Finset.univ.filter fun p => p < j ∧ co (e.symm p) = co (e.symm j)).card =
      (Finset.univ.filter fun q => a q < a (e.symm j) ∧ co q = co (e.symm j)).card := by
    intro j
    refine Finset.card_equiv e.symm (fun p => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine and_congr_left fun hc => ⟨fun hp => lt_of_le_of_ne (hmono hp.le) (fun h => hp.ne (hco' p j h hc)),
      fun h => ?_⟩
    by_contra hp
    exact absurd (hmono (not_lt.1 hp)) (not_le.2 h)
  have hord : ∀ i j : Fin (Fintype.card P), i < j → (a ∘ e.symm) i = (a ∘ e.symm) j →
      l ((co ∘ e.symm) j) + ((Finset.univ.filter fun p => p < j ∧ (co ∘ e.symm) p = (co ∘ e.symm) j).card : ℤ) ≤
        l ((co ∘ e.symm) i) + ((Finset.univ.filter fun p => p < i ∧ (co ∘ e.symm) p = (co ∘ e.symm) i).card : ℤ) := by
    intro i j hij h
    simp only [Function.comp_apply] at h ⊢
    rw [hcnt i, hcnt j]
    exact (hle i j hij.le).2 h
  have := hT n M E hE l hl ℓ hℓ hW hn (Fintype.card P) (a ∘ e.symm) (b ∘ e.symm) (co ∘ e.symm) hmono htab hord
  exact TrOf.transfer e E l ℓ col (a ∘ e.symm) (fun q q' => hainj _ _) b co this

end PositivityTheory.Rg.Cz

end
end

section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace SemiInvariantDeterminant

theorem det_bar {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] {n : ℕ} {bar : ι → ι}
    {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} (hK : IsKD bar κ) (τ : ι) (γ : Γ) :
    (κ (bar τ) γ).det = star (κ τ γ).det := by
  have e : κ (bar τ) γ = (starRingEnd ℂ).mapMatrix (κ τ γ) := by
    ext i j; exact hK.conj τ γ i j
  rw [e, ← RingHom.map_det]
  rfl

theorem det_mul_star {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] {n : ℕ} {bar : ι → ι}
    {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} (hK : IsKD bar κ) (τ : ι) (γ : Γ) :
    (κ τ γ).det * star (κ τ γ).det = 1 := by
  have := congrArg Matrix.det (hK.unit τ γ)
  rwa [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this

end SemiInvariantDeterminant

open SemiInvariantDeterminant in
theorem semiZero_of (hQ : QdetFacts) (_hW : WallAlg) (hL : LieInv) (hWQ : WallQuot) : SemiZero := by
  intro n hn M _ _ ι _ _ Γ _ _ bar κ E ρ hK hG s φ hφ hS
  obtain ⟨lab, c, ξ, -, hact, I, w, hw, hwξ⟩ := hS
  have hρ : ∀ γ, ρ γ (ξ I) = (∏ τ, (κ τ γ).det ^ c τ) • ξ I := by
    intro γ
    have h := congrFun (hact γ) I
    rw [actT_apply, Pi.smul_apply] at h
    rw [← h, Fintype.sum_unique]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
    rw [Subsingleton.elim (default : Fin 0 → Fin n) I]
  obtain ⟨N, F, hFgl, -, hFch, hFE, hN⟩ := hWQ n M ι E hG.gl hG.comm (fun _ _ => s) φ (by
    intro τ u
    rw [hφ τ u, Finset.prod_const, Finset.card_univ, Fintype.card_fin])
  have hξN : N.mkQ (ξ I) ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hN]
    push Not
    exact ⟨w, hw, hwξ⟩
  have htr : ∀ τ', N.mkQ ((∑ a, E τ' a a) (ξ I)) = (∑ a, F τ' a a) (N.mkQ (ξ I)) := by
    intro τ'
    simp only [LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun a _ => LinearMap.congr_fun (hFE τ' a a) (ξ I)
  have hc : ∀ τ, c τ = c (bar τ) := by
    intro τ
    have hl := hL n M ι Γ bar κ E ρ hK hG c (ξ I) hρ τ
    have h1 : N.mkQ ((∑ a, E τ a a) (ξ I)) = N.mkQ ((∑ a, E (bar τ) a a) (ξ I)) := by
      rw [htr, htr, (hQ n (M ⧸ N) (F τ) (hFgl τ)).2.2.1 _ (hFch τ),
        (hQ n (M ⧸ N) (F (bar τ)) (hFgl (bar τ))).2.2.1 _ (hFch (bar τ))]
    have h2 : (∑ a, E τ a a) (ξ I) - (∑ a, E (bar τ) a a) (ξ I) =
        ((n : ℂ) * ((c τ - c (bar τ) : ℤ) : ℂ)) • ξ I := by
      rw [LinearMap.sum_apply, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
      simp only [hl, if_true]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    have h3 : ((n : ℂ) * ((c τ - c (bar τ) : ℤ) : ℂ)) • N.mkQ (ξ I) = 0 := by
      rw [← map_smul, ← h2, map_sub, h1, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd (Nat.cast_eq_zero.mp h) (by omega)
      · exact sub_eq_zero.mp (Int.cast_eq_zero.mp h)
    · exact absurd h hξN
  have hχ : ∀ γ, (∏ τ, (κ τ γ).det ^ c τ) = 1 := by
    intro γ
    refine Finset.prod_involution (fun τ _ => bar τ) ?_ ?_ (fun _ _ => Finset.mem_univ _)
      (fun τ _ => hK.invol τ)
    · intro τ _
      rw [det_bar hK, ← hc τ, ← mul_zpow, det_mul_star hK, _root_.one_zpow]
    · intro τ _ _
      exact hK.ne τ
  exact ⟨ξ I, fun γ => by rw [hρ, hχ, one_smul], w, hw, hwξ⟩

end PositivityTheory.Rg.Cz

end
end

section
namespace PositivityTheory.Rg.Cz

theorem kType_holds : KType := by
  have tg := tensorGl_holds
  have jm := jmComm_of tg
  have cu := curry_holds
  have qd := qdetFacts_holds
  have pq := piQdet_of tg jm
  have sf := stepFormula_of tg jm pq cu
  have sc := stepChar_of tg sf qd
  have sp := spectrum_of tg jm cu sc
  have ht := height_of tg
  have wq := wallQuot_of qd
  have ch := chain_of tg jm cu sf qd sc ht wq
  have ca := colAnti_of tg jm ht
  have tf := transFin_of tg jm sf qd sp ch ca
  have tr := trans_of tf
  have ta := transAll_of tg tr
  have tk := tensorGK_of tg
  have wa := wallAlg_of tg jm qd sp
  have li := lieInv_holds
  have co := contract_of tg qd wa tk li wq
  have sz := semiZero_of qd wa li wq
  have sa := sphAll_of swStart_holds co sz
  exact kType_of tg ta tk sa young_holds

end PositivityTheory.Rg.Cz
end
