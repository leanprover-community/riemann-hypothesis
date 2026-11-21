import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomLocBijectiveGrSum

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

open DirectSum

section NSum

variable {κ : Type*} {R : Type*} [CommRing R]
  {V : ℕ → Type*} [∀ n, AddCommGroup (V n)] [∀ n, Module R (V n)]
  {V' : ℕ → Type*} [∀ n, AddCommGroup (V' n)] [∀ n, Module R (V' n)]

def NOpsCommute (y : κ → ∀ n, V n →ₗ[R] V (n + 1)) : Prop :=
  ∀ (i j : κ) (n : ℕ) (a : V n), y i (n + 1) (y j n a) = y j (n + 1) (y i n a)

def NSum {y : κ → ∀ n, V n →ₗ[R] V (n + 1)} (_ : NOpsCommute y) : Type _ := ⨁ n, V n

namespace NSum

variable {y : κ → ∀ n, V n →ₗ[R] V (n + 1)} (hy : NOpsCommute y)
  {y' : κ → ∀ n, V' n →ₗ[R] V' (n + 1)} (hy' : NOpsCommute y')

instance : AddCommGroup (NSum hy) := inferInstanceAs (AddCommGroup (⨁ n, V n))

instance : Module R (NSum hy) := inferInstanceAs (Module R (⨁ n, V n))

def of (n : ℕ) : V n →ₗ[R] NSum hy := DirectSum.lof R ℕ V n

def component (n : ℕ) : NSum hy →ₗ[R] V n := DirectSum.component R ℕ V n

@[simp]
theorem component_of (n : ℕ) (a : V n) : component hy n (of hy n a) = a :=
  DirectSum.component.lof_self R n a

theorem component_of_ne {n k : ℕ} (h : k ≠ n) (a : V k) : component hy n (of hy k a) = 0 :=
  (DirectSum.component.of R n k a).trans (dif_neg h)

theorem of_injective (n : ℕ) : Function.Injective (of hy n) :=
  Function.LeftInverse.injective (component_of hy n)

theorem lhom_ext {N : Type*} [AddCommGroup N] [Module R N] {f g : NSum hy →ₗ[R] N}
    (h : ∀ n a, f (of hy n a) = g (of hy n a)) : f = g :=
  DirectSum.linearMap_ext R fun n => LinearMap.ext (h n)

theorem induction {C : NSum hy → Prop} (h0 : C 0) (hof : ∀ n a, C (of hy n a))
    (hadd : ∀ a b, C a → C b → C (a + b)) (m : NSum hy) : C m :=
  DirectSum.induction_on (β := V) (motive := C) m h0 hof hadd

def desc {N : Type*} [AddCommGroup N] [Module R N] (φ : ∀ n, V n →ₗ[R] N) : NSum hy →ₗ[R] N :=
  DirectSum.toModule R ℕ N φ

@[simp]
theorem desc_of {N : Type*} [AddCommGroup N] [Module R N] (φ : ∀ n, V n →ₗ[R] N) (n : ℕ)
    (a : V n) : desc hy φ (of hy n a) = φ n a :=
  DirectSum.toModule_lof R n a

def op (i : κ) : Module.End R (NSum hy) := desc hy fun n => of hy (n + 1) ∘ₗ y i n

@[simp]
theorem op_of (i : κ) (n : ℕ) (a : V n) : op hy i (of hy n a) = of hy (n + 1) (y i n a) :=
  desc_of hy _ n a

theorem commute_op (i j : κ) : Commute (op hy i) (op hy j) :=
  lhom_ext hy fun n a => by simp [hy i j n a]

instance : Module (MvPolynomial κ R) (NSum hy) :=
  Module.compHom (NSum hy) (Wick.commEval R (op hy) (commute_op hy)).toRingHom

theorem smul_def (p : MvPolynomial κ R) (m : NSum hy) :
    p • m = Wick.commEval R (op hy) (commute_op hy) p m := rfl

instance : IsScalarTower R (MvPolynomial κ R) (NSum hy) where
  smul_assoc r p m := by rw [smul_def, smul_def, map_smul]; rfl

theorem X_smul (i : κ) (m : NSum hy) : (MvPolynomial.X i : MvPolynomial κ R) • m = op hy i m := by
  rw [smul_def, Wick.commEval_X]

@[simp]
theorem X_smul_of (i : κ) (n : ℕ) (a : V n) :
    (MvPolynomial.X i : MvPolynomial κ R) • of hy n a = of hy (n + 1) (y i n a) := by
  rw [X_smul, op_of]

def lift {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial κ R) N]
    [IsScalarTower R (MvPolynomial κ R) N] (φ : ∀ n, V n →ₗ[R] N)
    (hφ : ∀ i n a, φ (n + 1) (y i n a) = (MvPolynomial.X i : MvPolynomial κ R) • φ n a) :
    NSum hy →ₗ[MvPolynomial κ R] N where
  toFun := desc hy φ
  map_add' := map_add _
  map_smul' p m := by
    have hX (i : κ) (m : NSum hy) : desc hy φ ((MvPolynomial.X i : MvPolynomial κ R) • m) =
        (MvPolynomial.X i : MvPolynomial κ R) • desc hy φ m := by
      induction m using NSum.induction with
      | h0 => simp
      | hof n a => simp [hφ]
      | hadd a b ha hb => simp only [smul_add, map_add, ha, hb]
    rw [RingHom.id_apply]
    induction p using MvPolynomial.induction_on generalizing m with
    | C a => rw [← MvPolynomial.algebraMap_eq, algebraMap_smul, algebraMap_smul, map_smul]
    | add p q hp hq => rw [add_smul, add_smul, map_add, hp, hq]
    | mul_X p i hp => rw [mul_smul, mul_smul, hp, hX]

@[simp]
theorem lift_of {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial κ R) N]
    [IsScalarTower R (MvPolynomial κ R) N] (φ : ∀ n, V n →ₗ[R] N) (hφ) (n : ℕ) (a : V n) :
    lift hy φ hφ (of hy n a) = φ n a := desc_of hy φ n a

def map (φ : ∀ n, V n →ₗ[R] V' n) (hφ : ∀ i n a, φ (n + 1) (y i n a) = y' i n (φ n a)) :
    NSum hy →ₗ[MvPolynomial κ R] NSum hy' :=
  lift hy (fun n => of hy' n ∘ₗ φ n) fun i n a => by simp [hφ]

@[simp]
theorem map_of (φ : ∀ n, V n →ₗ[R] V' n) (hφ) (n : ℕ) (a : V n) :
    map hy hy' φ hφ (of hy n a) = of hy' n (φ n a) := lift_of hy _ _ n a

theorem component_map (φ : ∀ n, V n →ₗ[R] V' n) (hφ) (n : ℕ) (m : NSum hy) :
    component hy' n (map hy hy' φ hφ m) = φ n (component hy n m) := by
  induction m using NSum.induction with
  | h0 => simp
  | hof k a =>
    by_cases h : k = n
    · subst h
      simp
    · rw [map_of, component_of_ne hy' h, component_of_ne hy h, map_zero]
  | hadd a b ha hb => simp only [map_add, ha, hb]

theorem ext_component {m m' : NSum hy} (h : ∀ n, component hy n m = component hy n m') : m = m' :=
  DFinsupp.ext h

theorem map_bijective (φ : ∀ n, V n →ₗ[R] V' n) (hφ) (h : ∀ n, Function.Bijective (φ n)) :
    Function.Bijective (map hy hy' φ hφ) := by
  refine ⟨fun m m' e => ext_component hy fun n => (h n).1 ?_, fun m => ?_⟩
  · rw [← component_map hy hy' φ hφ, ← component_map hy hy' φ hφ, e]
  · induction m using NSum.induction with
    | h0 => exact ⟨0, map_zero _⟩
    | hof n b =>
      obtain ⟨a, rfl⟩ := (h n).2 b
      exact ⟨of hy n a, map_of hy hy' φ hφ n a⟩
    | hadd a b ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', map_add _ _ _⟩

end NSum

end NSum

section Bi

variable {ι κ : Type} {R : Type} [CommRing R]
  {W : ℕ → ℤ → Type} [∀ e t, AddCommGroup (W e t)] [∀ e t, Module R (W e t)]
  {W' : ℕ → ℤ → Type} [∀ e t, AddCommGroup (W' e t)] [∀ e t, Module R (W' e t)]

structure BiOps (W : ℕ → ℤ → Type) [∀ e t, AddCommGroup (W e t)] [∀ e t, Module R (W e t)]
    (ι κ : Type) where

  x : ι → ∀ e t, W e t →ₗ[R] W e (t + 1)

  y : κ → ∀ e t, W e t →ₗ[R] W (e + 1) t

  hx : ∀ i j e t a, x i e (t + 1) (x j e t a) = x j e (t + 1) (x i e t a)

  hy : ∀ k l e t a, y k (e + 1) t (y l e t a) = y l (e + 1) t (y k e t a)

  hxy : ∀ j l e t a, x j (e + 1) t (y l e t a) = y l e (t + 1) (x j e t a)

namespace BiOps

variable (D : BiOps (R := R) W ι κ) (D' : BiOps (R := R) W' ι κ)

theorem hyN (t : ℤ) : NOpsCommute (fun l e => D.y l e t) := fun i j e a => D.hy i j e t a

abbrev NM (t : ℤ) : Type := NSum (D.hyN t)

def xN (j : ι) (t : ℤ) : D.NM t →ₗ[MvPolynomial κ R] D.NM (t + 1) :=
  NSum.map (D.hyN t) (D.hyN (t + 1)) (fun e => D.x j e t) fun l e a => D.hxy j l e t a

@[simp]
theorem xN_of (j : ι) (t : ℤ) (e : ℕ) (a : W e t) :
    D.xN j t (NSum.of (D.hyN t) e a) = NSum.of (D.hyN (t + 1)) e (D.x j e t a) :=
  NSum.map_of (D.hyN t) (D.hyN (t + 1)) (fun e => D.x j e t) (fun l e a => D.hxy j l e t a) e a

theorem hxN : OperatorsCommute (R := MvPolynomial κ R) (A := D.NM) D.xN := fun i j t m => by
  induction m using NSum.induction with
  | h0 => simp
  | hof e a => simp [D.hx i j e t a]
  | hadd a b ha hb => simp only [map_add, ha, hb]

abbrev Tot : Type := GrSum D.hxN

abbrev grading : ℤ → Submodule (MvPolynomial κ R) D.Tot := GrSum.grading D.hxN

def of (e : ℕ) (t : ℤ) : W e t →+ D.Tot :=
  (GrSum.of D.hxN t).toAddMonoidHom.comp (NSum.of (D.hyN t) e).toAddMonoidHom

def comp (e : ℕ) (t : ℤ) : D.Tot →+ W e t :=
  (NSum.component (D.hyN t) e).toAddMonoidHom.comp
    ((GrSum.component D.hxN t).toAddMonoidHom)

theorem of_mem_grading (e : ℕ) (t : ℤ) (a : W e t) : D.of e t a ∈ D.grading t :=
  GrSum.of_mem_grading _ _ _

@[simp]
theorem comp_of (e : ℕ) (t : ℤ) (a : W e t) : D.comp e t (D.of e t a) = a := by
  simp [comp, of]

theorem of_injective (e : ℕ) (t : ℤ) : Function.Injective (D.of e t) :=
  Function.LeftInverse.injective (D.comp_of e t)

theorem X_smul_of (j : ι) (e : ℕ) (t : ℤ) (a : W e t) :
    (MvPolynomial.X j : MvPolynomial ι (MvPolynomial κ R)) • D.of e t a =
      D.of e (t + 1) (D.x j e t a) := by
  simp [of, xN]

theorem C_smul_of (c : MvPolynomial κ R) (e : ℕ) (t : ℤ) (a : W e t) :
    (MvPolynomial.C c : MvPolynomial ι (MvPolynomial κ R)) • D.of e t a =
      GrSum.of D.hxN t (c • NSum.of (D.hyN t) e a) := by
  rw [← MvPolynomial.algebraMap_eq, algebraMap_smul]
  exact (map_smul (GrSum.of D.hxN t) c _).symm

theorem C_X_smul_of (l : κ) (e : ℕ) (t : ℤ) (a : W e t) :
    (MvPolynomial.C (MvPolynomial.X l) : MvPolynomial ι (MvPolynomial κ R)) • D.of e t a =
      D.of (e + 1) t (D.y l e t a) := by
  rw [C_smul_of, NSum.X_smul_of]
  rfl

theorem C_C_smul_of (r : R) (e : ℕ) (t : ℤ) (a : W e t) :
    (MvPolynomial.C (MvPolynomial.C r) : MvPolynomial ι (MvPolynomial κ R)) • D.of e t a =
      D.of e t (r • a) := by
  rw [C_smul_of, ← MvPolynomial.algebraMap_eq, algebraMap_smul, ← map_smul]
  rfl

theorem induction {C : D.Tot → Prop} (h0 : C 0) (hof : ∀ e t a, C (D.of e t a))
    (hadd : ∀ a b, C a → C b → C (a + b)) (m : D.Tot) : C m := by
  have key (t : ℤ) (n : D.NM t) : C (GrSum.of D.hxN t n) := by
    induction n using NSum.induction with
    | h0 => rw [map_zero]; exact h0
    | hof e a => exact hof e t a
    | hadd a b ha hb => rw [map_add]; exact hadd _ _ ha hb
  exact DirectSum.induction_on (β := D.NM) (motive := C) m h0 (fun t n => key t n) hadd

theorem comp_of_ne {e e' : ℕ} {t t' : ℤ} (h : ¬(e = e' ∧ t = t')) (a : W e t) :
    D.comp e' t' (D.of e t a) = 0 := by
  by_cases ht : t = t'
  · subst ht
    have he : e ≠ e' := fun he => h ⟨he, rfl⟩
    simpa [comp, of] using NSum.component_of_ne (D.hyN t) he a
  · have := GrSum.component_of_ne D.hxN ht (NSum.of (D.hyN t) e a)
    simp only [comp, of, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe] at this ⊢
    rw [this, map_zero]

theorem exists_finset_sum (m : D.Tot) :
    ∃ s : Finset (ℕ × ℤ), m = ∑ q ∈ s, D.of q.1 q.2 (D.comp q.1 q.2 m) := by
  classical
  suffices h : ∃ s₀ : Finset (ℕ × ℤ), ∀ s, s₀ ⊆ s → m = ∑ q ∈ s, D.of q.1 q.2 (D.comp q.1 q.2 m) by
    obtain ⟨s₀, h⟩ := h
    exact ⟨s₀, h _ subset_rfl⟩
  induction m using D.induction with
  | h0 => exact ⟨∅, fun s _ => by simp⟩
  | hof e t a =>
    refine ⟨{(e, t)}, fun s hs => ?_⟩
    rw [Finset.sum_eq_single_of_mem (e, t) (hs (Finset.mem_singleton_self _))]
    · simp
    · rintro ⟨e', t'⟩ _ hne
      rw [comp_of_ne, map_zero]
      rintro ⟨rfl, rfl⟩
      exact hne rfl
  | hadd a b ha hb =>
    obtain ⟨s₁, h₁⟩ := ha
    obtain ⟨s₂, h₂⟩ := hb
    refine ⟨s₁ ∪ s₂, fun s hs => ?_⟩
    simp only [map_add, Finset.sum_add_distrib]
    rw [← h₁ s (Finset.union_subset_left hs), ← h₂ s (Finset.union_subset_right hs)]

def map (φ : ∀ e t, W e t →ₗ[R] W' e t)
    (hx : ∀ j e t a, φ e (t + 1) (D.x j e t a) = D'.x j e t (φ e t a))
    (hy : ∀ l e t a, φ (e + 1) t (D.y l e t a) = D'.y l e t (φ e t a)) :
    D.Tot →ₗ[MvPolynomial ι (MvPolynomial κ R)] D'.Tot :=
  GrSum.map D.hxN D'.hxN (fun t => NSum.map _ _ (fun e => φ e t) fun l e a => hy l e t a)
    fun j t m => by
      induction m using NSum.induction with
      | h0 => simp
      | hof e a => simp [hx]
      | hadd a b ha hb => simp only [map_add, ha, hb]

@[simp]
theorem map_of (φ : ∀ e t, W e t →ₗ[R] W' e t) (hx) (hy) (e : ℕ) (t : ℤ) (a : W e t) :
    D.map D' φ hx hy (D.of e t a) = D'.of e t (φ e t a) := by
  simp [map, of]

theorem isGradedMap_map (φ : ∀ e t, W e t →ₗ[R] W' e t) (hx) (hy) :
    IsGradedMap D.grading D'.grading (D.map D' φ hx hy) :=
  GrSum.isGradedMap_map _ _ _ _

theorem comp_map (φ : ∀ e t, W e t →ₗ[R] W' e t) (hx) (hy) (e : ℕ) (t : ℤ) (m : D.Tot) :
    D'.comp e t (D.map D' φ hx hy m) = φ e t (D.comp e t m) := by
  induction m using D.induction with
  | h0 => simp
  | hof e' t' a =>
    by_cases h : e' = e ∧ t' = t
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [map_of, comp_of_ne _ h, comp_of_ne _ h, map_zero]
  | hadd a b ha hb => simp only [map_add, ha, hb]

theorem X_smul_bijective (j : ι) (h : ∀ e t, Function.Bijective (D.x j e t)) :
    Function.Bijective fun m : D.Tot =>
      (MvPolynomial.X j : MvPolynomial ι (MvPolynomial κ R)) • m :=
  GrSum.X_smul_bijective D.hxN fun t => NSum.map_bijective (D.hyN t) (D.hyN (t + 1)) _ _ fun e => h e t

end BiOps

example : BiOps (R := ℤ) (fun _ _ => ℤ) Unit Unit where
  x _ _ _ := 2 • LinearMap.id
  y _ _ _ := 3 • LinearMap.id
  hx _ _ _ _ _ := rfl
  hy _ _ _ _ _ := rfl
  hxy _ _ _ _ a := by simp; ring

end Bi

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

section Tower

variable {ι : Type} [LinearOrder ι] {R : Type} [CommRing R] {g : ℕ} (ρ : Fin g → R)
  {T : ℕ → ℤ → Finset ι → Type} [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)]
  (res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S')
  (p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S)
  (mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S)

def TowerAx : Prop :=
  (∀ e t S S' (h : S ⊆ S') a, S.Nonempty →
    p e t S' (res (e + 1) t S S' h a) = res e t S S' h (p e t S a)) ∧
  (∀ j e t S a, S.Nonempty → p e (t + 1) S (mm j (e + 1) t S a) = mm j e t S (p e t S a)) ∧
  (∀ j e t S S' (h : S ⊆ S') a, S.Nonempty →
    res e (t + 1) S S' h (mm j e t S a) - mm j e t S' (res e t S S' h a) ∈
      Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e (t + 1) S'))) ∧
  (∀ e t S, S.Nonempty → Function.Surjective (p e t S)) ∧
  (∀ e t S, S.Nonempty → LinearMap.ker (p e t S) = Ideal.span (Set.range ρ) ^ (e + 1) • ⊤) ∧
  (∀ e t S, S.Nonempty → Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T e t S)) = ⊥)

def Ks (e : ℕ) (t : ℤ) (S : Finset ι) : Submodule R (T (e + 1) t S) :=
  if S.Nonempty then LinearMap.ker (p e t S) else ⊥

variable {ρ res p mm}

theorem mem_Ks {e : ℕ} {t : ℤ} {S : Finset ι} (hS : S.Nonempty) {a : T (e + 1) t S} :
    a ∈ Ks p e t S ↔ p e t S a = 0 := by
  simp [Ks, hS]

theorem eq_zero_of_mem_Ks {e : ℕ} {t : ℤ} {S : Finset ι} (hS : ¬S.Nonempty) {a : T (e + 1) t S}
    (ha : a ∈ Ks p e t S) : a = 0 := by
  simp only [Ks, if_neg hS, Submodule.mem_bot] at ha
  exact ha

theorem rho_mem (l : Fin g) : ρ l ∈ Ideal.span (Set.range ρ) := Ideal.subset_span ⟨l, rfl⟩

namespace TowerAx

variable (H : TowerAx ρ res p mm)
include H

theorem p_res (e t S S') (h : S ⊆ S') (a) (hS : S.Nonempty) :
    p e t S' (res (e + 1) t S S' h a) = res e t S S' h (p e t S a) := H.1 e t S S' h a hS

theorem p_mm (j e t S a) (hS : S.Nonempty) :
    p e (t + 1) S (mm j (e + 1) t S a) = mm j e t S (p e t S a) := H.2.1 j e t S a hS

theorem res_mm (j e t S S') (h : S ⊆ S') (a) (hS : S.Nonempty) :
    res e (t + 1) S S' h (mm j e t S a) - mm j e t S' (res e t S S' h a) ∈
      Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e (t + 1) S')) := H.2.2.1 j e t S S' h a hS

theorem surj (e t S) (hS : S.Nonempty) : Function.Surjective (p e t S) := H.2.2.2.1 e t S hS

theorem ker_eq (e t S) (hS : S.Nonempty) :
    LinearMap.ker (p e t S) = Ideal.span (Set.range ρ) ^ (e + 1) • ⊤ := H.2.2.2.2.1 e t S hS

theorem kill (e t S) (hS : S.Nonempty) :
    Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T e t S)) = ⊥ := H.2.2.2.2.2 e t S hS

theorem smul_eq_zero_of_mem {e : ℕ} {t : ℤ} {S : Finset ι} (hS : S.Nonempty) {m n : ℕ}
    (hmn : m + n = e + 1) {r : R} (hr : r ∈ Ideal.span (Set.range ρ) ^ m) {w : T e t S}
    (hw : w ∈ Ideal.span (Set.range ρ) ^ n • (⊤ : Submodule R (T e t S))) : r • w = 0 := by
  have hrw : r • w ∈ (Ideal.span (Set.range ρ) ^ m * Ideal.span (Set.range ρ) ^ n) •
      (⊤ : Submodule R (T e t S)) := by
    rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr hw
  rw [← pow_add, hmn, H.kill e t S hS] at hrw
  exact (Submodule.mem_bot R).1 hrw

theorem smul_eq_zero_of_p {e : ℕ} {t : ℤ} {S : Finset ι} (hS : S.Nonempty) {r : R}
    (hr : r ∈ Ideal.span (Set.range ρ)) {a : T (e + 1) t S} (ha : p e t S a = 0) : r • a = 0 := by
  have hw : a ∈ Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T (e + 1) t S)) := by
    rw [← H.ker_eq e t S hS]
    exact LinearMap.mem_ker.mpr ha
  exact H.smul_eq_zero_of_mem hS (m := 1) (n := e + 1) (by omega) (by rwa [pow_one]) hw

theorem rho_smul_surjInv (l : Fin g) {e : ℕ} {t : ℤ} {S : Finset ι} (hS : S.Nonempty)
    (b : T (e + 1 + 1) t S) :
    ρ l • Function.surjInv (H.surj (e + 1) t S hS) (p (e + 1) t S b) = ρ l • b := by
  have h : p (e + 1) t S (Function.surjInv (H.surj (e + 1) t S hS) (p (e + 1) t S b) - b) = 0 := by
    rw [map_sub, Function.surjInv_eq (H.surj (e + 1) t S hS), sub_self]
  have := H.smul_eq_zero_of_p hS (rho_mem l) h
  rwa [smul_sub, sub_eq_zero] at this

omit H in

def lam (H : TowerAx ρ res p mm) (l : Fin g) (e : ℕ) (t : ℤ) (S : Finset ι) (hS : S.Nonempty) :
    T (e + 1) t S →ₗ[R] T (e + 1 + 1) t S where
  toFun a := ρ l • Function.surjInv (H.surj (e + 1) t S hS) a
  map_add' a b := by
    obtain ⟨a, rfl⟩ := H.surj (e + 1) t S hS a
    obtain ⟨b, rfl⟩ := H.surj (e + 1) t S hS b
    rw [← map_add, H.rho_smul_surjInv l hS, H.rho_smul_surjInv l hS, H.rho_smul_surjInv l hS,
      smul_add]
  map_smul' r a := by
    obtain ⟨a, rfl⟩ := H.surj (e + 1) t S hS a
    rw [← map_smul, H.rho_smul_surjInv l hS, H.rho_smul_surjInv l hS, RingHom.id_apply, smul_comm]

omit H in
theorem lam_p (H : TowerAx ρ res p mm) (l : Fin g) {e : ℕ} {t : ℤ} {S : Finset ι}
    (hS : S.Nonempty) (b : T (e + 1 + 1) t S) :
    H.lam l e t S hS (p (e + 1) t S b) = ρ l • b := H.rho_smul_surjInv l hS b

omit H in

def yK (H : TowerAx ρ res p mm) (l : Fin g) (e : ℕ) (t : ℤ) (S : Finset ι) :
    Ks p e t S →ₗ[R] Ks p (e + 1) t S :=
  if hS : S.Nonempty then
    (H.lam l e t S hS).restrict fun a ha => by
      obtain ⟨b, rfl⟩ := H.surj (e + 1) t S hS a
      rw [mem_Ks hS, H.lam_p, map_smul]
      exact H.smul_eq_zero_of_p hS (rho_mem l) ((mem_Ks hS).1 ha)
  else 0

omit H in

theorem coe_yK (H : TowerAx ρ res p mm) (l : Fin g) {e : ℕ} {t : ℤ} {S : Finset ι}
    (hS : S.Nonempty) (a : Ks p e t S) (b : T (e + 1 + 1) t S) (hb : p (e + 1) t S b = a) :
    (H.yK l e t S a : T (e + 1 + 1) t S) = ρ l • b := by
  simp only [yK, dif_pos hS, LinearMap.restrict_coe_apply]
  rw [← hb, H.lam_p]

omit H in

def xK (H : TowerAx ρ res p mm) (j : ι) (e : ℕ) (t : ℤ) (S : Finset ι) :
    Ks p e t S →ₗ[R] Ks p e (t + 1) S :=
  (mm j (e + 1) t S).restrict fun a ha => by
    by_cases hS : S.Nonempty
    · rw [mem_Ks hS, H.p_mm j e t S a hS, (mem_Ks hS).1 ha, map_zero]
    · rw [eq_zero_of_mem_Ks hS ha, map_zero]
      exact zero_mem _

omit H in
@[simp]
theorem coe_xK (H : TowerAx ρ res p mm) (j : ι) (e : ℕ) (t : ℤ) (S : Finset ι) (a : Ks p e t S) :
    (H.xK j e t S a : T (e + 1) (t + 1) S) = mm j (e + 1) t S a := rfl

omit H in

def resK (H : TowerAx ρ res p mm) (e : ℕ) (t : ℤ) {S S' : Finset ι} (h : S ⊆ S') :
    Ks p e t S →ₗ[R] Ks p e t S' :=
  (res (e + 1) t S S' h).restrict fun a ha => by
    by_cases hS : S.Nonempty
    · rw [mem_Ks (hS.mono h), H.p_res e t S S' h a hS, (mem_Ks hS).1 ha, map_zero]
    · rw [eq_zero_of_mem_Ks hS ha, map_zero]
      exact zero_mem _

omit H in
@[simp]
theorem coe_resK (H : TowerAx ρ res p mm) (e : ℕ) (t : ℤ) {S S' : Finset ι} (h : S ⊆ S')
    (a : Ks p e t S) : (H.resK e t h a : T (e + 1) t S') = res (e + 1) t S S' h a := rfl

omit H in

def ops (H : TowerAx ρ res p mm)
    (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S)
    (S : Finset ι) : BiOps (R := R) (fun e t => Ks p e t S) ι (Fin g) where
  x j e t := H.xK j e t S
  y l e t := H.yK l e t S
  hx i j e t a := Subtype.ext (hc (e + 1) S i j t a)
  hy k l e t a := by
    by_cases hS : S.Nonempty
    · obtain ⟨b, hb⟩ := H.surj (e + 1) t S hS a
      obtain ⟨c, hc'⟩ := H.surj (e + 1 + 1) t S hS b
      have h1 (l : Fin g) : p (e + 1 + 1) t S (ρ l • c) = H.yK l e t S a := by
        rw [map_smul, hc', H.coe_yK l hS a b hb]
      apply Subtype.ext
      rw [H.coe_yK k hS _ _ (h1 l), H.coe_yK l hS _ _ (h1 k), smul_comm]
    · apply Subtype.ext
      simp [yK, hS]
  hxy j l e t a := by
    by_cases hS : S.Nonempty
    · obtain ⟨b, hb⟩ := H.surj (e + 1) t S hS a
      apply Subtype.ext
      have h1 : p (e + 1) (t + 1) S (mm j (e + 1 + 1) t S b) = H.xK j e t S a := by
        rw [H.p_mm j (e + 1) t S b hS, hb, coe_xK]
      rw [H.coe_yK l hS _ _ h1, coe_xK, H.coe_yK l hS a b hb, map_smul]
    · apply Subtype.ext
      simp [yK, hS]

omit H in

theorem resK_xK (H : TowerAx ρ res p mm) (j : ι) (e : ℕ) (t : ℤ) {S S' : Finset ι} (h : S ⊆ S')
    (a : Ks p e t S) :
    H.resK e (t + 1) h (H.xK j e t S a) = H.xK j e t S' (H.resK e t h a) := by
  apply Subtype.ext
  simp only [coe_resK, coe_xK]
  by_cases hS : S.Nonempty
  · have hS' : S'.Nonempty := hS.mono h
    have ha : (a : T (e + 1) t S) ∈
        Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T (e + 1) t S)) := by
      rw [← H.ker_eq e t S hS]
      exact LinearMap.mem_ker.mpr ((mem_Ks hS).1 a.2)
    have key : Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T (e + 1) t S)) ≤
        LinearMap.ker (res (e + 1) (t + 1) S S' h ∘ₗ mm j (e + 1) t S -
          mm j (e + 1) t S' ∘ₗ res (e + 1) t S S' h) := by
      rw [Submodule.smul_le]
      intro r hr x _
      rw [LinearMap.mem_ker, map_smul]
      refine H.smul_eq_zero_of_mem hS' (m := e + 1) (n := 1) rfl hr ?_
      rw [pow_one]
      exact H.res_mm j (e + 1) t S S' h x hS
    have hk := key ha
    rw [LinearMap.mem_ker] at hk
    simpa [sub_eq_zero] using hk
  · rw [eq_zero_of_mem_Ks hS a.2]
    simp

omit H in

theorem resK_yK (H : TowerAx ρ res p mm) (l : Fin g) (e : ℕ) (t : ℤ) {S S' : Finset ι}
    (h : S ⊆ S') (a : Ks p e t S) :
    H.resK (e + 1) t h (H.yK l e t S a) = H.yK l e t S' (H.resK e t h a) := by
  apply Subtype.ext
  by_cases hS : S.Nonempty
  · obtain ⟨b, hb⟩ := H.surj (e + 1) t S hS a
    have h1 : p (e + 1) t S' (res (e + 1 + 1) t S S' h b) = H.resK e t h a := by
      rw [H.p_res (e + 1) t S S' h b hS, hb, coe_resK]
    rw [H.coe_yK l (hS.mono h) _ _ h1, coe_resK, H.coe_yK l hS a b hb, map_smul]
  · obtain rfl : a = 0 := Subtype.ext (eq_zero_of_mem_Ks hS a.2)
    simp

variable (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S)
  fun j t => mm j e t S)

omit H in

abbrev Tot (H : TowerAx ρ res p mm) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R)
    (A := fun t => T e t S) fun j t => mm j e t S) (S : Finset ι) : Type :=
  (H.ops hc S).Tot

omit H in

def resTot (H : TowerAx ρ res p mm) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R)
    (A := fun t => T e t S) fun j t => mm j e t S) (S S' : Finset ι) (h : S ⊆ S') :
    H.Tot hc S →ₗ[MvPolynomial ι (MvPolynomial (Fin g) R)] H.Tot hc S' :=
  (H.ops hc S).map (H.ops hc S') (fun e t => H.resK e t h) (fun j e t a => H.resK_xK j e t h a)
    fun l e t a => H.resK_yK l e t h a

omit H in
@[simp]
theorem resTot_of (H : TowerAx ρ res p mm) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R)
    (A := fun t => T e t S) fun j t => mm j e t S) {S S' : Finset ι} (h : S ⊆ S') (e : ℕ) (t : ℤ)
    (a : Ks p e t S) :
    H.resTot hc S S' h ((H.ops hc S).of e t a) = (H.ops hc S').of e t (H.resK e t h a) :=
  BiOps.map_of (H.ops hc S) (H.ops hc S') (fun e t => H.resK e t h)
    (fun j e t a => H.resK_xK j e t h a) (fun l e t a => H.resK_yK l e t h a) e t a

omit H in

theorem comp_resTot (H : TowerAx ρ res p mm) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R)
    (A := fun t => T e t S) fun j t => mm j e t S) {S S' : Finset ι} (h : S ⊆ S') (e : ℕ) (t : ℤ)
    (m : H.Tot hc S) :
    (H.ops hc S').comp e t (H.resTot hc S S' h m) = H.resK e t h ((H.ops hc S).comp e t m) :=
  BiOps.comp_map (H.ops hc S) (H.ops hc S') (fun e t => H.resK e t h)
    (fun j e t a => H.resK_xK j e t h a) (fun l e t a => H.resK_yK l e t h a) e t m

omit H in
theorem isGradedMap_resTot (H : TowerAx ρ res p mm) (hc : ∀ e S, OperatorsCommute (ι := ι)
    (R := R) (A := fun t => T e t S) fun j t => mm j e t S) {S S' : Finset ι} (h : S ⊆ S') :
    IsGradedMap (H.ops hc S).grading (H.ops hc S').grading (H.resTot hc S S' h) :=
  BiOps.isGradedMap_map (H.ops hc S) (H.ops hc S') (fun e t => H.resK e t h)
    (fun j e t a => H.resK_xK j e t h a) (fun l e t a => H.resK_yK l e t h a)

end TowerAx

end Tower

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end
