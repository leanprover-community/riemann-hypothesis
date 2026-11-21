import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta

section
namespace GlobalTheory.FinsetKernelTrivial

open scoped BigOperators

noncomputable def restr {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V) (P : Finset X) :
    W →ₗ[ℂ] (P → ℂ) :=
  LinearMap.pi (fun x : P => (LinearMap.proj (R := ℂ) (φ := fun _ : X => ℂ) x.1).comp (V.subtype.comp W.subtype))

lemma restr_apply {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V) (P : Finset X)
    (w : W) (x : P) : restr V W P w x = ((w : V) : X → ℂ) x := rfl

lemma exists_finset_ker_eq_bot {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] : ∃ P : Finset X, LinearMap.ker (restr V W P) = ⊥ := by
  classical
  have hex : ∃ n, ∃ P : Finset X, Module.finrank ℂ (LinearMap.ker (restr V W P)) = n :=
    ⟨_, ∅, rfl⟩
  obtain ⟨P, hP⟩ := Nat.find_spec hex
  refine ⟨P, ?_⟩
  by_contra hne
  obtain ⟨w, hwK, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hf : ((w : V) : X → ℂ) ≠ 0 := by
    intro h
    apply hw0
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hf
  have hle : LinearMap.ker (restr V W (insert x P)) < LinearMap.ker (restr V W P) := by
    refine lt_of_le_of_ne ?_ ?_
    · intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      funext y
      have := congrFun hv ⟨y.1, Finset.mem_insert_of_mem y.2⟩
      simpa [restr_apply] using this
    · intro heq
      have : w ∈ LinearMap.ker (restr V W (insert x P)) := heq ▸ hwK
      rw [LinearMap.mem_ker] at this
      have := congrFun this ⟨x, Finset.mem_insert_self x P⟩
      exact hx (by simpa [restr_apply] using this)
  have hlt := Submodule.finrank_lt_finrank_of_lt hle
  have hmin := Nat.find_min hex (hP ▸ hlt)
  exact hmin ⟨insert x P, rfl⟩

theorem main : ∀ {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ ↥V) [FiniteDimensional ℂ ↥W],
    ∃ (P : Finset X) (e : X → ↥V), ∀ w ∈ W, w = ∑ x ∈ P, (↑w : X → ℂ) x • e x := by
  intro X V W _
  classical
  obtain ⟨P, hP⟩ := exists_finset_ker_eq_bot V W
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (restr V W P) hP
  refine ⟨P, fun x => if h : x ∈ P then ((L (Pi.single ⟨x, h⟩ 1) : W) : V) else 0, ?_⟩
  intro w hw
  have h1 : (⟨w, hw⟩ : W) = L (restr V W P ⟨w, hw⟩) := by
    have := congrArg (fun g => g ⟨w, hw⟩) hL
    simpa using this.symm
  have h2 : restr V W P ⟨w, hw⟩ = ∑ x : P, ((w : X → ℂ) x.1) • (Pi.single x (1 : ℂ)) := by
    funext y
    simp [restr_apply, Finset.sum_apply, Pi.single_apply]
  have h3 : w = ∑ x : P, ((w : X → ℂ) x.1) • ((L (Pi.single x 1) : W) : V) := by
    have := congrArg (fun u : W => (u : V)) h1
    simp only at this
    conv_lhs => rw [this, h2, map_sum]
    simp [map_smul]
  conv_lhs => rw [h3]
  rw [← Finset.sum_attach P]
  refine Finset.sum_congr rfl ?_
  intro x _
  simp [x.2]

end GlobalTheory.FinsetKernelTrivial
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory

theorem funSub_evalExpand_exists {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] :
    ∃ (P : Finset X) (e : X → V), ∀ w ∈ W, w = ∑ x ∈ P, (w : X → ℂ) x • e x := by
  first
  | exact @_root_.GlobalTheory.FinsetKernelTrivial.main
  | exact _root_.GlobalTheory.FinsetKernelTrivial.main
  | (apply _root_.GlobalTheory.FinsetKernelTrivial.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinsetKernelTrivial.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinsetKernelTrivial.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinsetKernelTrivial.main ..)

theorem funSub_multilinear_expand {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    {V : ∀ i, Submodule ℂ (X i → ℂ)} {N : Type} [AddCommMonoid N] [Module ℂ N]
    (Φ : MultilinearMap ℂ (fun i => V i) N) (P : ∀ i, Finset (X i)) (e : ∀ i, X i → V i)
    (h : ∀ i, V i) (hh : ∀ i, h i = ∑ x ∈ P i, (h i : X i → ℂ) x • e i x) :
    Φ h = ∑ x ∈ Fintype.piFinset P, (∏ i, (h i : X i → ℂ) (x i)) • Φ (fun i => e i (x i)) := by
  conv_lhs => rw [show h = fun i => ∑ x ∈ P i, (h i : X i → ℂ) x • e i x from funext hh]
  rw [Φ.map_sum_finset]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Φ.map_smul_univ]

end GlobalTheory

namespace GlobalTheory

theorem funProd_multilinear_sum_eq : ∀ {ι κ Δ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {X : ι → Type} {Y : κ → Type}
    {V : ∀ i, Submodule ℂ (X i → ℂ)} {V' : ∀ j, Submodule ℂ (Y j → ℂ)}
    (M : MultilinearMap ℂ (fun i => V i) (MultilinearMap ℂ (fun j => V' j) ℂ)) (τ : Δ →₀ ℂ)
    (f f' : Δ → ∀ i, V i) (g g' : Δ → ∀ j, V' j),
    (∀ (x : ∀ i, X i) (y : ∀ j, Y j),
      (τ.sum fun d a => a * (∏ i, (f d i : X i → ℂ) (x i)) * ∏ j, (g d j : Y j → ℂ) (y j)) =
        τ.sum fun d a => a * (∏ i, (f' d i : X i → ℂ) (x i)) * ∏ j, (g' d j : Y j → ℂ) (y j)) →
    (τ.sum fun d a => a * M (f d) (g d)) = τ.sum fun d a => a * M (f' d) (g' d) := by
  intro ι κ Δ _ _ _ _ X Y V V' M τ f f' g g' hfg
  classical
  let Wf : ∀ i, Submodule ℂ (V i) := fun i =>
    Submodule.span ℂ ((τ.support.image (fun d => f d i) ∪ τ.support.image (fun d => f' d i) :
      Finset (V i)) : Set (V i))
  let Wg : ∀ j, Submodule ℂ (V' j) := fun j =>
    Submodule.span ℂ ((τ.support.image (fun d => g d j) ∪ τ.support.image (fun d => g' d j) :
      Finset (V' j)) : Set (V' j))
  choose P e hP using fun i => funSub_evalExpand_exists (V i) (Wf i)
  choose Q e' hQ using fun j => funSub_evalExpand_exists (V' j) (Wg j)
  have key : ∀ (F : Δ → ∀ i, V i) (G : Δ → ∀ j, V' j),
      (∀ d ∈ τ.support, ∀ i, F d i ∈ Wf i) → (∀ d ∈ τ.support, ∀ j, G d j ∈ Wg j) →
      (τ.sum fun d a => a * M (F d) (G d)) =
        ∑ x ∈ Fintype.piFinset P, ∑ y ∈ Fintype.piFinset Q,
          M (fun i => e i (x i)) (fun j => e' j (y j)) *
            τ.sum fun d a => a * (∏ i, (F d i : X i → ℂ) (x i)) * ∏ j, (G d j : Y j → ℂ) (y j) := by
    intro F G hF hG
    have hM : ∀ d ∈ τ.support, M (F d) (G d) = ∑ x ∈ Fintype.piFinset P, ∑ y ∈ Fintype.piFinset Q,
        M (fun i => e i (x i)) (fun j => e' j (y j)) *
          ((∏ i, (F d i : X i → ℂ) (x i)) * ∏ j, (G d j : Y j → ℂ) (y j)) := by
      intro d hd
      rw [funSub_multilinear_expand M P e (F d) (fun i => hP i _ (hF d hd i))]
      rw [MultilinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [MultilinearMap.smul_apply,
        funSub_multilinear_expand (M fun i => e i (x i)) Q e' (G d) (fun j => hQ j _ (hG d hd j)),
        smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [smul_eq_mul]; ring
    rw [Finsupp.sum]
    refine (Finset.sum_congr rfl (fun d hd => congrArg (τ d * ·) (hM d hd))).trans ?_
    simp_rw [Finsupp.sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring
  have memf : ∀ d ∈ τ.support, ∀ i, f d i ∈ Wf i := fun d hd i =>
    Submodule.subset_span (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inl ⟨d, hd, rfl⟩)
  have memf' : ∀ d ∈ τ.support, ∀ i, f' d i ∈ Wf i := fun d hd i =>
    Submodule.subset_span (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inr ⟨d, hd, rfl⟩)
  have memg : ∀ d ∈ τ.support, ∀ j, g d j ∈ Wg j := fun d hd j =>
    Submodule.subset_span (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inl ⟨d, hd, rfl⟩)
  have memg' : ∀ d ∈ τ.support, ∀ j, g' d j ∈ Wg j := fun d hd j =>
    Submodule.subset_span (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inr ⟨d, hd, rfl⟩)
  rw [key f g memf memg, key f' g' memf' memg']
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [hfg x y]

end GlobalTheory
end
