import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

section
noncomputable section

namespace GlobalTheory.ThK.PolynomialMatching

open scoped TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def PolMatchOn (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (T : Finset (Pl F)) (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) : Prop :=
  ∃ (m m' : ℕ) (f : Fin m → SInf F _) (φ : Fin m → ∀ v : Pl F, (_ → Fv F v) → ℂ)
    (f' : Fin m' → SInf F _) (φ' : Fin m' → ∀ v : Pl F, (_ → Fv F v) → ℂ),
    (∀ i, f i ∈ G.M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = G.M.vac v) ∧
    (∀ j, f' j ∈ G.M'.Pol B.ψ B.emb ∧ (∀ v, φ' j v ∈ SB _) ∧ ∀ v ∉ T, φ' j v = G.M'.vac v) ∧
    Φ = ∑ i, pure (f i) (φ i) ∧ Φ' = ∑ j, pure (f' j) (φ' j) ∧
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v))

theorem polMatch_iff (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) :
    PolMatch B G X R Rf Φ Φ' ↔ ∃ T : Finset (Pl F), X.T ⊆ T ∧ PolMatchOn B G X R Rf T Φ Φ' := Iff.rfl

theorem I'_sum {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {ι : Type} (s : Finset ι) (Ψ : ι → (Fin a' × Fin (a + a') → AF F) → ℂ)
    (hΨ : ∀ j ∈ s, Ψ j ∈ schA F (Fin a' × Fin (a + a'))) (hc : ∀ j ∈ s, G.M'.Conv om' (Ψ j)) (h : UA σ G.W.J) :
    G.M'.I om' (∑ j ∈ s, Ψ j) h = ∑ j ∈ s, G.M'.I om' (Ψ j) h := by
  have e : ∀ g, theta om' (∑ j ∈ s, Ψ j) g h = ∑ j ∈ s, theta om' (Ψ j) g h := by
    intro g
    simp only [theta, map_sum]
    have hm : ∀ j ∈ s, om' (g, h) (Ψ j) ∈ schA F (Fin a' × Fin (a + a')) :=
      fun j hj => hT.weil'.isUSplitting.pres _ _ (hΨ j hj)
    induction s using Finset.induction_on with
    | empty => simp [thetaSum]
    | insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk,
        thetaSum_add F (hm k (Finset.mem_insert_self _ _)) (Submodule.sum_mem _ fun j hj => hm j (Finset.mem_insert_of_mem hj)),
        ih (fun j hj => hΨ j (Finset.mem_insert_of_mem hj)) (fun j hj => hc j (Finset.mem_insert_of_mem hj))
          (fun j hj => hm j (Finset.mem_insert_of_mem hj))]
  simp only [Model.I, e]
  exact integral_finset_sum s fun j hj => hc j hj h

end GlobalTheory.ThK.PolynomialMatching
end
end

section
noncomputable section

open scoped TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK.PolynomialMatching

section Extend

variable {ι : Type} {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

def padFam (T S : Finset ι) (c : ∀ i, M i) (x : ∀ u : T, M u) : ∀ u : S, M u :=
  fun u => if h : u.1 ∈ T then x ⟨u.1, h⟩ else c u.1

theorem padFam_update (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) [DecidableEq T] [DecidableEq S]
    (x : ∀ u : T, M u) (i : T) (y : M i) :
    padFam T S c (Function.update x i y) = Function.update (padFam T S c x) ⟨i.1, hTS i.2⟩ y := by
  funext u
  by_cases h : u.1 ∈ T
  · by_cases hu : u.1 = i.1
    · obtain ⟨u, hu'⟩ := u
      obtain ⟨i, hi⟩ := i
      simp only at hu
      subst hu
      simp [padFam, h]
    · have h1 : (⟨u.1, h⟩ : T) ≠ i := fun e => hu (by rw [← e])
      have h2 : u ≠ ⟨i.1, hTS i.2⟩ := fun e => hu (by rw [e])
      simp only [padFam, h, dif_pos, Function.update_of_ne h1, Function.update_of_ne h2]
  · have h2 : u ≠ ⟨i.1, hTS i.2⟩ := fun e => h (by rw [e]; exact i.2)
    simp only [padFam, h, dif_neg, not_false_eq_true, Function.update_of_ne h2]

def padMultilinear (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) :
    MultilinearMap ℂ (fun u : T => M u) (⨂[ℂ] u : S, M u) where
  toFun x := PiTensorProduct.tprod ℂ (padFam T S c x)
  map_update_add' x i y z := by
    simp only [padFam_update T S hTS c]
    exact (PiTensorProduct.tprod ℂ).map_update_add _ _ _ _
  map_update_smul' x i r y := by
    simp only [padFam_update T S hTS c]
    exact (PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _

def padTensor (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) :
    (⨂[ℂ] u : T, M u) →ₗ[ℂ] ⨂[ℂ] u : S, M u :=
  PiTensorProduct.lift (padMultilinear T S hTS c)

theorem padTensor_tprod (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) (x : ∀ u : T, M u) :
    padTensor T S hTS c (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ (padFam T S c x) := by
  simp [padTensor, padMultilinear]

end Extend

theorem polMatchOn_insert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a') (v : Pl F),
    Rf.p v (G.M.vac v) = Rf.p' v (G.M'.vac v) → ∀ (T : Finset (Pl F)) (Φ : (Fin a × Fin (a + a') → AF F) → ℂ)
    (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T Φ Φ' →
    GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf (insert v T) Φ Φ' := by
  intro F E _ _ _ _ _ σ B a a' G X R Rf v hv T Φ Φ' hM
  obtain ⟨m, m', f, φ, f', φ', hφ, hφ', hΦ, hΦ', hsum⟩ := hM
  refine ⟨m, m', f, φ, f', φ',
    fun i => ⟨(hφ i).1, (hφ i).2.1, fun w hw => (hφ i).2.2 w fun h => hw (Finset.mem_insert_of_mem h)⟩,
    fun j => ⟨(hφ' j).1, (hφ' j).2.1, fun w hw => (hφ' j).2.2 w fun h => hw (Finset.mem_insert_of_mem h)⟩,
    hΦ, hΦ', ?_⟩
  let c : ∀ u, Rf.Pi u := fun u => Rf.p u (G.M.vac u)
  have key := congrArg (LinearMap.lTensor R.Pi (padTensor T (insert v T) (Finset.subset_insert _ _) c)) hsum
  simp only [map_sum, LinearMap.lTensor_tmul, padTensor_tprod] at key
  have e1 : ∀ i, padFam T (insert v T) c (fun u : T => Rf.p u (φ i u)) =
      fun u : (insert v T : Finset (Pl F)) => Rf.p u (φ i u) := by
    intro i
    funext u
    by_cases h : u.1 ∈ T
    · simp [padFam, h]
    · simp [padFam, h, c, (hφ i).2.2 u.1 h]
  have e2 : ∀ j, padFam T (insert v T) c (fun u : T => Rf.p' u (φ' j u)) =
      fun u : (insert v T : Finset (Pl F)) => Rf.p' u (φ' j u) := by
    intro j
    funext u
    by_cases h : u.1 ∈ T
    · simp [padFam, h]
    · obtain ⟨u, hu⟩ := u
      have huv : u = v := by
        rcases Finset.mem_insert.1 hu with h' | h'
        · exact h'
        · exact absurd h' h
      subst huv
      simp [padFam, h, c, (hφ' j).2.2 u h, hv]
  simp only [e1, e2] at key
  exact key

end GlobalTheory.ThK.PolynomialMatching
end
end
