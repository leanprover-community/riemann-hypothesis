import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankAddValuationIntegerSubmoduleEqFinrankSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootProdLinearFactorsLatticeFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEigenFiltrationPiecesAddValInt

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

noncomputable section
namespace GlobalTheory.HerbCore
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {S : Type} [Fintype S] [DecidableEq S]
  (a : S → Int0 v) {N : ℕ} (Fil : Submodule (RS a) (Fin N → RS a))

def compSpan (s : S) : Submodule C (Fin N → C) :=
  Submodule.span C ((fun (x : Fin N → Int0 v) (i : Fin N) => (x i : C)) ''
    (eigQuot a Fil s : Set (Fin N → Int0 v)))

abbrev CompProd (τ : S) : Type := ∀ s : {s // s ≠ τ}, compSpan v a Fil s

def compMap (τ : S) : filKer a Fil τ →ₗ[Int0 v] CompProd v a Fil τ where
  toFun x s := ⟨fun i => ((ev a s.1 ((x : Fin N → RS a) i) : Int0 v) : C),
    Submodule.subset_span ⟨comp a N s.1 x, ⟨x, x.2.1, rfl⟩, rfl⟩⟩
  map_add' x y := by
    funext s; apply Subtype.ext; funext i; simp
  map_smul' c x := by
    funext s; apply Subtype.ext; funext i
    simp [Algebra.smul_def, ← AdjoinRoot.algebraMap_eq, AlgHom.commutes]
    exact Or.inl rfl

def diagMul (τ : S) : CompProd v a Fil τ →ₗ[C] CompProd v a Fil τ :=
  LinearMap.pi fun s => ((a s.1 : C) - (a τ : C)) • LinearMap.proj s

end GlobalTheory.HerbCore

noncomputable section
namespace GlobalTheory.HerbCore
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {S : Type} [Fintype S] [DecidableEq S]
  {a : S → Int0 v} {N : ℕ} {Fil : Submodule (RS a) (Fin N → RS a)}

theorem mulR_apply (r : RS a) (x : Fin N → RS a) : mulR a N r x = r • x := rfl

theorem mulR_mem_filKer (τ : S) {x : Fin N → RS a} (hx : x ∈ filKer a Fil τ) :
    mulR a N (lin a τ) x ∈ filKer a Fil τ := by
  rw [filKer, Submodule.mem_inf] at hx ⊢
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [mulR_apply]; exact Fil.smul_mem _ h1
  · rw [LinearMap.mem_ker] at h2 ⊢
    rw [mulR_apply] at h2
    rw [mulR_apply, mulR_apply, smul_smul, mul_comm, ← smul_smul, h2, smul_zero]

theorem compMap_mulR (τ : S) (x : Fin N → RS a) (hx : x ∈ filKer a Fil τ) :
    compMap v a Fil τ ⟨mulR a N (lin a τ) x, mulR_mem_filKer τ hx⟩ =
      diagMul v a Fil τ (compMap v a Fil τ ⟨x, hx⟩) := by
  funext s; apply Subtype.ext; funext i
  simp [compMap, diagMul, mulR_apply, ev_lin]

theorem det_diagMul (τ : S) :
    LinearMap.det (diagMul v a Fil τ) =
      ∏ s : {s // s ≠ τ}, ((a s.1 : C) - (a τ : C)) ^ eigRank v a Fil s.1 := by
  let bs : ∀ s : {s // s ≠ τ}, Basis (Fin (finrank C (compSpan v a Fil s.1))) C (compSpan v a Fil s.1) :=
    fun s => Module.finBasis C _
  let B := Pi.basis bs
  rw [← LinearMap.det_toMatrix B]
  have hM : LinearMap.toMatrix B B (diagMul v a Fil τ) =
      Matrix.diagonal (fun σ => (a σ.1.1 : C) - (a τ : C)) := by
    ext σ ρ
    rw [LinearMap.toMatrix_apply]
    have : diagMul v a Fil τ (B ρ) = ((a ρ.1.1 : C) - (a τ : C)) • B ρ := by
      funext s
      simp only [B, Pi.basis_apply, diagMul, LinearMap.pi_apply, LinearMap.smul_apply,
        LinearMap.proj_apply, Pi.smul_apply]
      by_cases h : s = ρ.1
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    rw [this, map_smul, B.repr_self, Matrix.diagonal_apply, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases h : ρ = σ
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [hM, Matrix.det_diagonal, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

end GlobalTheory.HerbCore

noncomputable section
namespace GlobalTheory.HerbCore
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {S : Type} [Fintype S] [DecidableEq S]
  {a : S → Int0 v} {N : ℕ} {Fil : Submodule (RS a) (Fin N → RS a)}

theorem lin_eq_mk (s : S) : lin a s = AdjoinRoot.mk _ (X - Polynomial.C (a s)) := by
  simp [lin, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

theorem prod_lin : ∏ s, lin a s = 0 := by
  simp_rw [lin_eq_mk]
  rw [← map_prod]
  exact AdjoinRoot.mk_self

theorem cofac_mul_cofac {s τ : S} (h : s ≠ τ) : cofac a τ * cofac a s = 0 := by
  have h1 : lin a s * ∏ t ∈ (Finset.univ.erase τ).erase s, lin a t = cofac a τ :=
    Finset.mul_prod_erase _ (lin a) (Finset.mem_erase.mpr ⟨h, Finset.mem_univ s⟩)
  have h2 : cofac a s * lin a s = ∏ t, lin a t :=
    Finset.prod_erase_mul _ (lin a) (Finset.mem_univ s)
  rw [← h1, mul_comm (lin a s), mul_assoc, mul_comm (lin a s), h2, prod_lin, mul_zero]

theorem ev_cofac (t s : S) : ev a t (cofac a s) = ∏ u ∈ Finset.univ.erase s, (a t - a u) := by
  simp [cofac, map_prod, ev_lin]

theorem ev_cofac_of_ne {t s : S} (h : t ≠ s) : ev a t (cofac a s) = 0 := by
  rw [ev_cofac]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h, Finset.mem_univ t⟩) (sub_self _)

theorem ev_cofac_self_ne_zero (ha : Function.Injective a) (s : S) : ev a s (cofac a s) ≠ 0 := by
  rw [ev_cofac]
  refine Finset.prod_ne_zero_iff.mpr fun u hu => sub_ne_zero.mpr fun h => ?_
  exact (Finset.mem_erase.mp hu).1 (ha h).symm

theorem ev_mk (s : S) (q : (Int0 v)[X]) : ev a s (AdjoinRoot.mk _ q) = q.eval (a s) := by
  simp [ev, AdjoinRoot.liftAlgHom, AdjoinRoot.lift_mk, Polynomial.eval₂_eq_eval_map]

theorem eq_zero_of_ev (ha : Function.Injective a) (r : RS a) (h : ∀ s, ev a s r = 0) : r = 0 := by
  have hmon : (∏ s, (X - Polynomial.C (a s)) : (Int0 v)[X]).Monic :=
    monic_prod_of_monic _ _ fun s _ => monic_X_sub_C _
  have hdeg : (∏ s, (X - Polynomial.C (a s)) : (Int0 v)[X]).natDegree = Fintype.card S := by
    rw [natDegree_prod_of_monic _ _ (fun s _ => monic_X_sub_C _)]; simp
  induction r using AdjoinRoot.induction_on with
  | ih p =>
    have hmk : AdjoinRoot.mk (∏ s, (X - Polynomial.C (a s))) p =
        AdjoinRoot.mk (∏ s, (X - Polynomial.C (a s))) (p %ₘ ∏ s, (X - Polynomial.C (a s))) := by
      rw [AdjoinRoot.mk_eq_mk]
      refine ⟨p /ₘ ∏ s, (X - Polynomial.C (a s)), ?_⟩
      have := modByMonic_add_div p (∏ s, (X - Polynomial.C (a s)))
      linear_combination this.symm
    rw [hmk] at h ⊢
    have hev : ∀ s, (p %ₘ ∏ s, (X - Polynomial.C (a s))).eval (a s) = 0 := by
      intro s
      rw [← ev_mk]; exact h s
    by_cases hq : p %ₘ ∏ s, (X - Polynomial.C (a s)) = 0
    · rw [hq, map_zero]
    · have hlt : (p %ₘ ∏ s, (X - Polynomial.C (a s))).natDegree < Fintype.card S := by
        rw [← hdeg]
        exact natDegree_lt_natDegree hq (degree_modByMonic_lt _ hmon)
      rw [eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ ha hev hlt, map_zero]

theorem eq_zero_of_cofac (ha : Function.Injective a) (τ : S) (r : RS a) (hP : cofac a τ * r = 0)
    (h : ∀ s, s ≠ τ → ev a s r = 0) : r = 0 := by
  refine eq_zero_of_ev ha r fun s => ?_
  by_cases hs : s = τ
  · subst hs
    have := congrArg (ev a s) hP
    rw [map_mul, map_zero] at this
    exact (mul_eq_zero.mp this).resolve_left (ev_cofac_self_ne_zero ha s)
  · exact h s hs

theorem mem_filKer_iff (τ : S) (x : Fin N → RS a) :
    x ∈ filKer a Fil τ ↔ x ∈ Fil ∧ cofac a τ • x = 0 := by
  rw [filKer, Submodule.mem_inf, LinearMap.mem_ker]; rfl

theorem mulR_injOn (ha : Function.Injective a) (τ : S) {x : Fin N → RS a} (hx : x ∈ filKer a Fil τ)
    (h0 : mulR a N (lin a τ) x = 0) : x = 0 := by
  rw [mem_filKer_iff] at hx
  funext i
  refine eq_zero_of_cofac ha τ (x i) (congrFun hx.2 i) fun s hs => ?_
  have := congrArg (ev a s) (congrFun h0 i)
  rw [mulR_apply, Pi.smul_apply, smul_eq_mul, map_mul, ev_lin, Pi.zero_apply, map_zero] at this
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr fun h => hs (ha h))

theorem compMap_injective (ha : Function.Injective a) (τ : S) :
    Function.Injective (compMap v a Fil τ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hx2 := ((mem_filKer_iff τ x.1).mp x.2).2
  apply Subtype.ext
  funext i
  refine eq_zero_of_cofac ha τ _ (congrFun hx2 i) fun s hs => ?_
  have := congrArg (fun p => ((p ⟨s, hs⟩ : compSpan v a Fil s) : Fin N → C) i) hx
  simpa [compMap] using this

end GlobalTheory.HerbCore

noncomputable section
namespace GlobalTheory.HerbCore
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {S : Type} [Fintype S] [DecidableEq S]
  {a : S → Int0 v} {N : ℕ} {Fil : Submodule (RS a) (Fin N → RS a)}

theorem filKer_finite_free (hsat : ∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil)
    (τ : S) : Module.Finite (Int0 v) (filKer a Fil τ) ∧ Module.Free (Int0 v) (filKer a Fil τ) := by
  have hmon : (∏ s, (X - Polynomial.C (a s)) : (Int0 v)[X]).Monic :=
    monic_prod_of_monic _ _ fun s _ => monic_X_sub_C _
  haveI : Module.Finite (Int0 v) (RS a) := hmon.finite_adjoinRoot
  haveI : Module.Free (Int0 v) (RS a) := hmon.free_adjoinRoot
  haveI : Module.Free (Int0 v) (Fin N → RS a) := inferInstance
  haveI : Module.IsTorsionFree (Int0 v) (Fin N → RS a) := Module.Free.instIsTorsionFree _ _
  have hsat' : GlobalTheory.IsSaturatedSubmodule (filKer a Fil τ) := by
    rw [GlobalTheory.isSaturatedSubmodule_iff]
    intro c hc x hx
    rw [mem_filKer_iff] at hx ⊢
    refine ⟨hsat c x hc hx.1, ?_⟩
    have h2 : c • (cofac a τ • x) = 0 := by rw [smul_comm]; exact hx.2
    exact (smul_eq_zero.mp h2).resolve_left hc
  exact ⟨hsat'.finite_of_valuationRing, hsat'.free_of_valuationRing⟩

theorem span_range_compMap (ha : Function.Injective a) (τ : S) :
    Submodule.span C (Set.range (compMap v a Fil τ)) = ⊤ := by
  set W := Submodule.span C (Set.range (compMap v a Fil τ)) with hW
  have key : ∀ (s : {s // s ≠ τ}) (y : Fin N → Int0 v) (hy : y ∈ eigQuot a Fil s.1)
      (hy' : (fun i => (y i : C)) ∈ compSpan v a Fil s.1),
      Pi.single (M := fun t : {t // t ≠ τ} => compSpan v a Fil t.1) s ⟨fun i => (y i : C), hy'⟩ ∈ W := by
    intro s y hy hy'
    obtain ⟨x0, hx0, rfl⟩ := hy
    have hz : cofac a s.1 • x0 ∈ filKer a Fil τ := by
      rw [mem_filKer_iff]
      refine ⟨Fil.smul_mem _ hx0, ?_⟩
      rw [smul_smul, cofac_mul_cofac s.2, zero_smul]
    have hd : ((ev a s.1 (cofac a s.1) : Int0 v) : C) ≠ 0 := by
      rw [Ne, ZeroMemClass.coe_eq_zero]; exact ev_cofac_self_ne_zero ha s.1
    have hval : compMap v a Fil τ ⟨cofac a s.1 • x0, hz⟩ =
        ((ev a s.1 (cofac a s.1) : Int0 v) : C) •
          Pi.single (M := fun t : {t // t ≠ τ} => compSpan v a Fil t.1) s
            ⟨fun i => ((comp a N s.1 x0) i : C), hy'⟩ := by
      funext t; apply Subtype.ext; funext i
      by_cases h : t = s
      · subst h; simp [compMap]; exact Or.inl rfl
      · have h' : t.1 ≠ s.1 := fun e => h (Subtype.ext e)
        simp [compMap, Pi.single_eq_of_ne h, ev_cofac_of_ne h']
    have : Pi.single (M := fun t : {t // t ≠ τ} => compSpan v a Fil t.1) s
        ⟨fun i => ((comp a N s.1 x0) i : C), hy'⟩ =
        (((ev a s.1 (cofac a s.1) : Int0 v) : C))⁻¹ • compMap v a Fil τ ⟨cofac a s.1 • x0, hz⟩ := by
      rw [hval, smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [this]
    exact W.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)
  have hsingle : ∀ (s : {s // s ≠ τ}) (w : compSpan v a Fil s.1),
      Pi.single (M := fun t : {t // t ≠ τ} => compSpan v a Fil t.1) s w ∈ W := by
    intro s w
    obtain ⟨w, hw⟩ := w
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact key s y hy _
    | zero =>
      have : (⟨0, Submodule.zero_mem _⟩ : compSpan v a Fil s.1) = 0 := rfl
      rw [this, Pi.single_zero]; exact W.zero_mem
    | add x z hx hz ihx ihz =>
      have : (⟨x + z, Submodule.add_mem _ hx hz⟩ : compSpan v a Fil s.1) = ⟨x, hx⟩ + ⟨z, hz⟩ := rfl
      rw [this, Pi.single_add]; exact W.add_mem ihx ihz
    | smul c x hx ih =>
      have : (⟨c • x, Submodule.smul_mem _ c hx⟩ : compSpan v a Fil s.1) = c • ⟨x, hx⟩ := rfl
      rw [this, Pi.single_smul]; exact W.smul_mem c ih
  rw [eq_top_iff]
  intro p _
  rw [← Finset.univ_sum_single p]
  exact W.sum_mem fun s _ => hsingle s (p s)

end GlobalTheory.HerbCore

noncomputable section
namespace GlobalTheory.HerbCore

theorem relLen_lin_filKer : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ∃ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ ∧ RelLen v ((filKer a Fil τ).map (mulR a N (lin a τ))) (filKer a Fil τ) r := by
  intro C _ v S _ _ a ha N Fil hsat τ
  set K := filKer a Fil τ with hK
  obtain ⟨hfin, hfree⟩ := filKer_finite_free (v := v) (a := a) hsat τ
  let n := finrank (Int0 v) K
  let b : Basis (Fin n) (Int0 v) K := Module.finBasis _ _
  let T : K →ₗ[Int0 v] K := (mulR a N (lin a τ)).restrict (fun x hx => mulR_mem_filKer τ hx)
  have hT : ∀ x : K, (T x : Fin N → RS a) = mulR a N (lin a τ) x := fun x => rfl
  let g : K →ₗ[Int0 v] (Fin N → RS a) := (mulR a N (lin a τ)).comp K.subtype
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (mulR_injOn ha τ x.2 hx)
  have hrange : LinearMap.range g = K.map (mulR a N (lin a τ)) := by
    simp only [g, LinearMap.range_comp, Submodule.range_subtype]
  let e : K ≃ₗ[Int0 v] K.map (mulR a N (lin a τ)) :=
    (LinearEquiv.ofInjective g hg).trans (LinearEquiv.ofEq _ _ hrange)
  let A := LinearMap.toMatrix b b T

  let Φ := compMap v a Fil τ
  have hli : LinearIndependent C (Φ ∘ b) :=
    (LinearIndependent.iff_fractionRing (Int0 v) C).mp
      (b.linearIndependent.map' Φ (LinearMap.ker_eq_bot.mpr (compMap_injective ha τ)))
  have hsp : ⊤ ≤ Submodule.span C (Set.range (Φ ∘ b)) := by
    rw [← span_range_compMap (v := v) (Fil := Fil) ha τ, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul, ← algebraMap_smul C]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let β : Basis (Fin n) C (CompProd v a Fil τ) := Basis.mk hli hsp
  have hmat : LinearMap.toMatrix β β (diagMul v a Fil τ) = A.map (algebraMap (Int0 v) C) := by
    ext i k
    rw [LinearMap.toMatrix_apply, Matrix.map_apply]
    have h1 : diagMul v a Fil τ (β k) = ∑ j, (algebraMap (Int0 v) C (A j k)) • β j := by
      rw [Basis.mk_apply, Function.comp_apply]
      have := compMap_mulR (v := v) τ (b k : Fin N → RS a) (b k).2
      simp only [Subtype.coe_eta] at this
      rw [← this]
      have h2 : (⟨mulR a N (lin a τ) (b k), mulR_mem_filKer τ (b k).2⟩ : K) = ∑ j, A j k • b j := by
        show T (b k) = _
        conv_lhs => rw [← b.sum_repr (T (b k))]
        simp [A, LinearMap.toMatrix_apply]
      rw [h2, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, algebraMap_smul, Basis.mk_apply]
      rfl
    rw [h1, β.repr_sum_self]
  have hdetC : ((A.det : Int0 v) : C) = ∏ s : {s // s ≠ τ}, ((a s.1 : C) - (a τ : C)) ^ eigRank v a Fil s.1 := by
    rw [← det_diagMul, ← LinearMap.det_toMatrix β, hmat]
    exact RingHom.map_det (algebraMap (Int0 v) C) A
  have hne : ((A.det : Int0 v) : C) ≠ 0 := by
    rw [hdetC]
    refine Finset.prod_ne_zero_iff.mpr fun s _ => pow_ne_zero _ (sub_ne_zero.mpr ?_)
    intro h
    exact s.2 (ha (Subtype.ext h))
  have hval : v ((A.det : Int0 v) : C) = yExp v a Fil τ := by
    have hprod : ∀ (ι : Type) (s : Finset ι) (f : ι → C), v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
      intro ι s f
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, v.map_mul, ih]
    rw [hdetC, hprod, yExp]
    rw [Finset.sum_subtype (Finset.univ.erase τ) (p := fun s => s ≠ τ) (by simp)
      (fun s => eigRank v a Fil s • v ((a s : C) - (a τ : C)))]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [AddValuation.map_pow]
  have htop : v ((A.det : Int0 v) : C) ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]; exact hne
  refine ⟨(v ((A.det : Int0 v) : C)).untop htop, by rw [WithTop.coe_untop, hval], n, b, b.map e, A, fun k => ?_, by rw [WithTop.coe_untop]⟩
  rw [Basis.map_apply]
  have : ((e (b k) : K.map (mulR a N (lin a τ))) : Fin N → RS a) = (T (b k) : Fin N → RS a) := rfl
  have h3 : T (b k) = ∑ i, A i k • b i := by
    conv_lhs => rw [← b.sum_repr (T (b k))]
    simp [A, LinearMap.toMatrix_apply]
  rw [this, h3, Submodule.coe_sum]
  simp

end GlobalTheory.HerbCore
end
end
end
end
end
end

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relLength_filtrationInterKerCofactor_linearFactor : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ∃ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ ∧ RelLen v ((filKer a Fil τ).map (mulR a N (lin a τ))) (filKer a Fil τ) r := by
  atlas_forward_decl GlobalTheory.HerbCore.relLen_lin_filKer
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

noncomputable section
namespace GlobalTheory.HerbDet

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem det_ne_zero_of_linearIndependent {n : ℕ} (u : Fin n → (Fin n → Int0 v))
    (hu : LinearIndependent (Int0 v) u) : (Matrix.of u).det ≠ 0 := by
  intro h0
  obtain ⟨w, hw, hw0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  apply hw
  have hs : ∑ i, w i • u i = 0 := by
    funext j
    have := congr_fun hw0 j
    simpa only [Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, Matrix.of_apply] using this
  exact funext (Fintype.linearIndependent_iff.1 hu w hs)

variable {S : Type} [Fintype S] [DecidableEq S] {a : S → Int0 v} {N : ℕ}
  {Fil : Submodule (RS a) (Fin N → RS a)} {τ : S}

theorem mem_preEig_of_proj_mem
    (hE8 : (preEig a Fil τ).map (proj a Fil) = eigSub a τ ((Fin N → RS a) ⧸ Fil))
    (hE10 : Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ) (z : Fin N → RS a)
    (hz : proj a Fil z ∈ eigSub a τ ((Fin N → RS a) ⧸ Fil)) : z ∈ preEig a Fil τ := by
  rw [← hE8] at hz
  obtain ⟨y, hy, hyz⟩ := hz
  have hzy : z - y ∈ Fil.restrictScalars (Int0 v) := by
    have h0 : proj a Fil (z - y) = 0 := by rw [map_sub, hyz, sub_self]
    exact (Submodule.Quotient.mk_eq_zero _).1 h0
  simpa using add_mem (hE10 hzy) hy

theorem linearIndependent_comb {ι κ : Type} [Fintype ι] [Fintype κ]
    (hE4 : preEig a Fil τ ⊓ LinearMap.ker (comp a N τ) ≤ Fil.restrictScalars (Int0 v))
    (hE10 : Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ)
    (l : Basis ι (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)))
    (x : ι → (Fin N → RS a)) (hx : ∀ i, proj a Fil (x i) = (l i : (Fin N → RS a) ⧸ Fil))
    (hxX : ∀ i, x i ∈ preEig a Fil τ)
    (f : Basis κ (Int0 v) (eigQuot a Fil τ)) :
    LinearIndependent (Int0 v)
      (Sum.elim (fun i => comp a N τ (x i)) (fun j => (f j : Fin N → Int0 v))) := by
  rw [Fintype.linearIndependent_iff]
  intro w hw
  rw [Fintype.sum_sum_type] at hw
  simp only [Sum.elim_inl, Sum.elim_inr] at hw
  have hmem : ∑ j, w (Sum.inr j) • (f j : Fin N → Int0 v) ∈
      (Fil.restrictScalars (Int0 v)).map (comp a N τ) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (f j).2
  obtain ⟨φ, hφ, hφe⟩ := hmem
  have hzX : ∑ i, w (Sum.inl i) • x i ∈ preEig a Fil τ :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hxX i)
  have hcomp : comp a N τ (∑ i, w (Sum.inl i) • x i + φ) = 0 := by
    rw [map_add, map_sum, hφe]
    simpa [map_smul] using hw
  have hzφ : ∑ i, w (Sum.inl i) • x i + φ ∈ Fil.restrictScalars (Int0 v) :=
    hE4 ⟨add_mem hzX (hE10 hφ), hcomp⟩
  have hz : ∑ i, w (Sum.inl i) • x i ∈ Fil.restrictScalars (Int0 v) := by
    simpa using sub_mem hzφ hφ
  have hprojz : proj a Fil (∑ i, w (Sum.inl i) • x i) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 hz
  have hl : ∑ i, w (Sum.inl i) • l i = 0 := by
    apply Subtype.ext
    rw [map_sum] at hprojz
    simp only [map_smul, hx] at hprojz
    simpa using hprojz
  have hα := Fintype.linearIndependent_iff.1 l.linearIndependent _ hl
  have hf : ∑ j, w (Sum.inr j) • f j = 0 := by
    apply Subtype.ext
    simp only [hα, zero_smul, Finset.sum_const_zero, zero_add] at hw
    simpa using hw
  have hβ := Fintype.linearIndependent_iff.1 f.linearIndependent _ hf
  rintro (i | j)
  · exact hα i
  · exact hβ j

theorem span_comb {ι κ : Type} [Fintype ι] [Fintype κ]
    (hE8 : (preEig a Fil τ).map (proj a Fil) = eigSub a τ ((Fin N → RS a) ⧸ Fil))
    (l : Basis ι (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)))
    (x : ι → (Fin N → RS a)) (hx : ∀ i, proj a Fil (x i) = (l i : (Fin N → RS a) ⧸ Fil))
    (f : Basis κ (Int0 v) (eigQuot a Fil τ)) (y : Fin N → Int0 v)
    (hy : y ∈ (preEig a Fil τ).map (comp a N τ)) :
    ∃ c : ι ⊕ κ → Int0 v, ∑ s, c s •
      (Sum.elim (fun i => comp a N τ (x i)) (fun j => (f j : Fin N → Int0 v))) s = y := by
  obtain ⟨z, hz, rfl⟩ := hy
  have hpz : proj a Fil z ∈ eigSub a τ ((Fin N → RS a) ⧸ Fil) := by
    rw [← hE8]; exact Submodule.mem_map_of_mem hz
  have hl := congrArg Subtype.val (l.sum_repr ⟨proj a Fil z, hpz⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hl
  have hsum : proj a Fil (z - ∑ i, l.repr ⟨proj a Fil z, hpz⟩ i • x i) = 0 := by
    rw [map_sub, map_sum]
    simp only [map_smul, hx]
    rw [hl, sub_self]
  have hw : z - ∑ i, l.repr ⟨proj a Fil z, hpz⟩ i • x i ∈ Fil.restrictScalars (Int0 v) :=
    (Submodule.Quotient.mk_eq_zero _).1 hsum
  have hfw : comp a N τ (z - ∑ i, l.repr ⟨proj a Fil z, hpz⟩ i • x i) ∈ eigQuot a Fil τ :=
    Submodule.mem_map_of_mem hw
  have h2 := congrArg Subtype.val (f.sum_repr ⟨_, hfw⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  refine ⟨Sum.elim (l.repr ⟨proj a Fil z, hpz⟩) (f.repr ⟨_, hfw⟩), ?_⟩
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have h3 : comp a N τ (z - ∑ i, l.repr ⟨proj a Fil z, hpz⟩ i • x i) =
      comp a N τ z - ∑ i, l.repr ⟨proj a Fil z, hpz⟩ i • comp a N τ (x i) := by
    simp only [map_sub, map_sum, map_smul]
  exact eq_sub_iff_add_eq'.1 (h2.trans h3)

end GlobalTheory.HerbDet

namespace GlobalTheory.HerbDet

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}
variable {S : Type} [Fintype S] [DecidableEq S] {a : S → Int0 v} {N : ℕ}
  {Fil : Submodule (RS a) (Fin N → RS a)} {τ : S}

theorem exists_basis_comb {ι κ : Type} [Fintype ι] [Fintype κ]
    (hE4 : preEig a Fil τ ⊓ LinearMap.ker (comp a N τ) ≤ Fil.restrictScalars (Int0 v))
    (hE8 : (preEig a Fil τ).map (proj a Fil) = eigSub a τ ((Fin N → RS a) ⧸ Fil))
    (hE10 : Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ)
    (l : Basis ι (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)))
    (x : ι → (Fin N → RS a)) (hx : ∀ i, proj a Fil (x i) = (l i : (Fin N → RS a) ⧸ Fil))
    (f : Basis κ (Int0 v) (eigQuot a Fil τ)) :
    ∃ b : Basis (ι ⊕ κ) (Int0 v) ((preEig a Fil τ).map (comp a N τ)),
      ∀ s, (b s : Fin N → Int0 v) =
        Sum.elim (fun i => comp a N τ (x i)) (fun j => (f j : Fin N → Int0 v)) s := by
  have hxX : ∀ i, x i ∈ preEig a Fil τ := fun i =>
    mem_preEig_of_proj_mem hE8 hE10 (x i) (by rw [hx i]; exact (l i).2)
  have hmem : ∀ s, Sum.elim (fun i => comp a N τ (x i)) (fun j => (f j : Fin N → Int0 v)) s ∈
      (preEig a Fil τ).map (comp a N τ) := by
    rintro (i | j)
    · exact Submodule.mem_map_of_mem (hxX i)
    · exact Submodule.map_mono hE10 (f j).2
  have hli := linearIndependent_comb hE4 hE10 l x hx hxX f
  have hli' : LinearIndependent (Int0 v)
      (fun s => (⟨_, hmem s⟩ : (preEig a Fil τ).map (comp a N τ))) := by
    apply LinearIndependent.of_comp ((preEig a Fil τ).map (comp a N τ)).subtype
    exact hli
  refine ⟨Basis.mk hli' ?_, fun s => by rw [Basis.mk_apply]⟩
  intro y _
  rw [Submodule.mem_span_range_iff_exists_fun]
  obtain ⟨c, hc⟩ := span_comb hE8 l x hx f y y.2
  exact ⟨c, Subtype.ext (by simpa using hc)⟩

theorem exists_basis_image {ι : Type} [Fintype ι]
    (hE6 : eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ) = ⊥)
    (h : Basis ι (Int0 v) (eigSub a τ (Fin N → RS a))) :
    ∃ b : Basis ι (Int0 v) ((eigSub a τ (Fin N → RS a)).map (comp a N τ)),
      ∀ k, (b k : Fin N → Int0 v) = comp a N τ (h k : Fin N → RS a) := by
  have hli : LinearIndependent (Int0 v) (fun k => comp a N τ (h k : Fin N → RS a)) := by
    rw [Fintype.linearIndependent_iff]
    intro w hw
    have hm : ((∑ k, w k • h k : eigSub a τ (Fin N → RS a)) : Fin N → RS a) ∈
        eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ) := by
      refine Submodule.mem_inf.2 ⟨Subtype.mem _, ?_⟩
      rw [LinearMap.mem_ker, Submodule.coe_sum, map_sum]
      simpa [map_smul] using hw
    rw [hE6, Submodule.mem_bot] at hm
    exact Fintype.linearIndependent_iff.1 h.linearIndependent w (Subtype.ext hm)
  have hmem : ∀ k, comp a N τ (h k : Fin N → RS a) ∈ (eigSub a τ (Fin N → RS a)).map (comp a N τ) :=
    fun k => Submodule.mem_map_of_mem (h k).2
  have hli' : LinearIndependent (Int0 v)
      (fun k => (⟨_, hmem k⟩ : (eigSub a τ (Fin N → RS a)).map (comp a N τ))) := by
    apply LinearIndependent.of_comp ((eigSub a τ (Fin N → RS a)).map (comp a N τ)).subtype
    exact hli
  refine ⟨Basis.mk hli' ?_, fun k => by rw [Basis.mk_apply]⟩
  rintro ⟨_, z, hz, rfl⟩ _
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨h.repr ⟨z, hz⟩, Subtype.ext ?_⟩
  have h1 := congrArg Subtype.val (h.sum_repr ⟨z, hz⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
  have h2 := congrArg (comp a N τ) h1
  simp only [map_sum, map_smul] at h2
  simpa using h2

theorem exists_basis_eigSub (d : Int0 v) (hd : d ≠ 0)
    (hE6 : eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ) = ⊥)
    (hE7 : (eigSub a τ (Fin N → RS a)).map (comp a N τ) =
      (⊤ : Submodule (Int0 v) (Fin N → Int0 v)).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) d)) :
    Nonempty (Basis (Fin N) (Int0 v) (eigSub a τ (Fin N → RS a))) := by
  have hex : ∀ i : Fin N, ∃ z ∈ eigSub a τ (Fin N → RS a),
      comp a N τ z = d • (Pi.single i 1 : Fin N → Int0 v) := by
    intro i
    have : d • (Pi.single i 1 : Fin N → Int0 v) ∈ (eigSub a τ (Fin N → RS a)).map (comp a N τ) := by
      rw [hE7]; exact ⟨Pi.single i 1, trivial, rfl⟩
    obtain ⟨z, hz, hze⟩ := this
    exact ⟨z, hz, hze⟩
  choose z hz hze using hex
  have hinj : ∀ y ∈ eigSub a τ (Fin N → RS a), comp a N τ y = 0 → y = 0 := by
    intro y hy hy0
    have : y ∈ eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ) := ⟨hy, hy0⟩
    rwa [hE6, Submodule.mem_bot] at this
  have hcomb : ∀ w : Fin N → Int0 v,
      comp a N τ (∑ i, w i • z i) = d • w := by
    intro w
    rw [map_sum]
    simp only [map_smul, hze]
    funext j
    simp [Finset.sum_apply, Pi.single_apply, mul_comm, mul_left_comm]
  have hli : LinearIndependent (Int0 v) (fun i => (⟨z i, hz i⟩ : eigSub a τ (Fin N → RS a))) := by
    rw [Fintype.linearIndependent_iff]
    intro w hw
    have h0 : ∑ i, w i • z i = 0 := by
      have := congrArg Subtype.val hw
      simpa using this
    have h1 : d • w = 0 := by rw [← hcomb, h0, map_zero]
    have h2 : w = 0 := (smul_eq_zero.1 h1).resolve_left hd
    intro i; rw [h2]; rfl
  refine ⟨Basis.mk hli ?_⟩
  rintro ⟨y, hy⟩ _
  rw [Submodule.mem_span_range_iff_exists_fun]
  have hy' : comp a N τ y ∈ (eigSub a τ (Fin N → RS a)).map (comp a N τ) :=
    Submodule.mem_map_of_mem hy
  rw [hE7] at hy'
  obtain ⟨u, -, hu⟩ := hy'
  refine ⟨u, Subtype.ext ?_⟩
  have hmem : y - ∑ i, u i • z i ∈ eigSub a τ (Fin N → RS a) :=
    sub_mem hy (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hz i))
  have hc : comp a N τ (y - ∑ i, u i • z i) = 0 := by
    rw [map_sub, hcomb, ← hu]; simp
  have := hinj _ hmem hc
  rw [sub_eq_zero] at this
  simpa using this.symm

end GlobalTheory.HerbDet

namespace GlobalTheory.HerbDet

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}
variable {S : Type} [Fintype S] [DecidableEq S] {a : S → Int0 v} {N : ℕ}
  {Fil : Submodule (RS a) (Fin N → RS a)} {τ : S}

theorem det_eq_mul_of_relLen {X' X : Submodule (Int0 v) (Fin N → Int0 v)} (hle : X' ≤ X) {r : ℝ}
    (hRL : RelLen v X' X r) (bX : Basis (Fin N) (Int0 v) X) (bX' : Basis (Fin N) (Int0 v) X') :
    ∃ c : C, v c = r ∧
      (Matrix.of fun k : Fin N => (bX k : Fin N → Int0 v)).det ≠ 0 ∧
      ((Matrix.of fun k : Fin N => (bX' k : Fin N → Int0 v)).det : C) =
        c * ((Matrix.of fun k : Fin N => (bX k : Fin N → Int0 v)).det : C) := by
  let A : Matrix (Fin N) (Fin N) (Int0 v) := fun i k => bX.repr ⟨(bX' k : Fin N → Int0 v), hle (bX' k).2⟩ i
  have hA : ∀ k, ((bX' k : Fin N → Int0 v)) = ∑ i, A i k • (bX i : Fin N → Int0 v) := by
    intro k
    have := congrArg Subtype.val (bX.sum_repr ⟨(bX' k : Fin N → Int0 v), hle (bX' k).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hM : (Matrix.of fun k : Fin N => (bX' k : Fin N → Int0 v)) =
      A.transpose * Matrix.of fun k : Fin N => (bX k : Fin N → Int0 v) := by
    ext k j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    rw [hA k, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  have hli : LinearIndependent (Int0 v) (fun k => (bX k : Fin N → Int0 v)) :=
    bX.linearIndependent.map' X.subtype (Submodule.ker_subtype _)
  have hli' : LinearIndependent (Int0 v) (fun k => (bX' k : Fin N → Int0 v)) :=
    bX'.linearIndependent.map' X'.subtype (Submodule.ker_subtype _)
  have hM0 := det_ne_zero_of_linearIndependent _ hli
  have hM0' := det_ne_zero_of_linearIndependent _ hli'
  have hA0 : A.det ≠ 0 := by
    intro h0
    apply hM0'
    rw [hM, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul]
  have hvA : v (A.det : C) ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]
    exact fun h0 => hA0 (Subtype.ext h0)
  have hRL' : RelLen v X' X ((v (A.det : C)).untop hvA) :=
    ⟨N, bX, bX', A, hA, by rw [WithTop.coe_untop]⟩
  have hrr := RelLen.unique v hRL hRL'
  refine ⟨(A.det : C), ?_, hM0, ?_⟩
  · rw [hrr, WithTop.coe_untop]
  · rw [hM, Matrix.det_mul, Matrix.det_transpose, Subring.coe_mul]

theorem det_part
    (hE4 : preEig a Fil τ ⊓ LinearMap.ker (comp a N τ) ≤ Fil.restrictScalars (Int0 v))
    (hE6 : eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ) = ⊥)
    (hE8 : (preEig a Fil τ).map (proj a Fil) = eigSub a τ ((Fin N → RS a) ⧸ Fil))
    (hE9 : eigSub a τ (Fin N → RS a) ≤ preEig a Fil τ)
    (hE10 : Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ) {r : ℝ}
    (hRL : RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ))
      ((preEig a Fil τ).map (comp a N τ)) r) {p j : ℕ}
    (h : Basis (Fin N) (Int0 v) (eigSub a τ (Fin N → RS a)))
    (l : Basis (Fin p) (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)))
    (x : Fin p → (Fin N → RS a))
    (hx : ∀ i, proj a Fil (x i) = (l i : (Fin N → RS a) ⧸ Fil))
    (f : Basis (Fin j) (Int0 v) (eigQuot a Fil τ)) (e : Fin N ≃ Fin p ⊕ Fin j) :
    ∃ c : C, v c = r ∧
      (Matrix.of fun k : Fin N =>
        Sum.elim (fun i => comp a N τ (x i)) (fun i => (f i : Fin N → Int0 v)) (e k)).det ≠ 0 ∧
      ((Matrix.of fun k : Fin N => comp a N τ (h k : Fin N → RS a)).det : C) =
        c * ((Matrix.of fun k : Fin N =>
          Sum.elim (fun i => comp a N τ (x i)) (fun i => (f i : Fin N → Int0 v)) (e k)).det : C) := by
  obtain ⟨bL0, hbL0⟩ := exists_basis_comb hE4 hE8 hE10 l x hx f
  obtain ⟨bh, hbh⟩ := exists_basis_image hE6 h
  have hbL : (fun k => ((bL0.reindex e.symm) k : Fin N → Int0 v)) = fun k =>
      Sum.elim (fun i => comp a N τ (x i)) (fun i => (f i : Fin N → Int0 v)) (e k) := by
    funext k
    have := hbL0 (e k)
    simpa only [Basis.reindex_apply, Equiv.symm_symm] using this
  have hbh' : (fun k => (bh k : Fin N → Int0 v)) = fun k => comp a N τ (h k : Fin N → RS a) :=
    funext hbh
  have := det_eq_mul_of_relLen (Submodule.map_mono hE9) hRL (bL0.reindex e.symm) bh
  rw [hbL, hbh'] at this
  exact this

theorem detIdentity_of_relLen : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type)
    [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a →
    ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)),
      (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) →
      ∀ τ : S, ∀ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ →
        RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ))
          ((preEig a Fil τ).map (comp a N τ)) r →
        DetIdentity v a Fil τ := by
  intro C _ v S _ _ a ha N Fil hsat τ r hr hRL
  obtain ⟨hd, -, -, hE4, -, hE6, hE7, hE8, hE9, hE10, -, -⟩ :=
    GlobalTheory.T.adjoinRootProdLinearFactors_lattice_facts C v S a ha N Fil hsat τ
  obtain ⟨hfFil, -, -, -, hfLie, -, -⟩ := GlobalTheory.T.finite_eigenFiltration_pieces_addValInt C v S a ha N Fil hsat τ

  haveI : Module.IsTorsionFree (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)) :=
    Module.IsTorsionFree.of_smul_eq_zero fun c m hcm => by
      by_cases hc : c = 0
      · exact Or.inl hc
      right
      obtain ⟨m, hm⟩ := m
      apply Subtype.ext
      induction m using Submodule.Quotient.induction_on with
      | H z =>
        have h0 : (c • Submodule.Quotient.mk z : (Fin N → RS a) ⧸ Fil) = 0 :=
          congrArg Subtype.val hcm
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
        show Submodule.Quotient.mk z = 0
        rw [Submodule.Quotient.mk_eq_zero]
        exact hsat c z hc h0
  haveI := hfLie
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v)
    (eigSub a τ ((Fin N → RS a) ⧸ Fil))

  haveI := hfFil
  haveI hfQ : Module.Finite (Int0 v) (eigQuot a Fil τ) :=
    Module.Finite.map (Fil.restrictScalars (Int0 v)) (comp a N τ)
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) (eigQuot a Fil τ)
  have hrk : finrank (Int0 v) (eigQuot a Fil τ) = eigRank v a Fil τ :=
    GlobalTheory.T.finrank_int0_submodule_eq_finrank_span C v N (eigQuot a Fil τ) hfQ
  have bF := Module.finBasisOfFinrankEq (Int0 v) (eigQuot a Fil τ) hrk
  have bLie := Module.finBasis (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil))
  obtain ⟨bH⟩ := exists_basis_eigSub (ev a τ (cofac a τ)) hd hE6 hE7
  refine ⟨finrank (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)), ?_, ⟨bH⟩, ⟨bLie⟩, ⟨bF⟩, ?_⟩
  ·
    obtain ⟨n, b1, b1', -, -, -⟩ := hRL
    have hlift : ∀ i, ∃ z : Fin N → RS a, proj a Fil z = (bLie i : (Fin N → RS a) ⧸ Fil) :=
      fun i => Submodule.mkQ_surjective Fil _
    choose x hx using hlift
    obtain ⟨bL, -⟩ := exists_basis_comb hE4 hE8 hE10 bLie x hx bF
    obtain ⟨bHi, -⟩ := exists_basis_image hE6 bH
    have h1 := Fintype.card_congr (bL.indexEquiv b1)
    have h2 := Fintype.card_congr (bHi.indexEquiv b1')
    simp only [Fintype.card_sum, Fintype.card_fin] at h1 h2
    omega
  · intro h l x hx f e
    obtain ⟨c, hc, h1, h2⟩ := det_part hE4 hE6 hE8 hE9 hE10 hRL h l x hx f e
    exact ⟨c, hc.trans hr, h1, h2⟩

end GlobalTheory.HerbDet
end
end

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.herbrand_determinant_identity_of_relativeLength : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ∀ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ → RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ)) ((preEig a Fil τ).map (comp a N τ)) r → DetIdentity v a Fil τ := by
  atlas_forward_decl GlobalTheory.HerbDet.detIdentity_of_relLen
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory.LenMap

theorem isTorsionFree_submodule {R : Type*} [CommRing R] [IsDomain R] {M : Type*} [AddCommGroup M]
    [Module R M] (h : ∀ (c : R) (x : M), c ≠ 0 → c • x = 0 → x = 0) (N : Submodule R M) :
    Module.IsTorsionFree R N := by
  refine ⟨fun r hr x y hxy => ?_⟩
  have hr0 : r ≠ 0 := hr.ne_zero
  have h1 : r • ((x : M) - y) = 0 := by
    have := congrArg Subtype.val hxy
    simp only [SetLike.val_smul] at this
    rw [smul_sub, this, sub_self]
  exact Subtype.ext (sub_eq_zero.1 (h r _ hr0 h1))

theorem exists_basis_sum {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') (Z : Submodule R M) {ι κ : Type*}
    [Fintype ι] [Fintype κ] (d : Basis ι R ↥(Z ⊓ LinearMap.ker f)) (e : Basis κ R ↥(Z.map f))
    (σ : κ → M) (hσZ : ∀ j, σ j ∈ Z) (hσf : ∀ j, f (σ j) = e j) :
    ∃ b : Basis (ι ⊕ κ) R Z, ∀ k, (b k : M) = Sum.elim (fun i => (d i : M)) σ k := by
  classical
  let w : ι ⊕ κ → M := Sum.elim (fun i => (d i : M)) σ
  have hwZ : ∀ k, w k ∈ Z := by
    rintro (i | j)
    · exact (Submodule.mem_inf.1 (d i).2).1
    · exact hσZ j
  let u : ι ⊕ κ → Z := fun k => ⟨w k, hwZ k⟩
  have hdf : ∀ i, f (d i : M) = 0 := fun i => LinearMap.mem_ker.1 (Submodule.mem_inf.1 (d i).2).2
  have hdli : LinearIndependent R (fun i => (d i : M)) :=
    d.linearIndependent.map' (Z ⊓ LinearMap.ker f).subtype (Submodule.ker_subtype _)
  have heli : LinearIndependent R (fun j => (e j : M')) :=
    e.linearIndependent.map' (Z.map f).subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent R u := by
    apply LinearIndependent.of_comp Z.subtype
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : ∑ i, g (Sum.inl i) • (d i : M) + ∑ j, g (Sum.inr j) • σ j = 0 := by
      simpa [Fintype.sum_sum_type, u, w] using hg
    have h2 : ∑ j, g (Sum.inr j) • (e j : M') = 0 := by
      have := congrArg f hg'
      simpa [map_add, map_sum, map_smul, hdf, hσf] using this
    have hr : ∀ j, g (Sum.inr j) = 0 := Fintype.linearIndependent_iff.1 heli _ h2
    have h1 : ∑ i, g (Sum.inl i) • (d i : M) = 0 := by simpa [hr] using hg'
    have hl : ∀ i, g (Sum.inl i) = 0 := Fintype.linearIndependent_iff.1 hdli _ h1
    rintro (i | j)
    · exact hl i
    · exact hr j
  have hsp : ⊤ ≤ Submodule.span R (Set.range u) := by
    rintro ⟨z, hz⟩ -
    rw [Submodule.mem_span_range_iff_exists_fun]
    have hfz : f z ∈ Z.map f := Submodule.mem_map_of_mem hz
    let bb := e.repr ⟨f z, hfz⟩
    have hy : (∑ j, bb j • (e j : M')) = f z := by
      have h0 := congrArg Subtype.val (e.sum_repr ⟨f z, hfz⟩)
      rw [Submodule.coe_sum] at h0
      simpa only [Submodule.coe_smul] using h0
    have hk : z - ∑ j, bb j • σ j ∈ Z ⊓ LinearMap.ker f := by
      refine Submodule.mem_inf.2 ⟨Z.sub_mem hz (Z.sum_mem fun j _ => Z.smul_mem _ (hσZ j)), ?_⟩
      rw [LinearMap.mem_ker, map_sub, map_sum]
      simp only [map_smul, hσf]
      rw [hy, sub_self]
    have hkk := congrArg Subtype.val (d.sum_repr ⟨_, hk⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hkk
    refine ⟨Sum.elim (d.repr ⟨_, hk⟩) bb, ?_⟩
    apply Subtype.ext
    rw [Fintype.sum_sum_type, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_sum]
    simp only [Submodule.coe_smul, Sum.elim_inl, Sum.elim_inr, u, w]
    rw [hkk, sub_add_cancel]
  exact ⟨Basis.mk hli hsp, fun k => by simp [u, w]⟩

end GlobalTheory.LenMap

namespace GlobalTheory.LenMap

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {M : Type} [AddCommGroup M]
  [Module (Int0 v) M]

theorem val_det_eq {ι : Type} [Fintype ι] [DecidableEq ι] {X' X : Submodule (Int0 v) M}
    (hle : X' ≤ X) (b c : Basis ι (Int0 v) X) (b' c' : Basis ι (Int0 v) X')
    (A B : Matrix ι ι (Int0 v)) (hA : ∀ k, (b' k : M) = ∑ i, A i k • (b i : M))
    (hB : ∀ k, (c' k : M) = ∑ i, B i k • (c i : M)) : v (A.det : C) = v (B.det : C) := by
  have key : ∀ (b : Basis ι (Int0 v) X) (b' : Basis ι (Int0 v) X')
      (A : Matrix ι ι (Int0 v)), (∀ k, (b' k : M) = ∑ i, A i k • (b i : M)) →
      LinearMap.toMatrix b' b (Submodule.inclusion hle) = A := by
    intro b b' A hA
    ext i k
    have : Submodule.inclusion hle (b' k) = ∑ i, A i k • b i := by
      apply Subtype.ext
      simpa using hA k
    rw [LinearMap.toMatrix_apply, this]
    simp [Finsupp.single_apply]
  have hAB : A = b.toMatrix c * B * c'.toMatrix b' := by
    rw [← key b b' A hA, ← key c c' B hB, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  have u1 : IsUnit (b.toMatrix c).det := by
    letI := b.invertibleToMatrix c
    exact Matrix.isUnit_det_of_invertible _
  have u2 : IsUnit (c'.toMatrix b').det := by
    letI := c'.invertibleToMatrix b'
    exact Matrix.isUnit_det_of_invertible _
  rw [hAB, Matrix.det_mul, Matrix.det_mul, Subring.coe_mul, Subring.coe_mul, v.map_mul,
    v.map_mul, v_unit v u1, v_unit v u2, zero_add, add_zero]

theorem relLen_iff_of_basis {ι : Type} [Fintype ι] [DecidableEq ι] {X' X : Submodule (Int0 v) M}
    (hle : X' ≤ X) (b : Basis ι (Int0 v) X) (b' : Basis ι (Int0 v) X')
    (A : Matrix ι ι (Int0 v)) (hA : ∀ k, (b' k : M) = ∑ i, A i k • (b i : M)) (r : ℝ) :
    RelLen v X' X r ↔ v (A.det : C) = r := by
  constructor
  · rintro ⟨n, c, c', B, hB, hr⟩
    let e := b.indexEquiv c
    rw [← hr, ← Matrix.det_reindex_self e.symm B]
    refine val_det_eq v hle b (c.reindex e.symm) b' (c'.reindex e.symm) A _ hA fun k => ?_
    simp only [Basis.reindex_apply, Equiv.symm_symm, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [hB]
    exact (Equiv.sum_comp e (fun i => B i (e k) • (c i : M))).symm
  · intro h
    let e := Fintype.equivFin ι
    refine ⟨Fintype.card ι, b.reindex e, b'.reindex e, Matrix.reindex e e A, fun k => ?_, ?_⟩
    · simp only [Basis.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
      rw [hA]
      exact (Equiv.sum_comp e.symm (fun i => A i (e.symm k) • (b i : M))).symm
    · rw [Matrix.det_reindex_self]; exact h

theorem card_eq_of_relLen {ι ι' : Type} [Fintype ι] [Fintype ι'] {X' X : Submodule (Int0 v) M}
    {r : ℝ} (h : RelLen v X' X r) (b : Basis ι (Int0 v) X) (b' : Basis ι' (Int0 v) X') :
    Fintype.card ι = Fintype.card ι' := by
  obtain ⟨n, c, c', -, -, -⟩ := h
  rw [Fintype.card_congr (b.indexEquiv c), Fintype.card_congr (b'.indexEquiv c')]

end GlobalTheory.LenMap

namespace GlobalTheory.LenMap

theorem relLen_map_iff : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M M' : Type) [AddCommGroup M] [Module (Int0 v) M] [AddCommGroup M'] [Module (Int0 v) M'], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) → (∀ (c : Int0 v) (x : M'), c ≠ 0 → c • x = 0 → x = 0) → ∀ (f : M →ₗ[Int0 v] M') (X' X : Submodule (Int0 v) M), X' ≤ X → X ⊓ LinearMap.ker f ≤ X' → Module.Finite (Int0 v) X → Module.Finite (Int0 v) X' → ∀ r : ℝ, (RelLen v X' X r ↔ RelLen v (X'.map f) (X.map f) r) := by
  intro C _ v M M' _ _ _ _ htM htM' f X' X hle hker hX hX' r
  classical
  haveI := isTorsionFree_submodule htM' (X.map f)
  haveI := isTorsionFree_submodule htM' (X'.map f)
  haveI := isTorsionFree_submodule htM (X ⊓ LinearMap.ker f)
  haveI : Module.Finite (Int0 v) (X.map f) := Module.Finite.map X f
  haveI : Module.Finite (Int0 v) (X'.map f) := Module.Finite.map X' f
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) (X.map f)
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) (X'.map f)
  let g : X →ₗ[Int0 v] X.map f := f.submoduleMap X
  have hg : Function.Surjective g := f.submoduleMap_surjective X
  haveI : Module.FinitePresentation (Int0 v) (X.map f) := Module.finitePresentation_of_projective _ _
  have hfg : (LinearMap.ker g).FG := Module.FinitePresentation.fg_ker g hg
  have hK : (LinearMap.ker g).map X.subtype = X ⊓ LinearMap.ker f := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have := congrArg Subtype.val hy
      simpa [g] using this
    · rintro ⟨hx, hfx⟩
      exact ⟨⟨x, hx⟩, Subtype.ext (by simpa [g] using hfx), rfl⟩
  haveI : Module.Finite (Int0 v) ↥(X ⊓ LinearMap.ker f) := by
    rw [Module.Finite.iff_fg, ← hK]
    exact hfg.map _
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) ↥(X ⊓ LinearMap.ker f)
  have hK' : X' ⊓ LinearMap.ker f = X ⊓ LinearMap.ker f :=
    le_antisymm (inf_le_inf_right _ hle) (le_inf hker inf_le_right)
  obtain ⟨q, ⟨d⟩⟩ : ∃ q : ℕ, Nonempty (Basis (Fin q) (Int0 v) ↥(X ⊓ LinearMap.ker f)) :=
    ⟨_, ⟨Module.finBasis _ _⟩⟩
  obtain ⟨p, ⟨c⟩⟩ : ∃ p : ℕ, Nonempty (Basis (Fin p) (Int0 v) ↥(X.map f)) :=
    ⟨_, ⟨Module.finBasis _ _⟩⟩
  obtain ⟨p', ⟨c'⟩⟩ : ∃ p : ℕ, Nonempty (Basis (Fin p) (Int0 v) ↥(X'.map f)) :=
    ⟨_, ⟨Module.finBasis _ _⟩⟩
  let d' : Basis (Fin q) (Int0 v) ↥(X' ⊓ LinearMap.ker f) := d.map (LinearEquiv.ofEq _ _ hK'.symm)
  have hd' : ∀ i, (d' i : M) = d i := fun i => rfl
  have hdf : ∀ i, f (d i : M) = 0 := fun i => LinearMap.mem_ker.1 (Submodule.mem_inf.1 (d i).2).2
  choose σ hσX hσf using fun j => Submodule.mem_map.1 (c j).2
  choose σ' hσX' hσf' using fun j => Submodule.mem_map.1 (c' j).2
  obtain ⟨b, hb⟩ := exists_basis_sum f X d c σ hσX hσf
  obtain ⟨b', hb'⟩ := exists_basis_sum f X' d' c' σ' hσX' hσf'
  by_cases hp : p = p'
  · subst hp
    let A : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) (Int0 v) :=
      Matrix.of fun i k => b.repr (Submodule.inclusion hle (b' k)) i
    have hA : ∀ k, (b' k : M) = ∑ i, A i k • (b i : M) := by
      intro k
      have h0 := congrArg Subtype.val (b.sum_repr (Submodule.inclusion hle (b' k)))
      rw [Submodule.coe_sum] at h0
      simpa only [Submodule.coe_smul, Submodule.coe_inclusion, A, Matrix.of_apply] using h0.symm
    rw [relLen_iff_of_basis v hle b b' A hA]
    let B := A.toBlocks₂₂
    have hB : ∀ k, (c' k : M') = ∑ j, B j k • (c j : M') := by
      intro k
      have h1 := congrArg f (hA (Sum.inr k))
      rw [hb', Sum.elim_inr, hσf', map_sum, Fintype.sum_sum_type] at h1
      simpa [hb, hdf, hσf, B, Matrix.toBlocks₂₂] using h1
    rw [relLen_iff_of_basis v (Submodule.map_mono hle) c c' B hB]
    have hinl : ∀ i, Submodule.inclusion hle (b' (Sum.inl i)) = b (Sum.inl i) := by
      intro i
      apply Subtype.ext
      rw [Submodule.coe_inclusion, hb, hb', Sum.elim_inl, Sum.elim_inl, hd']
    have h11 : A.toBlocks₁₁ = 1 := by
      ext i k
      simp [A, Matrix.toBlocks₁₁, hinl, Finsupp.single_apply, Matrix.one_apply, eq_comm]
    have h21 : A.toBlocks₂₁ = 0 := by
      ext i k
      simp [A, Matrix.toBlocks₂₁, hinl, Finsupp.single_apply]
    have hdet : A.det = B.det := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks A, h11, h21]
      rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
    rw [hdet]
  · constructor
    · intro h
      have := card_eq_of_relLen v h b b'
      simp only [Fintype.card_sum, Fintype.card_fin] at this
      omega
    · intro h
      have := card_eq_of_relLen v h c c'
      simp only [Fintype.card_fin] at this
      exact absurd this hp

end GlobalTheory.LenMap
end

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasLatticeRelativeLength_map_iff : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M M' : Type) [AddCommGroup M] [Module (Int0 v) M] [AddCommGroup M'] [Module (Int0 v) M'], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) → (∀ (c : Int0 v) (x : M'), c ≠ 0 → c • x = 0 → x = 0) → ∀ (f : M →ₗ[Int0 v] M') (X' X : Submodule (Int0 v) M), X' ≤ X → X ⊓ LinearMap.ker f ≤ X' → Module.Finite (Int0 v) X → Module.Finite (Int0 v) X' → ∀ r : ℝ, (RelLen v X' X r ↔ RelLen v (X'.map f) (X.map f) r) := by
  atlas_forward_decl GlobalTheory.LenMap.relLen_map_iff
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory

theorem relLen_chain_add : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type)
    [AddCommGroup M] [Module (Int0 v) M] (X'' X' X : Submodule (Int0 v) M) (r₁ r₂ : ℝ),
    RelLen v X'' X' r₂ → RelLen v X' X r₁ → RelLen v X'' X (r₁ + r₂) := by
  intro C _ v M _ _ X'' X' X r₁ r₂ h₂ h₁
  obtain ⟨n, b, b', A, hA, hr₂⟩ := h₂
  obtain ⟨m, c, c', B, hB, hr₁⟩ := h₁
  have hnm : n = m := by simpa using Fintype.card_congr (b.indexEquiv c')
  subst hnm
  have hU : ∀ i, (b i : M) = ∑ j, c'.toMatrix b j i • (c' j : M) := by
    intro i
    have := congrArg X'.subtype (c'.sum_repr (b i))
    simp only [map_sum, map_smul, Submodule.subtype_apply] at this
    simp only [Basis.toMatrix_apply]
    exact this.symm
  have u : IsUnit (c'.toMatrix b).det := by
    let _ := c'.invertibleToMatrix b
    exact Matrix.isUnit_det_of_invertible _
  refine ⟨n, c, b', B * c'.toMatrix b * A, fun k => ?_, ?_⟩
  · rw [hA k]
    simp_rw [hU, hB, Finset.smul_sum, smul_smul]
    simp_rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_smul]
    refine (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    congr 1
    ring
  · rw [Matrix.det_mul, Matrix.det_mul, Subring.coe_mul, Subring.coe_mul, v.map_mul, v.map_mul,
      v_unit v u, add_zero, hr₁, hr₂]
    rfl

end GlobalTheory
end

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relLen_trans_add : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type) [AddCommGroup M] [Module (Int0 v) M] (X'' X' X : Submodule (Int0 v) M) (r₁ r₂ : ℝ), RelLen v X'' X' r₂ → RelLen v X' X r₁ → RelLen v X'' X (r₁ + r₂) := by
  atlas_forward_decl GlobalTheory.relLen_chain_add
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory.SubLen

theorem exists_relLen_of_smul_le (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type)
    [AddCommGroup M] [Module (Int0 v) M]
    (htf : ∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0)
    (X' X : Submodule (Int0 v) M) (hle : X' ≤ X) (hX : Module.Finite (Int0 v) X)
    (hX' : Module.Finite (Int0 v) X') (c : Int0 v) (hc : c ≠ 0) (hcX : ∀ x ∈ X, c • x ∈ X') :
    ∃ r : ℝ, RelLen v X' X r := by
  haveI tfX : Module.IsTorsionFree (Int0 v) X :=
    Module.isTorsionFree_iff_smul_eq_zero.mpr fun r x h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · refine Or.inr (Subtype.ext ?_)
        have h' : r • (x : M) = 0 := by rw [← Submodule.coe_smul, h, Submodule.coe_zero]
        exact htf r _ hr h'
  haveI tfX' : Module.IsTorsionFree (Int0 v) X' :=
    Module.isTorsionFree_iff_smul_eq_zero.mpr fun r x h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · refine Or.inr (Subtype.ext ?_)
        have h' : r • (x : M) = 0 := by rw [← Submodule.coe_smul, h, Submodule.coe_zero]
        exact htf r _ hr h'
  haveI := hX
  haveI := hX'
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) X
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) X'
  let ι : X' →ₗ[Int0 v] X := Submodule.inclusion hle
  have hι : Function.Injective ι := Submodule.inclusion_injective hle
  let μ : X →ₗ[Int0 v] X' :=
    { toFun := fun x => ⟨c • (x : M), hcX x x.2⟩
      map_add' := fun x y => Subtype.ext (smul_add c (x : M) y)
      map_smul' := fun r x => Subtype.ext (by
        change c • (r • (x : M)) = r • (c • (x : M))
        exact smul_comm c r (x : M)) }
  have hμ : Function.Injective μ := by
    intro x y hxy
    have : c • ((x : M) - y) = 0 := by
      have h3 : c • (x : M) = c • (y : M) := congrArg Subtype.val hxy
      rw [smul_sub, h3, sub_self]
    exact Subtype.ext (sub_eq_zero.1 (htf c _ hc this))
  have h1 : finrank (Int0 v) X' ≤ finrank (Int0 v) X := LinearMap.finrank_le_finrank_of_injective hι
  have h2 : finrank (Int0 v) X ≤ finrank (Int0 v) X' := LinearMap.finrank_le_finrank_of_injective hμ
  have heq : finrank (Int0 v) X' = finrank (Int0 v) X := le_antisymm h1 h2
  let b := Module.finBasis (Int0 v) X
  let b' := Module.finBasisOfFinrankEq (Int0 v) X' heq
  let A := LinearMap.toMatrix b' b ι
  have hA : ∀ k, (b' k : M) = ∑ i, A i k • (b i : M) := by
    intro k
    have e := b.sum_repr (ι (b' k))
    have e2 := congrArg (Submodule.subtype X) e
    rw [map_sum] at e2
    simp only [map_smul, Submodule.subtype_apply] at e2
    simpa [A, LinearMap.toMatrix_apply, ι] using e2.symm
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hw0
    have : ι (b'.equivFun.symm w) = 0 := by
      have := Matrix.toLin_toMatrix b' b ι
      rw [← this, Matrix.toLin_apply]
      simp only [Basis.equivFun_symm_apply, Basis.repr_sum_self]
      change ∑ x, (A.mulVec w) x • b x = 0
      simp [hw]
    have h4 := hι (this.trans (map_zero ι).symm)
    have h5 := congrArg b'.equivFun h4
    rw [LinearEquiv.apply_symm_apply, map_zero] at h5
    exact h5
  have hv : v (A.det : C) ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]
    exact_mod_cast hdet
  exact ⟨(v (A.det : C)).untop hv, _, b, b', A, hA, (WithTop.coe_untop _ hv).symm⟩

end GlobalTheory.SubLen
end

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeRelativeLength_of_smul_le : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type) [AddCommGroup M] [Module (Int0 v) M], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) → ∀ (X' X : Submodule (Int0 v) M), X' ≤ X → Module.Finite (Int0 v) X → Module.Finite (Int0 v) X' → ∀ c : Int0 v, c ≠ 0 → (∀ x ∈ X, c • x ∈ X') → ∃ r : ℝ, RelLen v X' X r := by
  atlas_forward_decl GlobalTheory.SubLen.exists_relLen_of_smul_le
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory.ScalLen

theorem relLen_map_lsmul : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type)
    [AddCommGroup M] [Module (Int0 v) M], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) →
    ∀ (X : Submodule (Int0 v) M), Module.Finite (Int0 v) X → ∀ (c : Int0 v) (r : ℝ),
      v (c : C) = r →
      RelLen v (X.map (LinearMap.lsmul (Int0 v) M c)) X ((finrank (Int0 v) X : ℝ) * r) := by
  intro C _ v M _ _ htf X hX c r hr
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hr
  haveI : Module.IsTorsionFree (Int0 v) X := ⟨fun s hs x y hxy => by
    have hs0 : s ≠ 0 := hs.ne_zero
    apply Subtype.ext
    have h1 : s • ((x : M) - (y : M)) = 0 := by
      rw [smul_sub]
      have := congrArg Subtype.val hxy
      simp only [Submodule.coe_smul] at this
      rw [this, sub_self]
    exact sub_eq_zero.1 (htf s _ hs0 h1)⟩
  haveI : Module.Free (Int0 v) X := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing _ _
  set n := finrank (Int0 v) X with hn
  let b : Basis (Fin n) (Int0 v) X := Module.finBasis _ _
  let g : X →ₗ[Int0 v] M := (LinearMap.lsmul (Int0 v) M c).comp X.subtype
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    have h1 : c • ((x : M) - (y : M)) = 0 := by
      rw [smul_sub]
      simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.lsmul_apply] at hxy
      rw [hxy, sub_self]
    exact sub_eq_zero.1 (htf c _ hc h1)
  have hrange : LinearMap.range g = X.map (LinearMap.lsmul (Int0 v) M c) := by
    simp only [g, LinearMap.range_comp, Submodule.range_subtype]
  let e : X ≃ₗ[Int0 v] X.map (LinearMap.lsmul (Int0 v) M c) :=
    (LinearEquiv.ofInjective g hg).trans (LinearEquiv.ofEq _ _ hrange)
  refine ⟨n, b, b.map e, Matrix.diagonal (fun _ => c), fun k => ?_, ?_⟩
  · simp only [Basis.map_apply, Matrix.diagonal_apply, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  · rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Subring.coe_pow, AddValuation.map_pow, hr, ← WithTop.coe_nsmul, nsmul_eq_mul]

end GlobalTheory.ScalLen
end

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeRelativeLength_smul_eq_rank_mul_valuation : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type) [AddCommGroup M] [Module (Int0 v) M], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) → ∀ (X : Submodule (Int0 v) M), Module.Finite (Int0 v) X → ∀ (c : Int0 v) (r : ℝ), v (c : C) = r → RelLen v (X.map (LinearMap.lsmul (Int0 v) M c)) X ((finrank (Int0 v) X : ℝ) * r) := by
  atlas_forward_decl GlobalTheory.ScalLen.relLen_map_lsmul
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

noncomputable section
namespace GlobalTheory.HerbLen

theorem relLen_nonneg {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : Type}
    [AddCommGroup M] [Module (Int0 v) M] {X' X : Submodule (Int0 v) M} {r : ℝ}
    (h : RelLen v X' X r) : 0 ≤ r := by
  obtain ⟨n, b, b', A, -, hr⟩ := h
  have h0 : (0 : WithTop ℝ) ≤ v (A.det : C) := (mem_addValuationIntegerRing_iff v _).1 A.det.2
  rw [hr] at h0
  exact_mod_cast h0

theorem addVal_prod {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {ι : Type}
    (s : Finset ι) (f : ι → C) : v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, v.map_mul, ih]

set_option maxHeartbeats 1000000 in
theorem herbrand_lengthIdentities_auxiliary_bound (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type)
    [Fintype S] [DecidableEq S] (a : S → Int0 v) (ha : Function.Injective a) (N : ℕ)
    (Fil : Submodule (RS a) (Fin N → RS a))
    (hsat : ∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) (τ : S) (r : ℝ)
    (hr : (r : WithTop ℝ) = yExp v a Fil τ)
    (hlen : RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ))
      ((preEig a Fil τ).map (comp a N τ)) r) :
    LengthIdentities v a Fil τ := by
  unfold LengthIdentities
  obtain ⟨hd0, hker, hkerrange, hXker, hAX, -, -, hprojX, hHX, hFX, htf, g, helem⟩ :=
    GlobalTheory.T.adjoinRootProdLinearFactors_lattice_facts C v S a ha N Fil hsat τ
  obtain ⟨fF, fX, fK, fH, -, fFt, fKP⟩ := GlobalTheory.T.finite_eigenFiltration_pieces_addValInt C v S a ha N Fil hsat τ
  obtain ⟨-, -, hlc, hevc, -, -, -⟩ := GlobalTheory.T.adjoinRootProdLinearFactors_structure (Int0 v) S a τ
  have m1 : ∀ x : Fin N → RS a, x ∈ eigSub a τ (Fin N → RS a) ↔ lin a τ • x = 0 := by
    intro x; simp [eigSub, kerMul]
  have m2 : ∀ x : Fin N → RS a, x ∈ preEig a Fil τ ↔ lin a τ • x ∈ Fil := by
    intro x; simp [preEig, mulR]
  have m3 : ∀ x : Fin N → RS a, x ∈ filKer a Fil τ ↔ x ∈ Fil ∧ cofac a τ • x = 0 := by
    intro x; simp [filKer, mulR]
  have m4 : ∀ x : Fil, x ∈ eigSub a τ Fil ↔ lin a τ • (x : Fin N → RS a) = 0 := by
    intro x; simp [eigSub, kerMul, Subtype.ext_iff]
  generalize hd : ev a τ (cofac a τ) = d at hd0 helem hevc
  have hlinP : ∀ x : Fin N → RS a, lin a τ • (cofac a τ • x) = 0 := by
    intro x; rw [smul_smul, hlc, zero_smul]
  have hPh : ∀ x : Fin N → RS a, lin a τ • x = 0 → d • x = cofac a τ • x := by
    intro x h; rw [helem, h, smul_zero, sub_zero]
  have hcA : ∀ x, comp a N τ (lin a τ • x) = 0 := by
    intro x
    have : lin a τ • x ∈ LinearMap.ker (comp a N τ) := by rw [hkerrange]; exact ⟨x, rfl⟩
    exact this
  have hcP : ∀ x, comp a N τ (cofac a τ • x) = d • comp a N τ x := by
    intro x
    rw [show d • comp a N τ x = comp a N τ (d • x) from (map_smul (comp a N τ) d x).symm, helem,
      map_sub, smul_comm g (lin a τ) x, hcA, sub_zero]
  have hker' : ∀ x, comp a N τ x = 0 ↔ cofac a τ • x = 0 := hker
  have hkerA : ∀ x, mulR a N (lin a τ) x = 0 → x ∈ eigSub a τ (Fin N → RS a) := fun x h => (m1 x).2 h
  have hIinj : Function.Injective (incl a Fil) := fun x y h => Subtype.ext h
  have htfQ : ∀ (c : Int0 v) (y : (Fin N → RS a) ⧸ Fil), c ≠ 0 → c • y = 0 → y = 0 := by
    intro c y hc h
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      exact (Submodule.Quotient.mk_eq_zero _).2 (hsat c x hc h)
  have htfF : ∀ (c : Int0 v) (y : Fil), c ≠ 0 → c • y = 0 → y = 0 := by
    intro c y hc h
    exact Subtype.ext (htf c y hc (congrArg Subtype.val h))
  have htfO : ∀ (c : Int0 v) (y : Fin N → Int0 v), c ≠ 0 → c • y = 0 → y = 0 := by
    intro c y hc h; exact (smul_eq_zero.mp h).resolve_left hc
  have fgF : (Fil.restrictScalars (Int0 v)).FG := Module.Finite.iff_fg.mp fF
  have fgH : (eigSub a τ (Fin N → RS a)).FG := Module.Finite.iff_fg.mp fH
  have fgK : (filKer a Fil τ).FG := Module.Finite.iff_fg.mp fK
  have fB : Module.Finite (Int0 v) ↥(eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v)) :=
    Module.Finite.iff_fg.mpr (fgH.sup fgF)

  have hBX : eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ :=
    sup_le hHX hFX
  have hdB : ∀ x ∈ preEig a Fil τ,
      d • x ∈ eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v) := by
    intro x hx
    rw [helem]
    refine Submodule.sub_mem_sup ?_ ?_
    · exact (m1 _).2 (hlinP x)
    · exact Fil.smul_mem g ((m2 x).1 hx)
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_latticeRelativeLength_of_smul_le C v _ htf _ _ hBX fX fB d hd0 hdB

  have hmapB_proj : (eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v)).map (proj a Fil) =
      (eigSub a τ (Fin N → RS a)).map (proj a Fil) := by
    rw [Submodule.map_sup]
    have : (Fil.restrictScalars (Int0 v)).map (proj a Fil) = ⊥ := by
      rw [eq_bot_iff]; rintro _ ⟨x, hx, rfl⟩
      exact (Submodule.mem_bot _).2 ((Submodule.Quotient.mk_eq_zero _).2 hx)
    rw [this, sup_bot_eq]
  have ha1 : RelLen v ((eigSub a τ (Fin N → RS a)).map (proj a Fil))
      (eigSub a τ ((Fin N → RS a) ⧸ Fil)) δ := by
    have := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htfQ (proj a Fil) _ _ hBX ?_ fX fB δ).1 hδ
    · rwa [hmapB_proj, hprojX] at this
    · rintro x ⟨-, hx⟩
      exact Submodule.mem_sup_right ((Submodule.Quotient.mk_eq_zero _).1 hx)

  have hHA : (eigSub a τ (Fin N → RS a)).map (mulR a N (lin a τ)) = ⊥ := by
    rw [eq_bot_iff]; rintro _ ⟨x, hx, rfl⟩
    exact (Submodule.mem_bot _).2 ((m1 x).1 hx)
  have hmapB_A : (eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v)).map (mulR a N (lin a τ)) =
      (Fil.restrictScalars (Int0 v)).map (mulR a N (lin a τ)) := by
    rw [Submodule.map_sup, hHA, bot_sup_eq]
  have hb0 : RelLen v ((Fil.restrictScalars (Int0 v)).map (mulR a N (lin a τ))) (filKer a Fil τ) δ := by
    have := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htf (mulR a N (lin a τ)) _ _ hBX ?_ fX fB δ).1 hδ
    · rwa [hmapB_A, hAX] at this
    · rintro x ⟨-, hx⟩; exact Submodule.mem_sup_left (hkerA x hx)
  have hIm1 : (imMul a (lin a τ) Fil).map (incl a Fil) =
      (Fil.restrictScalars (Int0 v)).map (mulR a N (lin a τ)) := by
    ext z; constructor
    · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, w.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨lin a τ • x, Fil.smul_mem _ hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  have hIm2 : (kerMul a (cofac a τ) Fil).map (incl a Fil) = filKer a Fil τ := by
    ext z; constructor
    · rintro ⟨y, hy, rfl⟩
      exact (m3 _).2 ⟨y.2, by simpa [kerMul, Subtype.ext_iff, incl] using hy⟩
    · intro hz
      obtain ⟨hz1, hz2⟩ := (m3 z).1 hz
      exact ⟨⟨z, hz1⟩, by simpa [kerMul, Subtype.ext_iff] using hz2, rfl⟩
  have hfgImLin : (imMul a (lin a τ) Fil).FG :=
    Submodule.fg_of_fg_map_injective _ hIinj (by rw [hIm1]; exact fgF.map _)
  have hle2 : imMul a (lin a τ) Fil ≤ kerMul a (cofac a τ) Fil := by
    rintro _ ⟨y, rfl⟩
    show cofac a τ • lin a τ • y = 0
    rw [smul_smul, mul_comm, hlc, zero_smul]
  have hb : RelLen v (imMul a (lin a τ) Fil) (kerMul a (cofac a τ) Fil) δ := by
    refine (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htfF htf (incl a Fil) _ _ hle2 ?_ fKP
      (Module.Finite.iff_fg.mpr hfgImLin) δ).2 ?_
    · rintro x ⟨-, hx⟩
      have : x = 0 := hIinj (by rw [map_zero]; exact hx)
      rw [this]; exact Submodule.zero_mem _
    · rwa [hIm1, hIm2]

  have hIm3 : (imMul a (cofac a τ) Fil).map (incl a Fil) =
      (Fil.restrictScalars (Int0 v)).map (mulR a N (cofac a τ)) := by
    ext z; constructor
    · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, w.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨cofac a τ • x, Fil.smul_mem _ hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  have hfgImP : (imMul a (cofac a τ) Fil).FG :=
    Submodule.fg_of_fg_map_injective _ hIinj (by rw [hIm3]; exact fgF.map _)
  have hle3 : imMul a (cofac a τ) Fil ≤ eigSub a τ Fil := by
    rintro _ ⟨y, rfl⟩
    exact (m4 _).2 (hlinP y)
  have hd3 : ∀ y ∈ eigSub a τ Fil, d • y ∈ imMul a (cofac a τ) Fil := by
    intro y hy
    refine ⟨y, Subtype.ext ?_⟩
    show cofac a τ • (y : Fin N → RS a) = d • (y : Fin N → RS a)
    rw [hPh _ ((m4 y).1 hy)]
  obtain ⟨e₂, he₂⟩ := GlobalTheory.T.exists_latticeRelativeLength_of_smul_le C v _ htfF _ _ hle3 fFt (Module.Finite.iff_fg.mpr hfgImP) d hd0 hd3

  have fgE : (eigQuot a Fil τ).FG := fgF.map _
  have fE : Module.Finite (Int0 v) (eigQuot a Fil τ) := Module.Finite.iff_fg.mpr fgE
  have hfgFt : (eigSub a τ Fil).FG := Module.Finite.iff_fg.mp fFt
  have fCt : Module.Finite (Int0 v) ((eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil))) :=
    Module.Finite.iff_fg.mpr (hfgFt.map _)
  have hle4 : (eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil)) ≤ eigQuot a Fil τ := by
    rintro _ ⟨y, -, rfl⟩; exact ⟨y, y.2, rfl⟩
  have hd4 : ∀ z ∈ eigQuot a Fil τ, d • z ∈ (eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨cofac a τ • x, Fil.smul_mem _ hx⟩, (m4 _).2 (hlinP x), hcP x⟩
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_latticeRelativeLength_of_smul_le C v _ htfO _ _ hle4 fE fCt d hd0 hd4

  have hIm5 : (imMul a (cofac a τ) Fil).map ((comp a N τ).comp (incl a Fil)) =
      (eigQuot a Fil τ).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) d) := by
    ext z; constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨comp a N τ y, ⟨y, y.2, rfl⟩, (hcP y).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨cofac a τ • x, Fil.smul_mem _ hx⟩, ⟨⟨x, hx⟩, rfl⟩, hcP x⟩
  have he5 : RelLen v ((eigQuot a Fil τ).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) d))
      ((eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil))) e₂ := by
    have := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htfF htfO ((comp a N τ).comp (incl a Fil)) _ _ hle3 ?_ fFt
      (Module.Finite.iff_fg.mpr hfgImP) e₂).1 he₂
    · rwa [hIm5] at this
    · rintro y ⟨hy, hy0⟩
      have h1 : cofac a τ • (y : Fin N → RS a) = 0 := (hker' _).1 hy0
      have h2 : d • (y : Fin N → RS a) = 0 := by rw [hPh _ ((m4 y).1 hy), h1]
      have : y = 0 := Subtype.ext (htf d _ hd0 h2)
      rw [this]; exact Submodule.zero_mem _
  have hme : RelLen v ((eigQuot a Fil τ).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) d))
      (eigQuot a Fil τ) (m + e₂) :=
    GlobalTheory.T.relLen_trans_add C v _ _ _ _ m e₂ he5 hm
  have hdC0 : (d : C) ≠ 0 := fun h => hd0 (Subtype.ext h)
  have hvd : v (d : C) ≠ ⊤ := fun h => hdC0 ((AddValuation.top_iff v).1 h)
  obtain ⟨rd, hrd⟩ := WithTop.ne_top_iff_exists.1 hvd
  have hsc := GlobalTheory.T.latticeRelativeLength_smul_eq_rank_mul_valuation C v _ htfO (eigQuot a Fil τ) fE d rd hrd.symm
  have hsum : m + e₂ = (finrank (Int0 v) (eigQuot a Fil τ) : ℝ) * rd := RelLen.unique v hme hsc
  have hfr : finrank (Int0 v) (eigQuot a Fil τ) = eigRank v a Fil τ := GlobalTheory.T.finrank_int0_submodule_eq_finrank_span C v N _ fE
  have hdC : ((d : Int0 v) : C) = ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) := by
    rw [hevc]; push_cast; rfl
  have hvdeq : vd v a τ = (rd : WithTop ℝ) := by
    unfold vd; rw [← hdC, hrd]
  have hjr : eigRank v a Fil τ • vd v a τ = (((eigRank v a Fil τ : ℝ) * rd : ℝ) : WithTop ℝ) := by
    rw [hvdeq, ← WithTop.coe_nsmul, nsmul_eq_mul]

  have hKc : (filKer a Fil τ).map (comp a N τ) = ⊥ := by
    rw [eq_bot_iff]; rintro _ ⟨x, hx, rfl⟩
    exact (Submodule.mem_bot _).2 ((hker' x).2 ((m3 x).1 hx).2)
  have hKF : filKer a Fil τ ≤ Fil.restrictScalars (Int0 v) := fun x hx => ((m3 x).1 hx).1
  have hD'F : (Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ ≤
      Fil.restrictScalars (Int0 v) := sup_le inf_le_left hKF
  have hDB : eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ ≤
      eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v) := sup_le_sup_left hKF _
  have hFHt : Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a) =
      (eigSub a τ Fil).map (incl a Fil) := by
    ext z; constructor
    · rintro ⟨hz1, hz2⟩
      exact ⟨⟨z, hz1⟩, (m4 _).2 ((m1 z).1 hz2), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (m1 _).2 ((m4 y).1 hy)⟩
  have fD' : Module.Finite (Int0 v)
      ↥((Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ) :=
    Module.Finite.iff_fg.mpr (by rw [hFHt]; exact (hfgFt.map _).sup fgK)
  have fD : Module.Finite (Int0 v) ↥(eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ) :=
    Module.Finite.iff_fg.mpr (fgH.sup fgK)
  have hmapcD' : ((Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ).map
      (comp a N τ) = (eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil)) := by
    rw [Submodule.map_sup, hKc, sup_bot_eq, hFHt, Submodule.map_comp]
  have s1 : RelLen v ((Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ)
      (Fil.restrictScalars (Int0 v)) m := by
    refine (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htfO (comp a N τ) _ _ hD'F ?_ fF fD' m).2 ?_
    · rintro x ⟨hxF, hx0⟩
      exact Submodule.mem_sup_right ((m3 x).2 ⟨hxF, (hker' x).1 hx0⟩)
    · rw [hmapcD']; exact hm
  have s2 := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htf (mulR a N (lin a τ)) _ _ hD'F (by
      rintro x ⟨hxF, hx0⟩
      exact Submodule.mem_sup_left ⟨hxF, hkerA x hx0⟩) fF fD' m).1 s1
  have hDA' : ((Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ).map
      (mulR a N (lin a τ)) = (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ).map (mulR a N (lin a τ)) := by
    have h0 : (Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)).map (mulR a N (lin a τ)) = ⊥ :=
      le_bot_iff.1 (hHA ▸ Submodule.map_mono inf_le_right)
    rw [Submodule.map_sup, Submodule.map_sup, h0, hHA]
  have s3 : RelLen v (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ)
      (eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v)) m := by
    refine (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htf (mulR a N (lin a τ)) _ _ hDB ?_ fB fD m).2 ?_
    · rintro x ⟨-, hx0⟩; exact Submodule.mem_sup_left (hkerA x hx0)
    · rw [← hDA', hmapB_A]; exact s2
  have s4 := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htfO (comp a N τ) _ _ hDB (by
      rintro x ⟨hxB, hx0⟩
      obtain ⟨h, hh, f', hf', rfl⟩ := Submodule.mem_sup.1 hxB
      have hP0 : cofac a τ • (h + f') = 0 := (hker' _).1 hx0
      have hdh : d • h ∈ Fil := by
        rw [hPh h ((m1 h).1 hh)]
        have e1 : cofac a τ • h = -(cofac a τ • f') :=
          eq_neg_of_add_eq_zero_left (by rw [← smul_add]; exact hP0)
        rw [e1]; exact Fil.neg_mem (Fil.smul_mem _ hf')
      have hhF := hsat d h hd0 hdh
      exact Submodule.mem_sup_right ((m3 _).2 ⟨Fil.add_mem hhF hf', hP0⟩)) fB fD m).1 s3
  have hDc : (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ).map (comp a N τ) =
      (eigSub a τ (Fin N → RS a)).map (comp a N τ) := by
    rw [Submodule.map_sup, hKc, sup_bot_eq]
  rw [hDc] at s4
  have s5 := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htfO (comp a N τ) _ _ hBX (by
      rintro x ⟨hxX, hx0⟩
      exact Submodule.mem_sup_right (hXker ⟨hxX, hx0⟩)) fX fB δ).1 hδ
  have s6 := GlobalTheory.T.relLen_trans_add C v _ _ _ _ δ m s4 s5
  have hrδ : r = δ + m := RelLen.unique v hlen s6
  refine ⟨δ, e₂, m, ha1, hb, he₂, hm, ?_, ?_⟩
  · rw [hsum, hfr, hjr]
  · intro hall
    have hy : yExp v a Fil τ = eigRank v a Fil τ • vd v a τ := by
      unfold yExp vd
      rw [Finset.sum_congr rfl (fun s _ => by rw [hall s]), ← Finset.smul_sum,
        addVal_prod v]
      congr 1
      exact Finset.sum_congr rfl (fun s _ => v.map_sub_swap _ _)
    have hrj : r = (eigRank v a Fil τ : ℝ) * rd := by
      have : (r : WithTop ℝ) = (((eigRank v a Fil τ : ℝ) * rd : ℝ) : WithTop ℝ) := by
        rw [hr, hy, hjr]
      exact_mod_cast this
    have hδ0 := relLen_nonneg hδ
    have hm0 := relLen_nonneg hm
    have he0 := relLen_nonneg he₂
    rw [hfr] at hsum
    rw [hjr]
    refine ⟨hδ0, ?_, hm0, ?_⟩
    · exact WithTop.coe_le_coe.2 (by linarith)
    · exact WithTop.coe_le_coe.2 (by linarith)

theorem lengthIdentities_of_relLen : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ∀ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ → RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ)) ((preEig a Fil τ).map (comp a N τ)) r → LengthIdentities v a Fil τ :=
  fun C _ v S _ _ a ha N Fil hsat τ r hr hlen =>
    herbrand_lengthIdentities_auxiliary_bound C v S a ha N Fil hsat τ r hr hlen

end GlobalTheory.HerbLen
end
end

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.herbrand_lengthIdentities_of_relativeLength : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ∀ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ → RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ)) ((preEig a Fil τ).map (comp a N τ)) r → LengthIdentities v a Fil τ := by
  atlas_forward_decl GlobalTheory.HerbLen.lengthIdentities_of_relLen
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory.HerbrandAlg

theorem kerId : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, KernelIdentity v a Fil τ := by
  intro C _ v S _ _ a ha N Fil hF τ
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : lin a τ • x = 0 := hx
    show lin a τ • (Submodule.Quotient.mk x : (Fin N → RS a) ⧸ Fil) = 0
    rw [← Submodule.Quotient.mk_smul, hx', Submodule.Quotient.mk_zero]
  · ext x
    constructor
    · rintro ⟨hx, hk⟩
      have hx' : lin a τ • x = 0 := hx
      have hxF : x ∈ Fil := (Submodule.Quotient.mk_eq_zero Fil).1 hk
      refine ⟨⟨x, hxF⟩, ?_, rfl⟩
      show lin a τ • (⟨x, hxF⟩ : Fil) = 0
      exact Subtype.ext hx'
    · rintro ⟨⟨y, hy⟩, hy', rfl⟩
      have hy'' : lin a τ • (⟨y, hy⟩ : Fil) = 0 := hy'
      refine ⟨?_, ?_⟩
      · show lin a τ • y = 0
        exact congrArg Subtype.val hy''
      · show (Submodule.Quotient.mk y : (Fin N → RS a) ⧸ Fil) = 0
        exact (Submodule.Quotient.mk_eq_zero Fil).2 hy

theorem core : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ∃ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ ∧ RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ)) ((preEig a Fil τ).map (comp a N τ)) r := by
  intro C _ v S _ _ a ha N Fil hF τ
  obtain ⟨r, hr, hR⟩ := GlobalTheory.T.relLength_filtrationInterKerCofactor_linearFactor C v S a ha N Fil hF τ
  obtain ⟨hd, hcP, hkerc, hsat, hAX, hHc, hcH, hprojX, hHX, hFX, htf, g, hg⟩ :=
    GlobalTheory.T.adjoinRootProdLinearFactors_lattice_facts C v S a ha N Fil hF τ
  obtain ⟨fF, fX, fK, fH, -, -, -⟩ := GlobalTheory.T.finite_eigenFiltration_pieces_addValInt C v S a ha N Fil hF τ
  have tfO : ∀ (c : Int0 v) (x : Fin N → Int0 v), c ≠ 0 → c • x = 0 → x = 0 := by
    intro c x hc h
    funext i
    have := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_eq_zero] at this
    exact this.resolve_left hc
  have hKF : filKer a Fil τ ≤ Fil.restrictScalars (Int0 v) := inf_le_left
  have fKs : Module.Finite (Int0 v) ↥(eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ) := by
    rw [Module.Finite.iff_fg] at fH fK ⊢
    exact fH.sup fK
  have hle : eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ ≤ preEig a Fil τ :=
    sup_le hHX (hKF.trans hFX)
  have hA : preEig a Fil τ ⊓ LinearMap.ker (mulR a N (lin a τ)) ≤
      eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ := fun x hx =>
    Submodule.mem_sup_left (LinearMap.mem_ker.1 hx.2)
  have hmapH : (eigSub a τ (Fin N → RS a)).map (mulR a N (lin a τ)) = ⊥ :=
    eq_bot_iff.2 (by rintro _ ⟨x, hx, rfl⟩; exact (Submodule.mem_bot _).2 hx)
  have e1 : (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ).map (mulR a N (lin a τ)) =
      (filKer a Fil τ).map (mulR a N (lin a τ)) := by
    rw [Submodule.map_sup, hmapH, bot_sup_eq]
  have s1 : RelLen v (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ) (preEig a Fil τ) r :=
    (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htf (mulR a N (lin a τ)) _ _ hle hA fX fKs r).2 (by rw [e1, hAX]; exact hR)
  have hC : preEig a Fil τ ⊓ LinearMap.ker (comp a N τ) ≤
      eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ := fun x hx =>
    Submodule.mem_sup_right ⟨hsat hx, LinearMap.mem_ker.2 ((hcP x).1 (LinearMap.mem_ker.1 hx.2))⟩
  have s2 := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf tfO (comp a N τ) _ _ hle hC fX fKs r).1 s1
  have hK0 : (filKer a Fil τ).map (comp a N τ) = ⊥ :=
    eq_bot_iff.2 (by
      rintro _ ⟨x, hx, rfl⟩
      exact (Submodule.mem_bot _).2 ((hcP x).2 (LinearMap.mem_ker.1 hx.2)))
  have e2 : (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ).map (comp a N τ) =
      (eigSub a τ (Fin N → RS a)).map (comp a N τ) := by
    rw [Submodule.map_sup, hK0, sup_bot_eq]
  exact ⟨r, hr, e2 ▸ s2⟩

theorem herbrandDet : HerbrandDet := by
  intro C _ v S _ _ a ha N Fil hF τ
  obtain ⟨r, hr, hR⟩ := core C v S a ha N Fil hF τ
  exact ⟨GlobalTheory.T.herbrand_determinant_identity_of_relativeLength C v S a ha N Fil hF τ r hr hR, kerId C v S a ha N Fil hF τ,
    GlobalTheory.T.herbrand_lengthIdentities_of_relativeLength C v S a ha N Fil hF τ r hr hR⟩

end GlobalTheory.HerbrandAlg
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.herbrandQuotient_eigen_det : GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.HerbrandDet := by
  atlas_forward_decl GlobalTheory.HerbrandAlg.herbrandDet
end
