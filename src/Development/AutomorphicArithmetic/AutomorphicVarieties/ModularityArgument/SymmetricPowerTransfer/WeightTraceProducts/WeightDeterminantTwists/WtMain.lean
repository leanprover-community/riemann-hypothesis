import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.FinMH
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.MemHomogeneousExponentsOneBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.HomogeneousTraceDiagonal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.HOption

section
open Polynomial
namespace UpperTheory.V.Z.Sym.Wt

private theorem map_invT {R : Type} [CommRing R] (f : R →+* ℂ) (d : ℕ) (g : GL (Fin d) R) :
    Matrix.GeneralLinearGroup.map f (invT R d g) = invT ℂ d (Matrix.GeneralLinearGroup.map f g) := by
  ext i k
  rw [Matrix.GeneralLinearGroup.map_apply, invT_val, invT_val, ← map_inv, Matrix.transpose_apply,
    Matrix.transpose_apply, Matrix.GeneralLinearGroup.map_apply]

private theorem map_scal {R : Type} [CommRing R] (f : R →+* ℂ) (d : ℕ) (x : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin d) x) =
      Matrix.GeneralLinearGroup.scalar (Fin d) (Units.map f.toMonoidHom x) := by
  ext i k
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply, apply_ite f]

private theorem val_map {R : Type} [CommRing R] (f : R →+* ℂ) (d : ℕ) (g : GL (Fin d) R) :
    ((Matrix.GeneralLinearGroup.map f g : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) = (g : Matrix (Fin d) (Fin d) R).map f := rfl

theorem wtMain_of (h1 : FinMH) (h2 : ThFacts) (h3 : TwineC) (h4 : TrDC) (h5 : Scalars) (h6 : HqKappa) : WtMain := by
  intro R I _ _ em j hj
  classical
  have hWG : ∀ g : GL (Fin 3) R,
      WG em j g = repG I j (fun w => Matrix.GeneralLinearGroup.map (em w) g) := fun _ => rfl
  have hWD : ∀ (n : ℕ) (e : ℤ) (g : GL (Fin 2) R),
      WD em n e g = repD I n e (fun w => Matrix.GeneralLinearGroup.map (em w) g) := fun _ _ _ => rfl
  have hdet : ∀ (w : I) (g : GL (Fin 2) R),
      ((Matrix.GeneralLinearGroup.map (em w) g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det =
        em w (g : Matrix (Fin 2) (Fin 2) R).det := by
    intro w g
    rw [val_map, RingHom.map_det]
    rfl
  have htr : ∀ (w : I) (g : GL (Fin 2) R),
      ((Matrix.GeneralLinearGroup.map (em w) g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace =
        em w (g : Matrix (Fin 2) (Fin 2) R).trace := by
    intro w g
    rw [val_map, AddMonoidHom.map_trace]
  refine
    { finG := ?_, finD := ?_, th_sq := (h2 I j).1, th_rep := ?_, scalG := ?_, scalD := ?_,
      twine := ?_, stable := ?_, kappa := ?_ }
  · haveI : ∀ S : I → Bool, FiniteDimensional ℂ (Bi 3 (dg j S)) := fun S => h1 _ _ _
    infer_instance
  · intro n
    exact h1 _ _ _
  · intro g
    rw [hWG, hWG, (h2 I j).2]
    have hfun : (fun v => invT ℂ 3 (Matrix.GeneralLinearGroup.map (em v) g)) =
        fun w => Matrix.GeneralLinearGroup.map (em w) (invT R 3 g) :=
      funext fun v => (map_invT _ _ _).symm
    rw [hfun]
  · intro x
    rw [hWG]
    have hfun : (fun w => Matrix.GeneralLinearGroup.map (em w) (Matrix.GeneralLinearGroup.scalar (Fin 3) x)) =
        fun w => Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map (em w).toMonoidHom x) :=
      funext fun w => map_scal _ _ _
    rw [hfun]
    exact (h5 I _).1 j
  · intro n e x
    rw [hWD]
    have hfun : (fun w => Matrix.GeneralLinearGroup.map (em w) (Matrix.GeneralLinearGroup.scalar (Fin 2) x)) =
        fun w => Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (em w).toMonoidHom x) :=
      funext fun w => map_scal _ _ _
    rw [hfun, (h5 I _).2 n e]
    congr 1
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Units.val_zpow_eq_zpow_val, Units.coe_map]
    rfl
  · intro δ τ hch
    rw [hWG]
    refine h3 I j hj (fun w => Matrix.GeneralLinearGroup.map (em w) δ) (fun w => em w τ) ?_
    intro v
    rw [← map_invT, ← map_mul, val_map, Matrix.charpoly_map, hch]
    simp [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add]
  · intro e γ hγ
    rw [hWD, h4]
    show _ = ∏ w, hq (em w (γ : Matrix (Fin 2) (Fin 2) R).trace) 1 j
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [hdet, htr, hγ, map_one, one_zpow, one_mul]
  · intro z τ htz hdz
    rw [hWD, h4]
    show _ = ∏ w, hq (em w τ) 1 j
    refine Finset.prod_congr rfl fun w _ => ?_
    have hu : em w (z : Matrix (Fin 2) (Fin 2) R).det ≠ 0 := by
      have hz : IsUnit (z : Matrix (Fin 2) (Fin 2) R).det := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]
        exact Units.isUnit _
      exact (hz.map (em w)).ne_zero
    rw [hdet, htr, htz, hdz, map_add, map_ofNat, h6 j (em w τ)]
    rw [hdz, map_add, map_ofNat] at hu
    rw [zpow_neg, show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      inv_mul_cancel_left₀ (pow_ne_zero _ hu)]

end UpperTheory.V.Z.Sym.Wt
end

section
open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem swp_eval {I : Type} [Fintype I] {d : ℕ} (n : I → ℕ) (Q : Bi d n) (x : (I × Bool) × Fin d → ℂ) :
    MvPolynomial.eval x (swp d n Q).1 = MvPolynomial.eval (x ∘ UpperTheory.V.Z.Sym.Wt.flip I d) Q.1 := MvPolynomial.eval_rename _ _ _

theorem UpperTheory.V.Z.Sym.Wt.thFacts :
    UpperTheory.V.Z.Sym.Wt.ThFacts := by
  intro I _ j
  have key : ∀ (n : I → ℕ) (g : I → GL (Fin 3) ℂ) (P : Bi 3 n),
      swp 3 n (biRep 3 n g P) = biRep 3 n (fun v => invT ℂ 3 (g v)) (swp 3 n P) := by
    intro n g P
    apply Subtype.ext
    apply MvPolynomial.funext
    intro x
    rw [swp_eval]
    change MvPolynomial.eval _ ((mRep 3 (fun k => n k.1) (dbl 3 g)) P).1 =
      MvPolynomial.eval x ((mRep 3 (fun k => n k.1) (dbl 3 (fun v => invT ℂ 3 (g v)))) (swp 3 n P)).1
    rw [eval_mRep, eval_mRep, swp_eval]
    refine congrArg (fun y => MvPolynomial.eval y P.1) ?_
    funext p
    obtain ⟨⟨v, b⟩, i⟩ := p
    cases b <;> simp [act, UpperTheory.V.Z.Sym.Wt.flip, dbl, invT_invT]
  have hswp : ∀ (n : I → ℕ) (P : Bi 3 n), swp 3 n (swp 3 n P) = P := by
    intro n P
    apply Subtype.ext
    apply MvPolynomial.funext
    intro x
    rw [swp_eval, swp_eval]
    refine congrArg (fun y => MvPolynomial.eval y P.1) ?_
    funext p
    simp [UpperTheory.V.Z.Sym.Wt.flip]
  have hsg : ∀ S : I → Bool, sg S * sg S = 1 := by
    intro S
    simp only [sg, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro v _
    split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · apply LinearMap.ext
    intro P
    funext S
    simp only [Module.End.mul_apply, thG_apply, map_smul, smul_smul, hswp, hsg, one_smul, Module.End.one_apply]
  · intro g
    apply LinearMap.ext
    intro P
    funext S
    simp only [Module.End.mul_apply, thG_apply, repG_apply, map_smul, key]
end

section
open Polynomial UpperTheory.V.Z.Sym.Wt

open MvPolynomial in
private theorem homogeneous_trace_mul {d : ℕ} (n : ℕ) (g h : GL (Fin d) ℂ) :
    tr1 d n (g * h) = ∑ p ∈ deg1 d n ×ˢ deg1 d n, coeff p.1 (sbs (fun _ : Unit => g) (monomial p.2 1)) *
      coeff p.2 (sbs (fun _ : Unit => h) (monomial p.1 1)) := by
  classical
  have hcomp : ∀ P, sbs (fun _ : Unit => g * h) P = sbs (fun _ : Unit => g) (sbs (fun _ : Unit => h) P) := by
    intro P
    apply MvPolynomial.funext
    intro x
    rw [eval_sbs, eval_sbs, eval_sbs, ← act_mul]
    rfl
  rw [symPowTrace_eq_sum_coeff, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m hm
  have hmono : (monomial m (1 : ℂ)) ∈ MH d (fun _ : Unit => n) := by
    refine (memMH Unit d (fun _ => n) _).2 ?_
    intro m0 hm0 k
    rw [Finset.mem_singleton.1 (MvPolynomial.support_monomial_subset hm0)]
    exact mem_homogeneousExponentsOneBlock.1 hm
  have hQ := sbs_mem (fun _ : Unit => h) hmono
  have hQsum : sbs (fun _ : Unit => h) (monomial m 1) =
      ∑ m' ∈ deg1 d n, monomial m' (coeff m' (sbs (fun _ : Unit => h) (monomial m 1))) := by
    conv_lhs => rw [(sbs (fun _ : Unit => h) (monomial m 1)).as_sum]
    apply Finset.sum_subset
    · intro m' hm'
      rw [mem_homogeneousExponentsOneBlock]
      exact (memMH Unit d (fun _ => n) _).1 hQ m' hm' ()
    · intro m' _ hm'
      rw [MvPolynomial.notMem_support_iff.1 hm', monomial_zero]
  rw [hcomp]
  conv_lhs => rw [hQsum]
  rw [map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro m' _
  rw [show monomial m' (coeff m' (sbs (fun _ : Unit => h) (monomial m 1))) =
      coeff m' (sbs (fun _ : Unit => h) (monomial m 1)) • monomial m' (1 : ℂ) by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, MvPolynomial.coeff_smul, smul_eq_mul, mul_comm]

theorem UpperTheory.V.Z.Sym.Wt.trSwap :
    UpperTheory.V.Z.Sym.Wt.TrSwap := by
  classical
  intro I _ d n g
  have hinv : ∀ p, UpperTheory.V.Z.Sym.Wt.flip I d (UpperTheory.V.Z.Sym.Wt.flip I d p) = p := by
    intro p
    simp [UpperTheory.V.Z.Sym.Wt.flip]
  have hinj : Function.Injective (UpperTheory.V.Z.Sym.Wt.flip I d) := Function.LeftInverse.injective hinv
  have hglue : ∀ μ : I × Bool → Unit × Fin d →₀ ℕ,
      Finsupp.mapDomain (UpperTheory.V.Z.Sym.Wt.flip I d) (glue μ) = glue (fun k => μ (k.1, !k.2)) := by
    intro μ
    ext ⟨⟨i, b⟩, j⟩
    have := Finsupp.mapDomain_apply hinj (glue μ) ((i, !b), j)
    rw [show UpperTheory.V.Z.Sym.Wt.flip I d ((i, !b), j) = ((i, b), j) by
      simp [UpperTheory.V.Z.Sym.Wt.flip]] at this
    rw [this, glue_apply, glue_apply]
  rw [trace_blocks (K := I × Bool) (fun k => n k.1)
    ((sbs (dbl d g)).toLinearMap.comp (MvPolynomial.rename (UpperTheory.V.Z.Sym.Wt.flip I d)).toLinearMap)
    (biRep d n g * swp d n) (fun P => rfl)]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPolynomial.rename_monomial, hglue,
    coeff_sbs_glue]
  simp_rw [homogeneous_trace_mul]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_nbij' (fun μ v => (μ (v, false), μ (v, true)))
    (fun x k => if k.2 then (x k.1).2 else (x k.1).1) ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    rw [Fintype.mem_piFinset] at hμ ⊢
    intro v
    exact Finset.mem_product.2 ⟨hμ (v, false), hμ (v, true)⟩
  · intro x hx
    rw [Fintype.mem_piFinset] at hx ⊢
    rintro ⟨v, b⟩
    cases b
    · exact (Finset.mem_product.1 (hx v)).1
    · exact (Finset.mem_product.1 (hx v)).2
  · intro μ _
    funext ⟨v, b⟩
    cases b <;> rfl
  · intro x _
    rfl
  · intro μ _
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro v _
    rw [Fintype.prod_bool]
    show MvPolynomial.coeff (μ (v, true))
        ((sbs fun _ : Unit => invT ℂ d (g v)) (MvPolynomial.monomial (μ (v, false)) 1)) *
      MvPolynomial.coeff (μ (v, false))
        ((sbs fun _ : Unit => g v) (MvPolynomial.monomial (μ (v, true)) 1)) = _
    exact mul_comm _ _
end

section
open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem hs_opt {σ : Type} [Fintype σ] [DecidableEq σ] (x : Option σ → ℂ) (j : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Option σ) ℂ (j + 1)) =
      x none * MvPolynomial.eval x (MvPolynomial.hsymm (Option σ) ℂ j) +
        MvPolynomial.eval (x ∘ some) (MvPolynomial.hsymm σ ℂ (j + 1)) := by
  have ev : ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (y : τ → ℂ) (n : ℕ),
      MvPolynomial.eval y (MvPolynomial.hsymm τ ℂ n) = ∑ s : Sym τ n, ((s : Multiset τ).map y).prod := by
    intro τ _ _ y n
    rw [MvPolynomial.hsymm, map_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [map_multiset_prod, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl (fun a _ => MvPolynomial.eval_X _)
  rw [ev, ev, ev]
  rw [← (symOptionSuccEquiv (α := σ) (n := j)).symm.sum_comp, Fintype.sum_sum_type, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    show ((none ::ₘ (s : Multiset (Option σ))).map x).prod = _
    rw [Multiset.map_cons, Multiset.prod_cons]
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    show ((Multiset.map some (s : Multiset σ)).map x).prod = _
    rw [Multiset.map_map]

private theorem hs_succ {d : ℕ} (x : Fin (d + 1) → ℂ) (k : Fin (d + 1)) (j : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Fin (d + 1)) ℂ (j + 1)) =
      x k * MvPolynomial.eval x (MvPolynomial.hsymm (Fin (d + 1)) ℂ j) +
        MvPolynomial.eval (x ∘ k.succAbove) (MvPolynomial.hsymm (Fin d) ℂ (j + 1)) := by
  have e1 : ∀ n, MvPolynomial.hsymm (Fin (d + 1)) ℂ n =
      MvPolynomial.rename (finSuccEquiv' k).symm (MvPolynomial.hsymm (Option (Fin d)) ℂ n) :=
    fun n => (MvPolynomial.rename_hsymm (Option (Fin d)) ℂ n (finSuccEquiv' k).symm).symm
  rw [e1, e1, MvPolynomial.eval_rename, MvPolynomial.eval_rename, hs_opt]
  have h1 : (x ∘ (finSuccEquiv' k).symm) none = x k := by simp
  have h2 : (x ∘ (finSuccEquiv' k).symm) ∘ some = x ∘ k.succAbove := by
    ext i
    simp
  rw [h1, h2]

theorem UpperTheory.V.Z.Sym.Wt.hqThree :
    UpperTheory.V.Z.Sym.Wt.HqThree := by
  intro j a b
  have hv : (![a, 1, b] ∘ (1 : Fin 3).succAbove) = ![a, b] := by
    ext i
    fin_cases i <;> rfl
  rw [hs_succ ![a, 1, b] 1 j, hv, UpperTheory.V.Z.Sym.Wt.hqTwo]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, one_mul]
  ring
end

section
open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem tr_pi {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)] (f : ∀ i, Module.End ℂ (V i)) (F : Module.End ℂ (∀ i, V i)) (h : ∀ x i, F x i = f i (x i)) :
    LinearMap.trace ℂ _ F = ∑ i, LinearMap.trace ℂ _ (f i) := by
  have e : F = ∑ i, (LinearMap.single ℂ V i) ∘ₗ (f i ∘ₗ LinearMap.proj i) := by
    refine LinearMap.ext fun x => funext fun k => ?_
    rw [h, LinearMap.sum_apply, Finset.sum_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb.symm]
    · simp
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.trace_comp_comm']
  congr 1
  ext x
  simp

theorem UpperTheory.V.Z.Sym.Wt.twineC :
    UpperTheory.V.Z.Sym.Wt.TwineC := by
  intro I _ _ j hj g τ h
  haveI : ∀ S : I → Bool, FiniteDimensional ℂ (Bi 3 (dg j S)) := fun S => finMH _ _ _
  rw [tr_pi (fun S : I → Bool => sg S • (biRep 3 (dg j S) g * swp 3 (dg j S))) _ fun x S => by
    rw [Module.End.mul_apply, repG_apply, thG_apply, map_smul]; rfl]
  simp only [map_smul, trSwap _, smul_eq_mul, sg, ← Finset.prod_mul_distrib, dg]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ : I => (Finset.univ : Finset Bool))
    fun v b => (if b = true then (-1 : ℂ) else 1) * tr1 3 (if b = true then j - 1 else j) (g v * invT ℂ 3 (g v))]
  refine Finset.prod_congr rfl fun v _ => ?_
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a * a = τ v ^ 2 - 4 := IsAlgClosed.exists_eq_mul_self _ |>.imp fun _ h => h.symm
  have h1 : (τ v + a) / 2 + (τ v - a) / 2 = τ v := by ring
  have h2 : (τ v + a) / 2 * ((τ v - a) / 2) = 1 := by linear_combination (-1 / 4 : ℂ) * ha
  have hc : ((g v * invT ℂ 3 (g v) : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ).charpoly =
      ∏ i, (X - C (![(τ v + a) / 2, 1, (τ v - a) / 2] i)) := by
    rw [h, Fin.prod_univ_three]
    have e1 := congrArg (C : ℂ →+* ℂ[X]) h1
    have e2 := congrArg (C : ℂ →+* ℂ[X]) h2
    rw [map_add] at e1
    rw [map_mul, map_one] at e2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_one]
    linear_combination (X - 1) * X * e1 - (X - 1) * e2
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have := hqThree k ((τ v + a) / 2) ((τ v - a) / 2)
  rw [h1, h2] at this
  rw [Fintype.sum_bool, ← this]
  simp only [if_true, Bool.false_eq_true, if_false, Nat.add_sub_cancel, trOne _ _ _ _ hc]
  ring
end

section
open Polynomial UpperTheory.V.Z.Sym.Wt

theorem UpperTheory.V.Z.Sym.Wt.trProd :
    UpperTheory.V.Z.Sym.Wt.TrProd := by
  classical
  intro K _ d n g
  rw [trace_blocks n (sbs g).toLinearMap (mRep d n g) (fun P => rfl)]
  simp only [AlgHom.toLinearMap_apply]
  simp_rw [coeff_sbs_glue, symPowTrace_eq_sum_coeff]
  rw [Finset.prod_univ_sum]
end

section
open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem tr1_two_eq_hq_trace_det (g : GL (Fin 2) ℂ) (n : ℕ) :
    tr1 2 n g = hq (↑g : Matrix (Fin 2) (Fin 2) ℂ).trace (↑g : Matrix (Fin 2) (Fin 2) ℂ).det n := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := ↑g with hA
  have hs : A.charpoly.Splits := IsAlgClosed.splits _
  have hcard : Multiset.card A.charpoly.roots = 2 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard
  have hp : A.charpoly = ∏ i, (X - C (![a, b] i)) := by
    rw [hs.eq_prod_roots_of_monic (Matrix.charpoly_monic A), hab]
    simp [Fin.prod_univ_two]
  have htr : A.trace = a + b := by
    rw [Matrix.trace_eq_sum_roots_charpoly, hab]; simp
  have hdet : A.det = a * b := by
    rw [Matrix.det_eq_prod_roots_charpoly, hab]; simp
  rw [trOne 2 n g ![a, b] hp, hqTwo, htr, hdet]

theorem UpperTheory.V.Z.Sym.Wt.trDC :
    UpperTheory.V.Z.Sym.Wt.TrDC := by
  intro I _ n e g
  rw [repD_apply, map_smul, smul_eq_mul]
  have h := trProd I 2 (fun _ => n) g
  simp only [VD] at *
  rw [h]
  simp only [detE, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    Matrix.GeneralLinearGroup.val_det_apply]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => by rw [tr1_two_eq_hq_trace_det]
end

section
open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem mRep_scal {K : Type} [Fintype K] {d : ℕ} (n : K → ℕ) (s : K → ℂˣ) (Q : MH d n) :
    mRep d n (fun k => Matrix.GeneralLinearGroup.scalar (Fin d) (s k)) Q = (∏ k, (s k : ℂ) ^ n k) • Q := by
  apply Subtype.ext
  apply MvPolynomial.funext
  intro x
  rw [eval_mRep]
  have hact : act (fun k => Matrix.GeneralLinearGroup.scalar (Fin d) (s k)) x = fun p => (s p.1 : ℂ) * x p := by
    funext p
    simp [act, Matrix.scalar_apply, Matrix.diagonal_apply, mul_comm]
  rw [hact, Q.2 (fun k => (s k : ℂ)) x]
  simp

private theorem invT_scal {d : ℕ} (s : ℂˣ) :
    invT ℂ d (Matrix.GeneralLinearGroup.scalar (Fin d) s) = Matrix.GeneralLinearGroup.scalar (Fin d) s⁻¹ := by
  refine Units.ext ?_
  rw [invT_val, ← map_inv]
  exact Matrix.diagonal_transpose _

theorem UpperTheory.V.Z.Sym.Wt.scalars :
    UpperTheory.V.Z.Sym.Wt.Scalars := by
  intro I _ s
  refine ⟨fun j => ?_, fun n e => ?_⟩
  · have hd : dbl 3 (fun v ↦ Matrix.GeneralLinearGroup.scalar (Fin 3) (s v)) =
        fun k => Matrix.GeneralLinearGroup.scalar (Fin 3) (if k.2 then (s k.1)⁻¹ else s k.1) := by
      funext k
      obtain ⟨v, b⟩ := k
      cases b <;> simp [dbl, invT_scal]
    apply LinearMap.ext
    intro P
    funext S
    rw [repG_apply, Module.End.one_apply]
    change mRep 3 (fun k => dg j S k.1) (dbl 3 _) (P S) = P S
    rw [hd, mRep_scal]
    convert one_smul ℂ (P S)
    rw [Fintype.prod_prod_type]
    apply Finset.prod_eq_one
    intro v _
    rw [Fintype.prod_bool]
    simp
  · apply LinearMap.ext
    intro P
    rw [repD_apply, LinearMap.smul_apply, mRep_scal, smul_smul, LinearMap.smul_apply, Module.End.one_apply]
    congr 1
    simp only [detE, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val]
    simp
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have ha : (s v : ℂ) ≠ 0 := (s v).ne_zero
    rw [zpow_add₀ ha, zpow_mul, zpow_natCast, mul_comm]
    norm_cast
end

section
open Polynomial
namespace UpperTheory.V.Z.Sym.Wt
private theorem hq_kap (τ : ℂ) (j : ℕ) : hq (2 + τ) (2 + τ) (2 * j + 1) = (2 + τ) ^ (j + 1) * hq τ 1 j ∧ hq (2 + τ) (2 + τ) (2 * (j+1) + 1) = (2 + τ) ^ (j + 2) * hq τ 1 (j+1) := by
  have e : ∀ i, hq (2 + τ) (2 + τ) (i + 2) = (2 + τ) * hq (2 + τ) (2 + τ) (i + 1) - (2 + τ) * hq (2 + τ) (2 + τ) i :=
    fun i => hq.eq_3 _ _ i
  have f : ∀ i, hq τ 1 (i + 2) = τ * hq τ 1 (i + 1) - 1 * hq τ 1 i := fun i => hq.eq_3 _ _ i
  induction j with
  | zero =>
    have e2 : hq (2 + τ) (2 + τ) 2 = (2 + τ) * hq (2 + τ) (2 + τ) 1 - (2 + τ) * hq (2 + τ) (2 + τ) 0 := e 0
    have e3 : hq (2 + τ) (2 + τ) 3 = (2 + τ) * hq (2 + τ) (2 + τ) 2 - (2 + τ) * hq (2 + τ) (2 + τ) 1 := e 1
    refine ⟨?_, ?_⟩
    · show hq (2 + τ) (2 + τ) 1 = (2 + τ) ^ 1 * hq τ 1 0
      rw [hq.eq_2, hq.eq_1]
      ring
    · show hq (2 + τ) (2 + τ) 3 = (2 + τ) ^ 2 * hq τ 1 1
      rw [e3, e2, hq.eq_2, hq.eq_1, hq.eq_2]
      ring
  | succ j ih =>
    refine ⟨ih.2, ?_⟩
    have e5 : hq (2 + τ) (2 + τ) (2 * j + 5) =
        (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 4) - (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 3) := e (2 * j + 3)
    have e4 : hq (2 + τ) (2 + τ) (2 * j + 4) =
        (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 3) - (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 2) := e (2 * j + 2)
    have e3 : hq (2 + τ) (2 + τ) (2 * j + 3) =
        (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 2) - (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 1) := e (2 * j + 1)
    have f2 : hq τ 1 (j + 2) = τ * hq τ 1 (j + 1) - 1 * hq τ 1 j := f j
    have i0 : hq (2 + τ) (2 + τ) (2 * j + 1) = (2 + τ) ^ (j + 1) * hq τ 1 j := ih.1
    have i1 : hq (2 + τ) (2 + τ) (2 * j + 3) = (2 + τ) ^ (j + 2) * hq τ 1 (j + 1) := ih.2
    show hq (2 + τ) (2 + τ) (2 * j + 5) = (2 + τ) ^ (j + 3) * hq τ 1 (j + 2)
    rw [f2]
    linear_combination e5 + (2 + τ) * e4 + (2 + τ) * e3 + ((2 + τ) ^ 2 - 2 * (2 + τ)) * i1 - (2 + τ) ^ 2 * i0
theorem hqKappa : HqKappa := fun j τ => (hq_kap τ j).1
end UpperTheory.V.Z.Sym.Wt
end

section
theorem UpperTheory.V.Z.Sym.Wt.wtMain : UpperTheory.V.Z.Sym.Wt.WtMain :=
  UpperTheory.V.Z.Sym.Wt.wtMain_of UpperTheory.V.Z.Sym.Wt.finMH UpperTheory.V.Z.Sym.Wt.thFacts UpperTheory.V.Z.Sym.Wt.twineC UpperTheory.V.Z.Sym.Wt.trDC
    UpperTheory.V.Z.Sym.Wt.scalars UpperTheory.V.Z.Sym.Wt.hqKappa
end
