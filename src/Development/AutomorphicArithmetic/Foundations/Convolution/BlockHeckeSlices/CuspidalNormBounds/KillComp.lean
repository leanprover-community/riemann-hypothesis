import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.HkApply
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.BandOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CompBound
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CommuteCenterRtInfGL
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.AbsTaylor
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.LiftSingle
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.SubEqZeroIff
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ExistsFinMap
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoeffProdOneAdd

section
open NumberField MvPolynomial PositivityTheory.Rg.Fx

private theorem vars_pieceK {ι κ : Type} [Fintype ι] (k : ℕ) (F : KF ι κ) : ∀ j ∈ (pieceK k F).vars, j ∈ F.vars := by
  classical
  intro j hj
  rw [mem_vars_iff_mem_support] at hj ⊢
  obtain ⟨d, hd, hjd⟩ := hj
  refine ⟨d, ?_, hjd⟩
  by_contra hn
  apply mem_support_iff.mp hd
  unfold pieceK
  rw [coeff_sum]
  refine Finset.sum_eq_zero fun β hβ => ?_
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact hn hβ

private theorem congr_mod {σ κ A : Type} [CommRing A] [Algebra ℂ A] (J : Ideal A) (Z X : σ → A) (e : σ → MvPolynomial σ ℂ)
    (H H' : κ → A) (G P : MvPolynomial κ (MvPolynomial σ ℂ)) (hZ : ∀ p, Z p - aeval X (e p) ∈ J)
    (hH : ∀ k ∈ P.vars, H k - H' k ∈ J)
    (hG : map (aeval e : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ).toRingHom G = P) :
    eval₂ (aeval Z).toRingHom H G - eval₂ (aeval X).toRingHom H' P ∈ J := by
  rw [← Ideal.Quotient.eq]
  have h1 : (Ideal.Quotient.mkₐ ℂ J).comp (aeval Z) = ((Ideal.Quotient.mkₐ ℂ J).comp (aeval X)).comp (aeval e) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq.mpr (hZ p)
  have h2 : (Ideal.Quotient.mk J).comp (aeval Z).toRingHom =
      ((Ideal.Quotient.mk J).comp (aeval X).toRingHom).comp
        (aeval e : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ).toRingHom :=
    RingHom.ext fun p => DFunLike.congr_fun h1 p
  rw [eval₂_comp_left, eval₂_comp_left, h2, ← eval₂_map, hG]
  refine eval₂Hom_congr' rfl (fun j hj _ => ?_) rfl
  exact Ideal.Quotient.eq.mpr (hH j hj)

theorem UpperTheory.ConvolutionTheory.BW.absKill :
    UpperTheory.ConvolutionTheory.BW.AbsKill := by
  intro τ κ A V _ _ n r _ _ _ _ _ _ Z H I t c idx Λ h good C hS F G hgood hev hG φ x
  classical
  obtain ⟨τ₀⟩ := ‹Nonempty τ›
  choose s hs using hS.surj
  let b : Fam (τ × Fin n) κ :=
    { r := r
      Λ := Λ
      emb := Matrix.of fun p j => if idx p.2 = j then 1 else 0
      pr := Matrix.of fun j p => if p = (τ₀, s j) then 1 else 0
      pr_emb := by
        ext i j
        rw [Matrix.mul_apply, Finset.sum_eq_single (τ₀, s i) (fun p _ hp => by simp [hp]) (by simp)]
        simp [hs, Matrix.one_apply]
      h := h }
  have hsub : b.sub F = 0 := by
    rw [UpperTheory.ConvolutionTheory.FX.sub_eq_zero_iff]
    rintro Λ' h' ⟨z, h1, h2⟩
    have e1 : Λ' = fun p => Λ p + z (idx p.2) := by
      funext p
      rw [h1]
      simp [b, apply_ite ((↑) : ℝ → ℂ)]
    have e2 : h' = fun k => ev z (h k) := funext h2
    rw [e1, e2]
    exact hev z
  have key := UpperTheory.ConvolutionTheory.FX.rearrange (τ × Fin n) κ b A V I t ((LinearMap.proj x).comp c)
    (fun v m => UpperTheory.ConvolutionTheory.FX.abs_taylor τ κ A V n r Z H I t c idx Λ h good C hS v x m) F φ
  rw [hsub, map_zero, zero_smul, map_zero] at key
  let J : Ideal A :=
    { carrier := {a | ∀ ψ, c (a • ψ) = 0}
      add_mem' := fun {a a'} ha ha' ψ => by rw [add_smul, map_add, ha, ha', add_zero]
      zero_mem' := fun ψ => by rw [zero_smul, map_zero]
      smul_mem' := fun a a' ha ψ => by rw [smul_eq_mul, mul_comm, mul_smul]; exact ha _ }
  have hJ : ∀ a a' : A, a - a' ∈ J ↔ ∀ ψ, c (a • ψ) = c (a' • ψ) := fun a a' =>
    forall_congr' fun ψ => by rw [sub_smul, map_sub, sub_eq_zero]
  have hX : (fun i : τ × Fin n => algebraMap ℂ A (b.Λ i) + ∑ j, (b.emb i j : ℂ) • I j) =
      fun q => algebraMap ℂ A (Λ q) + I (idx q.2) := by
    funext p
    simp [b, apply_ite ((↑) : ℝ → ℂ)]
  rw [hX] at key
  convert key using 2 with k
  have := congr_mod J Z (fun q => algebraMap ℂ A (Λ q) + I (idx q.2)) blockE H (fun k' => lift I t (h k')) (G k)
    (pieceK k F) (fun p => (hJ _ _).mpr (hS.cen p))
    (fun j hj => (hJ _ _).mpr (hS.hecke j (hgood j (vars_pieceK k F j hj)))) (hG k)
  exact congrFun ((hJ _ _).mp this φ) x
end

section
open NumberField

noncomputable section

namespace UpperTheory.ConvolutionTheory.BW

open GlobalTheory.CuspRep PositivityTheory.Rg.Fx UpperTheory.V.Cm

private theorem sum_pi {m j : ℕ} (F : (Fin (m + 1) → ℕ) → ℂ) :
    ∑ A ∈ Finset.piAntidiag Finset.univ j, F A =
      ∑ a ∈ Finset.range (j + 1), ∑ A ∈ Finset.piAntidiag Finset.univ (j - a), F (Fin.cons a A) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun A _ => ⟨A 0, Fin.tail A⟩) (fun p _ => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    simp only [Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true, Fin.sum_univ_succ, Finset.mem_sigma,
      Finset.mem_range] at hA ⊢
    refine ⟨by omega, ?_⟩
    change ∑ i : Fin m, A i.succ = _
    omega
  · intro p hp
    simp only [Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true, Fin.sum_univ_succ, Finset.mem_sigma,
      Finset.mem_range, Fin.cons_zero, Fin.cons_succ] at hp ⊢
    have h2 : ∑ i, p.2 i = j - p.1 := hp.2
    omega
  · intro A _
    exact Fin.cons_self_tail A
  · intro p _
    simp
  · intro A _
    simp

private theorem esymm_zero' (s : Multiset ℂ) : s.esymm 0 = 1 := by simp [Multiset.esymm]

private theorem esymm_add' (s t : Multiset ℂ) (j : ℕ) :
    (s + t).esymm j = ∑ a ∈ Finset.range (j + 1), s.esymm a * t.esymm (j - a) :=
  _root_.UpperTheory.Reformulated.B.Qk43.esymm_add s t j

private theorem esymm_sum : ∀ (m : ℕ) (M : Fin m → Multiset ℂ) (j : ℕ),
    (∑ l, M l).esymm j = ∑ a ∈ Finset.piAntidiag Finset.univ j, ∏ l, (M l).esymm (a l)
  | 0, M, 0 => by simp [esymm_zero']
  | 0, M, j + 1 => by simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | m + 1, M, j => by
    rw [Fin.sum_univ_succ, esymm_add', sum_pi]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [esymm_sum m, Finset.mul_sum]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)} {n : ℕ}

private theorem ev_hEP (d : Dat S n) (z : Fin d.len → ℂ) (k : Pl E × Fin n) :
    ev z (d.hEP k) = d.ptH (fun l => z l + d.rho l) k := by
  have hq : qc k.1 ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.LFun.qV_ne_zero k.1)
  rw [Dat.hEP, map_sum, Dat.ptH, Dat.ptS, esymm_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e : ∀ (v : Fin d.len → ℝ) (c : ℂ), ev z (AddMonoidAlgebra.single v (MvPolynomial.C c)) =
      c * Complex.exp (∑ l, (v l : ℂ) * z l) := fun v c => by
    simp [ev, lift, AddMonoidAlgebra.liftNCRingHom, expChar]
  rw [e, Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  have h := Multiset.pow_smul_esymm (qc k.1 ^ (-(z l + d.rho l))) (a l) ((d.sat l k.1).map fun x : ℂˣ => (x : ℂ))
  simp only [smul_eq_mul, Multiset.map_map, Function.comp_def] at h
  simp only [mul_comm _ (qc k.1 ^ (-(z l + d.rho l)))]
  rw [← h, mul_assoc, mul_comm]
  congr 1
  rw [← Complex.cpow_natCast, Complex.cpow_def_of_ne_zero hq, Complex.cpow_natCast, Complex.cpow_def_of_ne_zero hq,
    ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  simp only [Pi.neg_apply]
  push_cast
  unfold qc
  ring

private theorem supp_good {F : KF ((E →+* ℂ) × Fin n) (Pl E × Fin n)}
    {G : ℕ → MvPolynomial (Pl E × Fin n) (MvPolynomial ((E →+* ℂ) × Fin n) ℂ)} (hF : ∀ x ∈ F.vars, x.1 ∉ S) (hG : Gen F G)
    (k : ℕ) {β : (Pl E × Fin n) →₀ ℕ} (hβ : β ∈ (G k).support) : ∀ x ∈ β.support, x.1 ∉ S := by
  classical
  intro x hx
  refine hF x ((MvPolynomial.mem_vars_iff_mem_support x).2 ⟨β, ?_, hx⟩)
  by_contra hn
  have h := congrArg (MvPolynomial.coeff β) (hG k)
  rw [MvPolynomial.coeff_map, pieceK, MvPolynomial.coeff_sum, Finset.sum_eq_zero fun γ hγ => by
    rw [MvPolynomial.coeff_monomial, if_neg fun e : γ = β => hn (e ▸ hγ)]] at h
  exact MvPolynomial.mem_support_iff.1 hβ (UpperTheory.ConvolutionTheory.FX.blockE_inj (E →+* ℂ) n (h.trans (map_zero _).symm))

private theorem list_rel {M A ι : Type} [AddCommGroup M] [Module ℂ M] {V : Submodule ℂ M} [CommRing A] [Module A V]
    (f : ι → A) (g : ι → Module.End ℂ M) (e : ι → ℕ) (l : List ι) (h : ∀ i ∈ l, ∀ v : V, ((f i • v : V) : M) = g i v) :
    ∀ v : V, (((l.map fun i => f i ^ e i).prod • v : V) : M) = (l.map fun i => g i ^ e i).prod v := by
  induction l with
  | nil => simp
  | cons i l ih =>
    intro v
    have hp : ∀ (m : ℕ) (v : V), ((f i ^ m • v : V) : M) = (g i ^ m) v := fun m => by
      induction m with
      | zero => simp
      | succ m ih => intro v; rw [pow_succ', pow_succ', mul_smul, h i (by simp), ih, Module.End.mul_apply]
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, mul_smul, hp, Module.End.mul_apply,
      ih fun j hj => h j (List.mem_cons_of_mem _ hj)]

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW GlobalTheory.CuspRep PositivityTheory.Rg.Fx in
theorem UpperTheory.ConvolutionTheory.BW.killOne :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.KillOne E := by
  intro E _ _ _ S n C d φ F G hC hb hs hF hK hG t
  obtain ⟨A, _, _, _, _, Z, H, I, T, hZ, hH, hsys⟩ := exists_sys d hC
  have h := absKill (E →+* ℂ) (Pl E × Fin n) A (bsp S n hC) n d.len Z H I T (cmp d hC) d.idx d.lamR d.hEP _ C hsys F G hF
    (fun z => by
      have := hK fun l => z l + d.rho l
      rw [← this]
      congr 2
      · funext p
        simp only [Dat.lamR, Dat.ptL]
        ring
      · funext k
        exact ev_hEP d z k) hG ⟨φ, hb, hs⟩ t
  have e : ∀ k (v : bsp S n hC), ((MvPolynomial.eval₂ (MvPolynomial.aeval Z).toRingHom H (G k) • v : bsp S n hC) : Sm E n) =
      app (G k) v := fun k v => by
    rw [MvPolynomial.eval₂_eq, Finset.sum_smul, Submodule.coe_sum, app, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [mul_smul, Module.End.mul_apply, hmon, ← Finset.prod_map_toList,
      ← list_rel H (fun p => hk n p.1 (p.2 + 1)) β _ fun p hp => hH p (supp_good hF hG k hβ p (Finset.mem_toList.1 hp))]
    exact hZ _ _
  convert h using 2 with k
  exact congrArg (fun ψ : Sm E n => d.comp ψ.1 t) (e k ⟨φ, hb, hs⟩).symm
end
end

section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GroundTheory.Automorphic PositivityTheory.Rg.Fx UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

private theorem exists_esymm (n : ℕ) (c : Fin n → ℂ) :
    ∃ y : Fin n → ℂ, ∀ i : Fin n, MvPolynomial.aeval y (MvPolynomial.esymm (Fin n) ℂ ((i : ℕ) + 1)) = c i := by
  classical
  let a : Fin n → ℂ := fun k => (-1) ^ (n - (k : ℕ)) * c (Fin.rev k)
  let q : Polynomial ℂ := ∑ k : Fin n, Polynomial.C (a k) * Polynomial.X ^ (k : ℕ)
  have hq : q.degree < n := Polynomial.degree_sum_fin_lt a
  let p : Polynomial ℂ := Polynomial.X ^ n + q
  have hm : p.Monic := Polynomial.monic_X_pow_add hq
  have hd : p.natDegree = n := by
    have h0 : q.degree < (Polynomial.X ^ n : Polynomial ℂ).degree := by rwa [Polynomial.degree_X_pow]
    simp only [p]
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt h0, Polynomial.natDegree_X_pow]
  have hs : Multiset.card p.roots = p.natDegree := (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hl : p.roots.toList.length = n := by rw [Multiset.length_toList, hs, hd]
  refine ⟨fun j => p.roots.toList.get (j.cast hl.symm), fun i => ?_⟩
  have hy : (Finset.univ : Finset (Fin n)).val.map (fun j => p.roots.toList.get (j.cast hl.symm)) = p.roots := by
    rw [Fin.univ_val_map]
    conv_rhs => rw [← Multiset.coe_toList p.roots]
    congr 1
    refine List.ext_get (by simpa using hl.symm) fun k h1 h2 => ?_
    simp
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, hy]
  have hi : ((Fin.rev i : Fin n) : ℕ) + ((i : ℕ) + 1) = n := by
    have := i.2
    rw [Fin.val_rev]; omega
  have hcoef := Polynomial.coeff_eq_esymm_roots_of_card hs (k := ((Fin.rev i : Fin n) : ℕ)) (by omega)
  have e1 : p.natDegree - ((Fin.rev i : Fin n) : ℕ) = (i : ℕ) + 1 := by omega
  rw [e1, hm.leadingCoeff, one_mul] at hcoef
  have e2 : p.coeff ((Fin.rev i : Fin n) : ℕ) = (-1) ^ ((i : ℕ) + 1) * c i := by
    have h3 : (Polynomial.X ^ n : Polynomial ℂ).coeff ((Fin.rev i : Fin n) : ℕ) = 0 := by
      rw [Polynomial.coeff_X_pow, if_neg (by omega)]
    have h4 : q.coeff ((Fin.rev i : Fin n) : ℕ) = a (Fin.rev i) := by
      simp only [q, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      rw [Finset.sum_eq_single (Fin.rev i)]
      · simp
      · intro b _ hb
        rw [if_neg (fun h => hb (Fin.ext h.symm)), mul_zero]
      · simp
    simp only [p, Polynomial.coeff_add, h3, zero_add, h4, a, Fin.rev_rev]
    congr 2
    omega
  rw [e2] at hcoef
  have h5 : ((-1 : ℂ) ^ ((i : ℕ) + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact (mul_left_cancel₀ h5 hcoef).symm

private theorem aeval_blockE_injective (τ : Type) (n : ℕ) :
    Function.Injective (MvPolynomial.aeval blockE : MvPolynomial (τ × Fin n) ℂ →ₐ[ℂ] MvPolynomial (τ × Fin n) ℂ) := by
  refine (injective_iff_map_eq_zero _).2 fun P hP => MvPolynomial.funext fun c => ?_
  choose y hy using fun t : τ => exists_esymm n fun i => c (t, i)
  let x : τ × Fin n → ℂ := fun p => y p.1 p.2
  have h : (MvPolynomial.aeval x : MvPolynomial (τ × Fin n) ℂ →ₐ[ℂ] ℂ).comp (MvPolynomial.aeval blockE) = MvPolynomial.aeval c := by
    refine MvPolynomial.algHom_ext fun p => ?_
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, blockE, MvPolynomial.aeval_rename]
    exact hy p.1 p.2
  have h2 := DFunLike.congr_fun h P
  rw [AlgHom.comp_apply, hP, map_zero] at h2
  rw [map_zero, ← MvPolynomial.coe_aeval_eq_eval]
  exact h2.symm

private theorem vars_of_gen {τ κ : Type} [Fintype τ] {n : ℕ} {F : KF (τ × Fin n) κ}
    {G : MvPolynomial κ (MvPolynomial (τ × Fin n) ℂ)} {k : ℕ}
    (h : MvPolynomial.map (MvPolynomial.aeval blockE : MvPolynomial (τ × Fin n) ℂ →ₐ[ℂ] MvPolynomial (τ × Fin n) ℂ).toRingHom G =
      pieceK k F) {β : κ →₀ ℕ} (hβ : β ∈ G.support) : β ∈ F.support := by
  classical
  by_contra hF
  have h1 : (pieceK k F).coeff β = 0 := by
    rw [pieceK, MvPolynomial.coeff_sum]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [MvPolynomial.coeff_monomial, if_neg (fun e : b = β => hF (e ▸ hb))]
  rw [← h, MvPolynomial.coeff_map] at h1
  exact MvPolynomial.mem_support_iff.1 hβ ((injective_iff_map_eq_zero _).1 (aeval_blockE_injective τ n) _ h1)

section Ops

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

private def Q (S : Set (Pl E)) (C : ℝ) (ψ : Sm E n) : Prop := Band C ψ ∧ Sph S ψ

private def Op (S : Set (Pl E)) (C : ℝ) (k : GA E n) (T : Module.End ℂ (Sm E n)) : Prop :=
  ∀ ψ, Q S C ψ → Q S C (T ψ) ∧ rt E n k (T ψ) = T (rt E n k ψ)

variable {S : Set (Pl E)} {C : ℝ} {k : GA E n}

private theorem Q_zero (hb : BandOps E) (hC : 0 ≤ C) : Q S C (0 : Sm E n) :=
  ⟨(hb n C hC).1, fun w _ x _ => map_zero _⟩

private theorem Q_add (hb : BandOps E) (hC : 0 ≤ C) {ψ χ : Sm E n} (h : Q S C ψ) (h' : Q S C χ) : Q S C (ψ + χ) :=
  ⟨((hb n C hC).2 ψ h.1).1 χ h'.1, fun w hw x hx => by rw [map_add, h.2 w hw x hx, h'.2 w hw x hx]⟩

private theorem Op_zero (hb : BandOps E) (hC : 0 ≤ C) : Op S C k (0 : Module.End ℂ (Sm E n)) := fun ψ _ =>
  ⟨Q_zero hb hC, by simp⟩

private theorem Op_one : Op S C k (1 : Module.End ℂ (Sm E n)) := fun ψ h => ⟨h, rfl⟩

private theorem Op_add (hb : BandOps E) (hC : 0 ≤ C) {T T' : Module.End ℂ (Sm E n)} (h : Op S C k T) (h' : Op S C k T') :
    Op S C k (T + T') := fun ψ hψ =>
  ⟨Q_add hb hC (h ψ hψ).1 (h' ψ hψ).1, by
    rw [LinearMap.add_apply, LinearMap.add_apply, map_add, (h ψ hψ).2, (h' ψ hψ).2]⟩

private theorem Op_sum (hb : BandOps E) (hC : 0 ≤ C) {ι : Type*} (s : Finset ι) {T : ι → Module.End ℂ (Sm E n)}
    (h : ∀ i ∈ s, Op S C k (T i)) : Op S C k (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Op_zero hb hC
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Op_add hb hC (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem Q_rt (hh : HkOps E) (hb : BandOps E) (hC : 0 ≤ C) (k : KA E n) {ψ : Sm E n} (h : Q S C ψ) :
    Q S C (rt E n (k : GA E n) ψ) :=
  ⟨((hb n C hC).2 ψ h.1).2.2.2.1 _, fun w hw =>
    ((((hh n w 0).2.2.2 S ψ hw h.2).2.2.1 k).1) w hw⟩

private theorem Op_mul {k : KA E n} (hh : HkOps E) (hb : BandOps E) (hC : 0 ≤ C) {T T' : Module.End ℂ (Sm E n)}
    (h : Op S C (k : GA E n) T) (h' : Op S C (k : GA E n) T') : Op S C (k : GA E n) (T * T') := fun ψ hψ =>
  ⟨(h _ (h' ψ hψ).1).1, by
    rw [Module.End.mul_apply, Module.End.mul_apply, (h _ (h' ψ hψ).1).2, (h' ψ hψ).2]⟩

private theorem Op_pow {k : KA E n} (hh : HkOps E) (hb : BandOps E) (hC : 0 ≤ C) {T : Module.End ℂ (Sm E n)}
    (h : Op S C (k : GA E n) T) (m : ℕ) : Op S C (k : GA E n) (T ^ m) := by
  induction m with
  | zero => simpa using Op_one
  | succ m ih => rw [pow_succ]; exact Op_mul hh hb hC ih h

private theorem Op_prod {k : KA E n} (hh : HkOps E) (hb : BandOps E) (hC : 0 ≤ C) (L : List (Module.End ℂ (Sm E n)))
    (h : ∀ T ∈ L, Op S C (k : GA E n) T) : Op S C (k : GA E n) L.prod := by
  induction L with
  | nil => simpa using Op_one
  | cons a L ih =>
    rw [List.prod_cons]
    exact Op_mul hh hb hC (h a List.mem_cons_self) (ih fun T hT => h T (List.mem_cons_of_mem a hT))

private theorem Op_hk {k : KA E n} (hh : HkOps E) (hb : BandOps E) (hC : 0 ≤ C) {w : Pl E} (hw : w ∉ S) (j : ℕ) :
    Op S C (k : GA E n) (hk n w j) := fun ψ hψ =>
  ⟨⟨((hb n C hC).2 ψ hψ.1).2.2.2.2 w j, ((hh n w j).2.2.2 S ψ hw hψ.2).1⟩,
    (((hh n w j).2.2.2 S ψ hw hψ.2).2.2.1 k).2⟩

private theorem zop_mem (P : MvPolynomial ((E →+* ℂ) × Fin n) ℂ) : zop P ∈ Zalg E n := by
  rw [Zalg_eq_map]
  exact ⟨_, (evZ E n P).2, rfl⟩

private theorem Op_zop (hb : BandOps E) (hC : 0 ≤ C) (P : MvPolynomial ((E →+* ℂ) × Fin n) ℂ) :
    Op S C k (zop P) := fun ψ hψ => by
  have hc : ∀ (g : GA E n) (χ : Sm E n), rt E n g (zop P χ) = zop P (rt E n g χ) := fun g χ =>
    (LinearMap.congr_fun (GlobalTheory.CompanionTheory.CTFin.Slice1.commute_rt_of_mem_Zalg (zop_mem P) g).eq χ).symm
  refine ⟨⟨((hb n C hC).2 ψ hψ.1).2.2.1 _, fun w hw x hx => ?_⟩, hc k ψ⟩
  exact (hc _ ψ).trans (congrArg _ (hψ.2 w hw x hx))

private theorem Op_app {k : KA E n} (hh : HkOps E) (hb : BandOps E) (hC : 0 ≤ C)
    {G : MvPolynomial (Pl E × Fin n) (MvPolynomial ((E →+* ℂ) × Fin n) ℂ)}
    (hG : ∀ β ∈ G.support, ∀ p ∈ β.support, p.1 ∉ S) : Op S C (k : GA E n) (app G) := by
  refine Op_sum hb hC _ fun β hβ => Op_mul hh hb hC (Op_zop hb hC _) (Op_prod hh hb hC _ fun T hT => ?_)
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hT
  exact Op_pow hh hb hC (Op_hk hh hb hC (hG β hβ p (Finset.mem_toList.1 hp)) _) _

end Ops

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW in
theorem UpperTheory.ConvolutionTheory.BW.killComp :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.KillComp E := by
  intro E _ _ _ S n C φ w F G hC hφ hS hw hv hG hsum k d hd
  have hh := UpperTheory.ConvolutionTheory.BW.hkOps E
  have hb := UpperTheory.ConvolutionTheory.BW.bandOps E
  have hu := UpperTheory.ConvolutionTheory.BW.umgOps E
  have hc := UpperTheory.ConvolutionTheory.BW.compBound E
  have ho := UpperTheory.ConvolutionTheory.BW.killOne E
  funext t
  have hQ : Q S C φ := ⟨hφ, hS⟩
  have hQk : Q S C (rt E n (k : GA E n) φ) := Q_rt hh hb hC k hQ
  have hop : ∀ i, Op S C (k : GA E n) (app (G i)) := fun i => Op_app hh hb hC fun β hβ p hp =>
    hv p ((MvPolynomial.mem_vars p).2 ⟨β, vars_of_gen (hG i) hβ, hp⟩)
  let W : ℕ → Sm E n := fun e => ∑ i ∈ Finset.range e, app (G i) φ
  have hWQ : ∀ e, Q S C (W e) := fun e => by
    have h := (Op_sum hb hC (Finset.range e) fun i _ => hop i) φ hQ
    simpa only [LinearMap.sum_apply] using h.1
  have hUk : ∀ ψ : Sm E n, Umg ψ → Umg (rt E n (k : GA E n) ψ) := fun ψ h => ((hu n).2 ψ h).2.2.2.2.1 _
  have hWU : ∀ e, Umg (rt E n (k : GA E n) (W e)) := fun e => hUk _ (hWQ e).1.toUmg
  obtain ⟨N, hN⟩ := hsum
  obtain ⟨C₀, R, hB⟩ := (hc S n d).1 N
  have hlin := (hc S n d).2
  have hzero : d.comp (0 : Sm E n).1 t = 0 := by
    have h := hlin 0 0 1 ((hu n).1) ((hu n).1) t
    simp only [one_smul, add_zero, one_mul] at h
    exact left_eq_add.1 h
  have hpart : ∀ e, d.comp (rt E n (k : GA E n) (W e)).1 t =
      ∑ i ∈ Finset.range e, d.comp (app (G i) (rt E n (k : GA E n) φ)).1 t := by
    intro e
    induction e with
    | zero => simpa [W] using hzero
    | succ e ih =>
      have e1 : rt E n (k : GA E n) (W (e + 1)) =
          (1 : ℂ) • rt E n (k : GA E n) (W e) + app (G e) (rt E n (k : GA E n) φ) := by
        simp only [W, Finset.sum_range_succ, map_add, one_smul]
        rw [(hop e φ hQ).2]
      have hU2 : Umg (app (G e) (rt E n (k : GA E n) φ)) := (hop e _ hQk).1.1.toUmg
      rw [e1, hlin _ _ 1 (hWU e) hU2 t, ih, one_mul, Finset.sum_range_succ]
  have hlim : Filter.Tendsto (fun e => ∑ i ∈ Finset.range e, d.comp (app (G i) (rt E n (k : GA E n) φ)).1 t)
      Filter.atTop (nhds 0) := by
    rcases hd with h | h
    · exact (ho S n C d _ F G hC hQk.1 hQk.2 hv h hG t).tendsto_sum_nat
    · have h0 : ∀ i, d.comp (app (G i) (rt E n (k : GA E n) φ)).1 t = 0 := fun i =>
        congrFun (h _ (hop i _ hQk).1.1 (hop i _ hQk).1.2) t
      simp [h0]
  have hwk := hUk w hw
  let D : ℕ → Sm E n := fun e => (-1 : ℂ) • rt E n (k : GA E n) (W e) + rt E n (k : GA E n) w
  have hDU : ∀ e, Umg (D e) := fun e => ((hu n).2 _ (((hu n).2 _ (hWU e)).2.2.1 (-1))).2.1 _ hwk
  have hDc : ∀ e, d.comp (D e).1 t = d.comp (rt E n (k : GA E n) w).1 t -
      ∑ i ∈ Finset.range e, d.comp (app (G i) (rt E n (k : GA E n) φ)).1 t := fun e => by
    rw [hlin _ _ (-1) (hWU e) hwk t, hpart]
    ring
  have hDv : ∀ e g, (D e).1 g = (w - W e).1 (g * (k : GA E n)) := fun e g => by
    simp only [D]
    change (-1 : ℂ) • (W e).1 (g * (k : GA E n)) + w.1 (g * (k : GA E n)) = w.1 (g * (k : GA E n)) - (W e).1 (g * (k : GA E n))
    simp only [smul_eq_mul]
    ring
  set M : ℝ := (AutomorphicForm.heightConst E n * AutomorphicForm.height (k : GA E n)) ^ N with hM
  have hM0 : 0 ≤ M := pow_nonneg (mul_nonneg (zero_le_one.trans AutomorphicForm.one_le_heightConst)
    (AutomorphicForm.height_pos _).le) N
  have hconv : Filter.Tendsto (fun e => ∑ i ∈ Finset.range e, d.comp (app (G i) (rt E n (k : GA E n) φ)).1 t)
      Filter.atTop (nhds (d.comp (rt E n (k : GA E n) w).1 t)) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    set X : ℝ := Real.exp (R * ‖t‖) with hX
    have hX0 : 0 ≤ X := (Real.exp_pos _).le
    set A : ℝ := |C₀| * M * X + 1 with hA
    have hA0 : 0 < A := by positivity
    have hε : 0 < δ / (2 * A) := by positivity
    filter_upwards [hN _ hε] with e he
    have hb1 : ∀ g, ‖(D e).1 g‖ ≤ (δ / (2 * A) * M) * AutomorphicForm.height g ^ N := fun g => by
      rw [hDv]
      refine (he _).trans ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hε.le
      rw [hM, ← mul_pow]
      refine pow_le_pow_left₀ (AutomorphicForm.height_pos _).le ((AutomorphicForm.height_mul_le _ _).trans (le_of_eq ?_)) N
      ring
    have hb2 := hB _ _ (hDU e) hb1 t
    rw [hDc] at hb2
    rw [dist_comm, dist_eq_norm]
    refine lt_of_le_of_lt hb2 ?_
    have h3 : C₀ * (δ / (2 * A) * M) * X ≤ |C₀| * (δ / (2 * A) * M) * X := by
      have : 0 ≤ δ / (2 * A) * M := mul_nonneg hε.le hM0
      gcongr
      exact le_abs_self _
    refine lt_of_le_of_lt h3 ?_
    have h4 : |C₀| * (δ / (2 * A) * M) * X = δ / (2 * A) * (A - 1) := by
      rw [hA]; ring
    rw [h4]
    have h5 : δ / (2 * A) * (A - 1) ≤ δ / (2 * A) * A := by
      exact mul_le_mul_of_nonneg_left (by linarith) hε.le
    have h6 : δ / (2 * A) * A = δ / 2 := by field_simp
    linarith
  exact tendsto_nhds_unique hconv hlim
end
end
