import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwBernHk
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwBernFaith
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkEv
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemFixedPiIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.MultiTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.SymOfVieta
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem dc_apply {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K K' : Subgroup H) (x : H) (h : FinOrb K K' x) (m : M) :
    dc ρ K K' x m = ∑ᶠ q : MulAction.orbit K (x : H ⧸ K'), ρ (q : H ⧸ K').out m := by
  have : Finite (MulAction.orbit K (x : H ⧸ K')) := h
  have := Fintype.ofFinite (MulAction.orbit K (x : H ⧸ K'))
  rw [dc, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

private theorem relIndex_ne {H : Type} [Group H] (K I : Subgroup H) (h : FinOrb K I 1) : I.relIndex K ≠ 0 := by
  have e : I.subgroupOf K = MulAction.stabilizer K ((1 : H) : H ⧸ I) := by
    ext g
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    change _ ↔ (g : H) ∈ MulAction.stabilizer H ((1 : H) : H ⧸ I)
    rw [MulAction.stabilizer_quotient]
  rw [Subgroup.relIndex, e, MulAction.index_stabilizer]
  exact Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self _) h

private theorem bern_ev {O H E : Type} [CommRing O] [IsDomain O] [Ring H] [Algebra O H] [Ring E] [Algebra O E] {n : ℕ} {q : O}
    (b : Hk.Bern n q H) (hF : b.Faithful) (ev : H →ₐ[O] E) :
    (∀ z : MvPolynomial (Fin n) O, z.IsSymmetric → ev b.one * ev.comp b.th z = ev.comp b.th z * ev b.one) ∧
      (∀ (ι : Type) [Fintype ι] (a c : ι → MvPolynomial (Fin n) O), Hk.IsDual a c →
        ∑ i, ev.comp b.th (a i) * ev b.one * ev.comp b.th (c i) = ev.comp b.th (Hk.NN n q)) ∧
      ∀ y, ev b.one * ev.comp b.th y * ev b.one = ev.comp b.th (Hk.dd (Hk.NN n q * y)) * ev b.one := by
  refine ⟨fun z hz => ?_, fun ι _ a c hd => ?_, fun y => ?_⟩
  · simp only [AlgHom.comp_apply, ← map_mul]
    congr 1
    rw [Hk.Bern.one, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => (hkBern O n _ _ b).2 z hz w
  · simp only [AlgHom.comp_apply, ← map_mul, ← map_sum]
    rw [hkSum O n _ _ b hF ι a c hd]
  · simp only [AlgHom.comp_apply]
    rw [← map_mul, ← map_mul, hkSandwich O n _ _ b hF y, map_mul]

private theorem ev_rel {O H E : Type} [CommRing O] [Ring H] [Algebra O H] [Ring E] [Algebra O E] (ev : H →ₐ[O] E)
    {a y z : H} {c : O} {y' z' : E} (h : a * y = c • z) (hy : ev y = y') (hz : ev z = z') : ev a * y' = c • z' := by
  rw [← hy, ← hz, ← map_mul, h, map_smul]

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem bruh : ∀ g ∈ KO k (Fin n), ∃! w : Equiv.Perm (Fin n),
    ∃ a ∈ iwC k n ⊤, ∃ b ∈ iwC k n ⊤, g = a * pm k n w * b := by
  rw [(memIwC k n ⊤).2.1]
  exact (bruhatKO k n).2

private theorem iw_le : iwC k n ⊤ ≤ KO k (Fin n) := by
  rw [(memIwC k n ⊤).2.1]
  exact iwahori_le_KO k (Fin n)

private theorem dom_fund {x : kˣ} (hx : IsUnif x) (m : ℕ) : Dom (fun j : Fin n => x ^ fund n m j) := by
  have hx1 : valuation k (x : k) ≤ 1 := by
    obtain ⟨p, -, hp⟩ := hx
    rw [← hp]
    exact p.2
  intro j l hjl
  have hjl' : (j : ℕ) ≤ (l : ℕ) := hjl
  simp only [fund]
  by_cases h1 : (l : ℕ) < m
  · have h2 : (j : ℕ) < m := lt_of_le_of_lt hjl' h1
    simp [h1, h2]
  · by_cases h2 : (j : ℕ) < m
    · simpa [h1, h2] using hx1
    · simp [h1, h2]

private theorem fund_split {T : Type} [CommGroup T] (x : T) (i : Fin n) : (fun j : Fin n => x ^ fund n ((i : ℕ) + 1) j)
    = Pi.mulSingle i x * (fun j : Fin n => x ^ fund n (i : ℕ) j) := by
  funext j
  simp only [fund, Pi.mul_apply]
  by_cases hj : j = i
  · subst hj
    simp
  · have hne : (j : ℕ) ≠ (i : ℕ) := fun h => hj (Fin.ext h)
    rw [Pi.mulSingle_eq_of_ne hj, one_mul]
    by_cases h : (j : ℕ) < (i : ℕ)
    · have h' : (j : ℕ) < (i : ℕ) + 1 := by omega
      simp [h, h']
    · have h' : ¬ (j : ℕ) < (i : ℕ) + 1 := by omega
      simp [h, h']

private theorem dc_K {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) :
    (∀ m ∈ fixd ρ (iwC k n ⊤), dc ρ (KO k (Fin n)) (iwC k n ⊤) 1 m ∈ fixd ρ (KO k (Fin n))) ∧
    ∀ m ∈ fixd ρ (KO k (Fin n)),
      dc ρ (KO k (Fin n)) (iwC k n ⊤) 1 m = ((iwC k n ⊤).relIndex (KO k (Fin n))) • m := by
  obtain ⟨hf, -, h3⟩ := hkTrace A _ M ρ _ _ iw_le _ (pm k n) (heckePairIwC k n ⊤).1 (bruhatKO k n).1 bruh
  have ha := (hkApply A _ M ρ _ _ 1 hf).1
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · rw [← ha ⟨m, hm⟩]
    exact Subtype.property _
  · have h := congrArg Subtype.val (h3 ⟨m, hm⟩)
    rw [trc, ha, Submodule.coe_smul, Nat.cast_smul_eq_nsmul] at h
    exact h

private theorem locO (O M : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    (ρ : Representation O (GL (Fin n) k) M) {x : kˣ} (hx : IsUnif x) (hq : IsUnit (resCard k : O)) :
    ∃ (th : MvPolynomial (Fin n) O →ₐ[O] Module.End O (fixd ρ (iwC k n ⊤))) (E : Module.End O (fixd ρ (iwC k n ⊤))),
      (∀ v, (E v : M) = dc ρ (KO k (Fin n)) (iwC k n ⊤) 1 v) ∧
      (∀ i : Fin n, th (MvPolynomial.X i) * hk ρ (iwC k n ⊤) (pw x (fund n i)) =
        ((resCard k : O) ^ (i : ℕ)) • hk ρ (iwC k n ⊤) (pw x (fund n ((i : ℕ) + 1)))) ∧
      (∀ z : MvPolynomial (Fin n) O, z.IsSymmetric → E * th z = th z * E) ∧
      (∀ (ι : Type) [Fintype ι] (a b : ι → MvPolynomial (Fin n) O), Hk.IsDual a b →
        ∑ i, th (a i) * E * th (b i) = th (Hk.NN n (resCard k : O))) ∧
      ∀ y, E * th y * E = th (Hk.dd (Hk.NN n (resCard k : O) * y)) * E := by
  obtain ⟨b, hT, hX⟩ := bernHk k n O x hx hq
  have hF := bernFaith k n O x hx hq b hT hX
  obtain ⟨ev, hev⟩ := hkEv O _ M ρ _ (heckePairIwC k n ⊤).1
  obtain ⟨hf, h2, -⟩ := hkTrace O _ M ρ _ _ iw_le _ (pm k n) (heckePairIwC k n ⊤).1 (bruhatKO k n).1 bruh
  obtain ⟨g1, g2, g3⟩ := bern_ev b hF ev
  refine ⟨ev.comp b.th, ev b.one, fun v => ?_, fun i => ?_, g1, g2, g3⟩
  · have h : ev b.one = ∑ w, hk ρ (iwC k n ⊤) (pm k n w) :=
      (map_sum ev b.T Finset.univ).trans (Finset.sum_congr rfl fun w _ => (congrArg ev (hT w)).trans (hev _))
    rw [h, h2]
    exact (hkApply O _ M ρ _ _ 1 hf).1 v
  · exact ev_rel ev (hX i) (hev _) (hev _)

private theorem locA (O A M V : Type) [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup M] [Module A M]
    [AddCommGroup V] [Module A V] (ρ : Representation A (GL (Fin n) k) M) {x : kˣ} (hx : IsUnif x)
    (hq : IsUnit (resCard k : O)) (tf : ∀ (c : ℕ) (m : M), c ≠ 0 → c • m = 0 → m = 0)
    (ι : V →ₗ[A] M) (hι : Function.Injective ι) (hI : ∀ v, ι v ∈ fixd ρ (iwC k n ⊤))
    (Θ : (Fin n → kˣ) →* (Module.End A V)ˣ)
    (hΘ : ∀ t, Dom t → ∀ v, ι ((Θ t).val v) = dc ρ (iwC k n ⊤) (iwC k n ⊤) (diagT k (Fin n) t) (ι v))
    (e : Module.End A V) (he : ∀ v, ι (e v) = dc ρ (KO k (Fin n)) (iwC k n ⊤) 1 (ι v))
    (φ : MvPolynomial (Fin n) O →+* Module.End A V)
    (hC : ∀ o v, φ (MvPolynomial.C o) v = algebraMap O A o • v)
    (hφ : ∀ i, φ (MvPolynomial.X i) = ((resCard k : A) ^ (i : ℕ)) • (Θ (Pi.mulSingle i x)).val) :
    (∀ z : MvPolynomial (Fin n) O, z.IsSymmetric → Commute e (φ z)) ∧
      (∀ (J : Type) [Fintype J] (a b : J → MvPolynomial (Fin n) O), Hk.IsDual a b →
        ∑ i, φ (a i) * e * φ (b i) = φ (Hk.NN n (resCard k : O))) ∧
      ∀ y v, ι v ∈ fixd ρ (KO k (Fin n)) → e (φ y v) = φ (Hk.dd (Hk.NN n (resCard k : O) * y)) v := by
  letI : Module O M := Module.compHom M (algebraMap O A)
  have hs : ∀ (o : O) (m : M), o • m = algebraMap O A o • m := fun _ _ => rfl
  let ρO : Representation O (GL (Fin n) k) M :=
    { toFun := fun g => { toFun := ρ g, map_add' := map_add _, map_smul' := fun o m => map_smul (ρ g) (algebraMap O A o) m }
      map_one' := LinearMap.ext fun m => LinearMap.congr_fun (map_one ρ) m
      map_mul' := fun g h => LinearMap.ext fun m => LinearMap.congr_fun (map_mul ρ g h) m }
  have hdc : ∀ K K' g, FinOrb K K' g → ∀ m, dc ρO K K' g m = dc ρ K K' g m := fun K K' g h m => by
    rw [dc_apply _ _ _ _ h, dc_apply _ _ _ _ h]; rfl
  obtain ⟨th, E, hE, hX, hsym, hsum, hsw⟩ := locO O M ρO hx hq
  have hP := heckePairIwC k n ⊤
  let j : V →+ fixd ρO (iwC k n ⊤) := ⟨⟨fun v => ⟨ι v, hI v⟩, Subtype.ext (map_zero ι)⟩, fun a b => Subtype.ext (map_add ι a b)⟩
  have hj : ∀ v, (j v : M) = ι v := fun _ => rfl
  have jinj : Function.Injective j := fun a b h => hι (congrArg Subtype.val h)
  have je : ∀ v, j (e v) = E (j v) := fun v => Subtype.ext (by rw [hE, hj, hj, he, hdc _ _ _ (hP.2.2 ⊤).2])
  have jΘ : ∀ m v, j ((Θ fun a => x ^ fund n m a).val v) = hk ρO (iwC k n ⊤) (pw x (fund n m)) (j v) := fun m v =>
    Subtype.ext (by
      rw [hj, hΘ _ (dom_fund hx m), ← hdc _ _ _ (hP.1 _)]
      exact ((hkApply O _ M ρO _ _ _ (hP.1 _)).1 (j v)).symm)
  have jX : ∀ i v, j (φ (MvPolynomial.X i) v) = th (MvPolynomial.X i) (j v) := by
    intro i v
    obtain ⟨u, rfl⟩ := ((Module.End.isUnit_iff _).1 (Θ fun a => x ^ fund n i a).isUnit).2 v
    have h := LinearMap.congr_fun (hX i) (j u)
    rw [Module.End.mul_apply, ← jΘ, LinearMap.smul_apply, ← jΘ, fund_split, map_mul, Units.val_mul,
      Module.End.mul_apply] at h
    rw [h, hφ]
    apply Subtype.ext
    rw [hj, LinearMap.smul_apply, map_smul, Submodule.coe_smul, hs, map_pow, map_natCast, hj]
  have jφ : ∀ z v, j (φ z v) = th z (j v) := by
    intro z
    induction z using MvPolynomial.induction_on with
    | C o =>
      intro v
      apply Subtype.ext
      rw [hC, hj, map_smul, ← MvPolynomial.algebraMap_eq, th.commutes, Module.algebraMap_end_apply, Submodule.coe_smul, hs, hj]
    | add p q hp hq => intro v; simp only [map_add, LinearMap.add_apply, hp, hq]
    | mul_X p i hp => intro v; simp only [map_mul, Module.End.mul_apply, hp, jX]
  refine ⟨fun z hz => LinearMap.ext fun v => jinj ?_, fun J _ a b hd => LinearMap.ext fun v => jinj ?_, fun y v hv => ?_⟩
  · simp only [Module.End.mul_apply, je, jφ]
    exact LinearMap.congr_fun (hsym z hz) _
  · rw [jφ, ← hsum J a b hd]
    simp only [LinearMap.sum_apply, map_sum, Module.End.mul_apply, je, jφ]
  · have h1 : e v = ((iwC k n ⊤).relIndex (KO k (Fin n))) • v := hι (by rw [he, map_nsmul, (dc_K ρ).2 _ hv])
    have h2 : e (φ y (e v)) = φ (Hk.dd (Hk.NN n (resCard k : O) * y)) (e v) := jinj (by
      simp only [je, jφ]
      exact LinearMap.congr_fun (hsw y) _)
    rw [h1, map_nsmul, map_nsmul, map_nsmul, ← sub_eq_zero, ← nsmul_sub] at h2
    apply hι
    rw [← sub_eq_zero, ← map_sub]
    refine tf _ _ (relIndex_ne _ _ (hP.2.2 ⊤).2) ?_
    rw [← map_nsmul, h2, map_zero]

end Loc

private theorem comm_dc {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K K' : Subgroup H) (x : H) (φ : Module.End A M) (h : ∀ g, Commute φ (ρ g)) :
    Commute φ (dc ρ K K' x) :=
  finsum_induction (fun e => Commute φ e) (Commute.zero_right φ) (fun _ _ h1 h2 => h1.add_right h2) fun _ => h _

private theorem lprod_mem {A V : Type} [CommRing A] [AddCommGroup V] [Module A V] (W : Submodule A V) (f : Module.End A V)
    (hf : ∀ v, f v ∈ W) (s : List (Module.End A V)) (hs : ∀ a ∈ s, ∀ v ∈ W, a v ∈ W) (h : f ∈ s) (v : V) : s.prod v ∈ W := by
  induction s with
  | nil => simp at h
  | cons a s ih =>
    rw [List.prod_cons, Module.End.mul_apply]
    rcases List.mem_cons.1 h with rfl | h'
    · exact hf _
    · exact hs a List.mem_cons_self _ (ih (fun b hb => hs b (List.mem_cons_of_mem _ hb)) h')

private theorem comm_unit {R : Type} [Monoid R] {e : R} {u v w : Rˣ} (h : w = u * v) (hw : Commute e w) (hv : Commute e v) :
    Commute e u := by
  have : u = w * v⁻¹ := by rw [h, mul_inv_cancel_right]
  rw [this, Units.val_mul]
  exact hw.mul_right hv.units_inv_right

private theorem stab {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M)
    (K : Subgroup G) (tf : ∀ (k : ℕ) (m : M), k ≠ 0 → k • m = 0 → m = 0) (U : Submodule A M) (e f : Module.End A U) (r : ℕ)
    (hr : r ≠ 0) (eK : ∀ v, (e v : M) ∈ fixd ρ K) (hf : Commute e f) (v : U) (h1 : (e v : M) = r • (v : M)) :
    (f v : M) ∈ fixd ρ K := by
  intro g hg
  have h1' : e v = r • v := Subtype.ext h1
  have h2 := eK (f v) g hg
  have h3 : e (f v) = r • f v := by
    rw [← map_nsmul, ← h1']
    exact LinearMap.congr_fun hf.eq v
  rw [h3, Submodule.coe_smul_of_tower, map_nsmul, ← sub_eq_zero, ← nsmul_sub] at h2
  exact sub_eq_zero.1 (tf r _ hr h2)

private theorem comm_res {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {U : Submodule A M}
    {e f : Module.End A U} {e' f' : Module.End A M} (he : ∀ v, (e v : M) = e' v) (hf : ∀ v, (f v : M) = f' v)
    (h : Commute e' f') : Commute e f := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, he, hf, hf, he]
  exact LinearMap.congr_fun h.eq _

private theorem emb_C {O A V : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup V] [Module A V] {q n : ℕ}
    (act : PU A q n →ₐ[A] Module.End A V) (j : Fin q) (o : O) (v : V) :
    (act.toRingHom.comp (emb O A j)) (MvPolynomial.C o) v = algebraMap O A o • v := by
  have : emb O A (q := q) (n := n) j (MvPolynomial.C o) = algebraMap A _ (algebraMap O A o) := by simp [emb]
  exact (congrArg (fun p => act p v) this).trans (LinearMap.congr_fun (act.commutes _) v)

private theorem emb_X {O A V : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup V] [Module A V] {q n : ℕ}
    (act : PU A q n →ₐ[A] Module.End A V) (j : Fin q) (i : Fin n) :
    (act.toRingHom.comp (emb O A j)) (MvPolynomial.X i) = act (MvPolynomial.X (j, i)) := by
  have : emb O A (q := q) (n := n) j (MvPolynomial.X i) = MvPolynomial.X (j, i) := by simp [emb]
  exact congrArg act this

section

variable {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : Representation A (GV n w) M)

private theorem comm_at {j j' : Fin q} (h : j ≠ j') (g : GLw n (w j)) (g' : GLw n (w j')) :
    Commute (ρ (atJ n w j g)) (ρ (atJ n w j' g')) :=
  (Pi.mulSingle_commute (f := fun j => GLw n (w j)) h g g').map ρ

private theorem comm_dd {j j' : Fin q} (h : j ≠ j') (K K' : Subgroup (GLw n (w j))) (g : GLw n (w j))
    (I I' : Subgroup (GLw n (w j'))) (g' : GLw n (w j')) :
    Commute (dc (ρ.comp (atJ n w j)) K K' g) (dc (ρ.comp (atJ n w j')) I I' g') :=
  comm_dc _ _ _ _ _ fun a' => (comm_dc _ _ _ _ _ fun a => comm_at ρ (Ne.symm h) a' a).symm

private theorem mem_pi (H : ∀ j, Subgroup (GLw n (w j))) (m : M) :
    m ∈ fixd ρ (Subgroup.pi Set.univ H) ↔ ∀ j, m ∈ fixd (ρ.comp (atJ n w j)) (H j) :=
  by apply _root_.UpperTheory.Reformulated.B.Gr29.mem_pi <;> assumption

private theorem pres (j : Fin q) : ∀ m ∈ fixd ρ (UC n w fun _ => ⊤),
    dc (ρ.comp (atJ n w j)) (KO _ (Fin n)) (iwC _ n ⊤) 1 m ∈ fixd ρ (UC n w fun _ => ⊤) := by
  intro m hm
  rw [UC, mem_pi] at hm ⊢
  intro j'
  by_cases e : j' = j
  · subst e
    exact fixd_anti _ iw_le ((dc_K _).1 m (hm _))
  · intro u hu
    have h1 := LinearMap.congr_fun (comm_dc (ρ.comp (atJ n w j)) (KO _ (Fin n)) (iwC _ n ⊤) 1 _
      fun g' => comm_at ρ e u g').eq m
    rw [Module.End.mul_apply, Module.End.mul_apply, show ρ (atJ n w j' u) m = m from hm j' u hu] at h1
    exact h1

private theorem memI (j : Fin q) (v : fixd ρ (UC n w fun _ => ⊤)) : (v : M) ∈ fixd (ρ.comp (atJ n w j)) (iwC _ n ⊤) :=
  (mem_pi ρ _ _).1 v.2 j

variable {ρ} {e : Fin q → Module.End A (fixd ρ (UC n w fun _ => ⊤))}
  (he : ∀ j v, (e j v : M) = dc (ρ.comp (atJ n w j)) (KO _ (Fin n)) (iwC _ n ⊤) 1 v)

include he

private theorem e_K (j : Fin q) (v : fixd ρ (UC n w fun _ => ⊤)) : (e j v : M) ∈ fixd (ρ.comp (atJ n w j)) (KO _ (Fin n)) := by
  rw [he]; exact (dc_K _).1 _ (memI ρ j v)

private theorem e_e (j j' : Fin q) : Commute (e j) (e j') := by
  by_cases h : j = j'
  · subst h; exact Commute.refl _
  · exact comm_res (he j) (he j') (comm_dd ρ h _ _ _ _ _ _)

private theorem fixed_vectors_stable_under_hecke_action (tf : ∀ (k : ℕ) (m : M), k ≠ 0 → k • m = 0 → m = 0) (j : Fin q)
    (f : Module.End A (fixd ρ (UC n w fun _ => ⊤))) (hf : Commute (e j) f) :
    ∀ v ∈ (fixd (ρ.comp (atJ n w j)) (KO _ (Fin n))).comap (fixd ρ (UC n w fun _ => ⊤)).subtype,
      f v ∈ (fixd (ρ.comp (atJ n w j)) (KO _ (Fin n))).comap (fixd ρ (UC n w fun _ => ⊤)).subtype := fun v hv =>
  stab _ _ tf _ (e j) f _ (relIndex_ne _ _ ((heckePairIwC _ n ⊤).2.2 ⊤).2) (e_K he j) hf v
    ((he j v).trans ((dc_K _).2 _ hv))

private theorem e_X {l : ℕ} {x δ : ∀ j, ((w j).adicCompletion L)ˣ} (T : ThData l ρ x δ) (hx : ∀ j, IsUnif (x j))
    (j j' : Fin q) (i : Fin n) (h : j ≠ j') : Commute (e j) (T.actw (MvPolynomial.X (j', i))) := by
  have eΘ : ∀ t, Dom t → Commute (e j) (T.Θw j' t).val := fun t ht =>
    comm_res (he j) (T.hw.1 j' t ht) (comm_dd ρ h _ _ _ _ _ _)
  rw [T.actw_u]
  exact Commute.smul_right (comm_unit ((congrArg (T.Θw j') (fund_split (x j') i)).trans (map_mul _ _ _))
    (eΘ _ (dom_fund (hx j') _)) (eΘ _ (dom_fund (hx j') _))) _

private theorem e_prod (tf : ∀ (k : ℕ) (m : M), k ≠ 0 → k • m = 0 → m = 0) (v : fixd ρ (UC n w fun _ => ⊤)) :
    ((List.ofFn e).prod v : M) ∈ fixd ρ (UK n w) := by
  refine (mem_pi ρ _ _).2 fun j => ?_
  refine lprod_mem ((fixd (ρ.comp (atJ n w j)) (KO _ (Fin n))).comap (fixd ρ (UC n w fun _ => ⊤)).subtype) (e j) (e_K he j) _
    (fun a ha => ?_) (List.mem_ofFn.2 ⟨j, rfl⟩) v
  obtain ⟨j', rfl⟩ := List.mem_ofFn.1 ha
  exact fixed_vectors_stable_under_hecke_action he tf j _ (e_e he j j')

end

theorem UpperTheory.V.Pa.Lev.hkHypOf :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (l : ℕ) (O A M : Type) [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) (x δ : ∀ j, ((w j).adicCompletion L)ˣ) (T : ThData l ρ x δ), (∀ j, IsUnif (x j)) → (∀ j, IsUnit (qj w j : O)) → (∀ (k : ℕ) (m : M), k ≠ 0 → k • m = 0 → m = 0) → ∃ e : Fin q → Module.End A (fixd ρ (UC n w fun _ => ⊤)), HkHyp O (qj w) T.actw e (fun j => (fixd (ρ.comp (atJ n w j)) (KO _ (Fin n))).comap (fixd ρ (UC n w fun _ => ⊤)).subtype) ∧ ∀ v, ((List.ofFn e).prod v : M) ∈ fixd ρ (UK n w) := by
  intro L _ _ n q w l O A M _ _ _ _ _ _ ρ x δ T hx hq tf
  obtain ⟨e, he⟩ : ∃ e : Fin q → Module.End A (fixd ρ (UC n w fun _ => ⊤)), ∀ j v,
      (e j v : M) = dc (ρ.comp (atJ n w j)) (KO _ (Fin n)) (iwC _ n ⊤) 1 v :=
    ⟨fun j => LinearMap.restrict _ (pres ρ j), fun _ _ => rfl⟩
  have hloc := fun j => locA O A M (fixd ρ (UC n w fun _ => ⊤)) (ρ.comp (atJ n w j)) (hx j) (hq j) tf
    (fixd ρ (UC n w fun _ => ⊤)).subtype Subtype.val_injective (memI ρ j) (T.Θw j) (T.hw.1 j) (e j) (he j)
    (T.actw.toRingHom.comp (emb O A j)) (emb_C _ j) (fun i => (emb_X _ j i).trans (T.actw_u j i))
  exact ⟨e, ⟨e_e he, e_X he T hx, fun j => (hloc j).1, fun j => (hloc j).2.1,
    fun j j' i h => fixed_vectors_stable_under_hecke_action he tf j _ (e_X he T hx j j' i h),
    fun j j' _ => fixed_vectors_stable_under_hecke_action he tf j _ (e_e he j j'), fun j => (hloc j).2.2⟩, e_prod he tf⟩
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem prod_pairs_dvd {A : Type} [CommRing A] {n : ℕ} (u : Fin n → A) (c : A) :
    ∏ p ∈ Hk.pairs n, (u p.2 - c * u p.1) ∣ ∏ i, ∏ i' ∈ Finset.univ.erase i, (u i - u i') * (u i - c * u i') := by
  have h1 : ∏ p ∈ Hk.pairs n, (u p.2 - c * u p.1) =
      ∏ i, ∏ i' ∈ Finset.univ.filter (fun i' => i' < i), (u i - c * u i') := by
    unfold Hk.pairs
    rw [Finset.prod_filter, ← Finset.univ_product_univ, Finset.prod_product_right]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_filter]
  rw [h1]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun i _ => ?_
  refine (Finset.prod_dvd_prod_of_subset _ (Finset.univ.erase i) _ ?_).trans
    (Finset.prod_dvd_prod_of_dvd _ _ fun i' _ => dvd_mul_left _ _)
  intro i' hi'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi'
  simp [hi'.ne]

private theorem twoMaps_of_dvd {R B M V : Type} [CommRing R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V]
    [Module R V] {q n : ℕ} (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) {f g : PU R q n}
    (hfg : f ∣ g) (h : TwoMaps (M := M) β P act f) : TwoMaps (M := M) β P act g := by
  obtain ⟨c, rfl⟩ := hfg
  obtain ⟨φ, ψ, h1, h2, h3, h4⟩ := h
  refine ⟨φ, ψ.comp (act c).toAddMonoidHom, h1, fun t v => ?_, fun v => ?_, fun z => ?_⟩
  · show ψ (act c (act t v)) = _ • ψ (act c v)
    rw [← h2, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  · show φ (ψ (act c v)) = _
    rw [h3, map_mul, Module.End.mul_apply]
  · show ψ (act c (φ z)) = _
    rw [h2, h4, mul_comm f c, map_mul, map_mul, mul_smul]

theorem UpperTheory.V.Pa.Lev.twoMul :
    ∀ (O R B M V : Type) [CommRing O] [CommRing R] [Algebra O R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (Nq : Fin q → ℕ), TwoMaps (M := M) β P act (∏ j, emb O R j (Hk.NN n (Nq j : O))) → TwoMaps (M := M) β P act (fEl Nq fun j i => MvPolynomial.X (j, i)) := by
  intro O R B M V _ _ _ _ _ _ _ _ q n β P act Nq h
  refine twoMaps_of_dvd β P act ?_ h
  unfold fEl
  refine Finset.prod_dvd_prod_of_dvd _ _ fun j _ => ?_
  have e : emb O R j (Hk.NN n (Nq j : O)) = ∏ p ∈ Hk.pairs n,
      ((MvPolynomial.X (j, p.2) : PU R q n) - (Nq j : PU R q n) * MvPolynomial.X (j, p.1)) := by
    unfold Hk.NN
    rw [map_prod]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp [emb]
  rw [e]
  exact prod_pairs_dvd (fun i => (MvPolynomial.X (j, i) : PU R q n)) _
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem unit_card (l : ℕ) [hl : Fact l.Prime] (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    (hw : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (O : Type) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] :
    IsUnit (resCard (w.adicCompletion L) : O) := by
  rw [resCard_eq_normV]
  by_contra hn
  have h1 : residue O (normV w : O) = 0 := (residue_eq_zero_iff _).2 hn
  rw [map_natCast, CharP.cast_eq_zero_iff (ResidueField O) l] at h1
  have hmax := w.isMaximal
  letI : Field (𝓞 L ⧸ w.asIdeal) := Ideal.Quotient.field _
  have hfin : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 L ⧸ w.asIdeal)
  have h2 : l ∣ Fintype.card (𝓞 L ⧸ w.asIdeal) := by
    rw [← Nat.card_eq_fintype_card]; exact h1
  have h3 := (prime_dvd_char_iff_dvd_card (R := 𝓞 L ⧸ w.asIdeal) l).2 h2
  have h4 : ringChar (𝓞 L ⧸ w.asIdeal) = l :=
    ((Nat.prime_dvd_prime_iff_eq hl.out (CharP.char_is_prime (𝓞 L ⧸ w.asIdeal) _)).1 h3).symm
  apply hw
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← h4]
  exact ringChar.Nat.cast_ringChar

private theorem chi_monic {n : ℕ} {A G : Type} [CommRing A] [Nontrivial A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G) :
    (D.chi y).Monic ∧ (D.chi y).natDegree = n := by
  obtain ⟨h0, -, -, -, h1, h2, -⟩ := UpperTheory.V.CA.d_chi D.toDet y
  rw [Det.lam, pow_zero, one_mul, Nat.sub_zero] at h0
  rw [(UpperTheory.V.CA.d_toDet D y).1] at h0 h1 h2
  exact ⟨h1, le_antisymm h2 (Polynomial.le_natDegree_of_ne_zero (by rw [h0]; exact one_ne_zero))⟩

private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  have : (D.comap φ).chi (MonoidAlgebra.single g 1) = D.chi (MonoidAlgebra.single (φ g) 1) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom _ φ _) = D.D _ _
    congr 1
    rw [map_sub]
    simp
  rw [GDet.lam, GDet.lam, this]

private theorem lam_map {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] (D : GDet n A G) (f : A →+* A')
    (i : ℕ) (g : G) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 i
  rwa [MonoidAlgebra.mapRingHom_single, map_one] at this

private theorem fix_le {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A]
    [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) :
    fixd ρ (UK n w) ≤ fixd ρ (UC n w fun _ => ⊤) := by
  intro m hm u hu
  refine hm u fun j _ => ?_
  have h1 : iwC ((w j).adicCompletion L) n ⊤ ≤ KO _ (Fin n) := by
    rw [(memIwC _ n ⊤).2.1]
    exact iwahori_le_KO _ (Fin n)
  exact h1 (hu j trivial)

private theorem fix_at {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A]
    [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) (j : Fin q) :
    fixd ρ (UK n w) ≤ fixd (ρ.comp (atJ n w j)) (KO _ (Fin n)) := by
  intro m hm u hu
  refine hm (atJ n w j u) fun j' _ => ?_
  by_cases e : j' = j
  · subst e
    simpa [atJ] using hu
  · simp [atJ, Pi.mulSingle_eq_of_ne e]

private theorem two_gen (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (O A B M N : Type)
    [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [CommRing B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (ρ : Representation A (GV n w) M) (β : A →+* B) (P : Fin q → Polynomial B)
    (act : PU A q n →ₐ[A] Module.End A (fixd ρ (UC n w fun _ => ⊤)))
    (e : Fin q → Module.End A (fixd ρ (UC n w fun _ => ⊤)))
    (H : HkHyp O (qj w) act e
      (fun j => (fixd (ρ.comp (atJ n w j)) (KO _ (Fin n))).comap (fixd ρ (UC n w fun _ => ⊤)).subtype))
    (he : ∀ v, ((List.ofFn e).prod v : M) ∈ fixd ρ (UK n w))
    (eM : fixd ρ (UK n w) ≃+ N) (hM : ∀ (t : A) m, eM (t • m) = β t • eM m)
    (hP : ∀ j, (P j).Monic ∧ (P j).natDegree = n) (c : Fin q → ℕ → A)
    (hc : ∀ j k, β (c j k) = (-1) ^ k * (P j).coeff (n - k))
    (hs : ∀ j k, k ≤ n → ∀ m : fixd ρ (UC n w fun _ => ⊤), (m : M) ∈ fixd ρ (UK n w) →
      act (emb ℤ A j (MvPolynomial.esymm (Fin n) ℤ k)) m = c j k • m) :
    TwoMaps (M := N) β P act (fEl (qj w) fun j i => MvPolynomial.X (j, i)) := by
  let inc : N →+ fixd ρ (UC n w fun _ => ⊤) :=
    (Submodule.inclusion (fix_le ρ)).toAddMonoidHom.comp eM.symm.toAddMonoidHom
  have hinc : ∀ m, (inc m : M) = eM.symm m := fun _ => rfl
  let t0 : fixd ρ (UC n w fun _ => ⊤) →ₗ[A] fixd ρ (UK n w) :=
    ((fixd ρ (UC n w fun _ => ⊤)).subtype.comp (List.ofFn e).prod).codRestrict _ he
  let tr : fixd ρ (UC n w fun _ => ⊤) →+ N := eM.toAddMonoidHom.comp t0.toAddMonoidHom
  have hβ : ∀ (t : A) m, inc (β t • m) = t • inc m := fun t m => Subtype.ext (by
    obtain ⟨m, rfl⟩ := eM.surjective m
    rw [← hM, Submodule.coe_smul, hinc, hinc, eM.symm_apply_apply, eM.symm_apply_apply, Submodule.coe_smul])
  refine twoMul O A B N _ q n β P act (qj w) (multiTwo O A B N _ q n (qj w) β P act e _ inc tr H (fun j => (hP j).1)
    (fun j => (hP j).2) ?_ hβ (fun v => Subtype.ext ?_) (fun j m => fix_at ρ j (eM.symm m).2) fun j k hk m => ?_)
  · intro a b hab
    have h1 := congrArg Subtype.val hab
    rw [hinc, hinc] at h1
    exact eM.symm.injective (Subtype.ext h1)
  · rw [hinc]
    exact congrArg Subtype.val (eM.symm_apply_apply (t0 v))
  · rw [hs j k hk (inc m) (eM.symm m).2, ← hc, hβ]

theorem UpperTheory.V.Pa.Lev.twoOf :
    LocP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : TWBase (pairOf B.u) J Empty D) (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (w : Fin q → Plc L) (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ), (∀ j, ((l : ℕ) : 𝓞 L) ∉ (w j).asIdeal) → (∀ j, IsUnif (x j)) → (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∀ (T : ThData l A.ρ x δ) (ph ta : Fin q → (globOf r V).G₀), LocOk A x δ ph ta → TwoMaps (M := b.M) A.β.toRingHom (fun j => (pairOf B.u).D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1)) T.actw (fEl (qj w) fun j i => MvPolynomial.X (j, i)) := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b V h q w A x δ hl hx hδ T ph ta hok
  have hs := symOf hP l L Ω s V0 O n r B J D b V h q w A x δ hl hx hδ T ph ta hok
  have hch : CharP (ResidueField O) l := UpperTheory.V.Pa.IsCoef.char
  obtain ⟨ι, hι, -⟩ := hok
  obtain ⟨e, H, he⟩ := hkHypOf L n q w l O A.R A.P A.ρ x δ T hx (fun j => unit_card l L (w j) (hl j) O)
    (fun k m hk hm => hι m fun y => by
      have h1 := congrArg y.sp hm
      rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul ℂ] at h1
      exact (smul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hk))
  refine two_gen L n q w O A.R B.B A.P b.M A.ρ A.β.toRingHom _ T.actw e H he A.eM A.eM_smul
    (fun j => chi_monic _ _) (fun j k => A.p.D.lam k (MonoidAlgebra.single (ph j) 1)) (fun j k => ?_) hs
  exact (lam_map A.p.D A.β.toRingHom k (ph j)).symm.trans
    ((congrArg (fun D' => GDet.lam D' k (MonoidAlgebra.single (ph j) 1)) A.β_pair.1).trans (lam_comap _ _ k _))
end
