import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvNear
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SiegelAdmissibleToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpecAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf

section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private def Nr (X : Tower Ω ε) (f : X.K) : Prop :=
  ∃ T : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ z ∈ T, s z = z) → X.gal s f = f

private theorem exp_inj (X : Tower Ω ε) : Function.Injective X.exp := X.exp.toRingHom.injective

private theorem nr_j (X : Tower Ω ε) : Nr X X.jK := by
  refine ⟨∅, fun s _ => exp_inj X ?_⟩
  ext r
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [X.gal_exp, hn, map_intCast]

private theorem nr_c (X : Tower Ω ε) (c : Ω) : Nr X (algebraMap Ω X.K c) := by
  refine ⟨{c}, fun s hs => exp_inj X ?_⟩
  ext r
  rw [X.gal_exp, AlgHom.commutes, HahnSeries.algebraMap_apply']
  by_cases h : r = 0 <;> simp [h, hs c (Finset.mem_singleton_self c)]

private theorem nr_two (X : Tower Ω ε) {f g : X.K} (hf : Nr X f) (hg : Nr X g) :
    ∃ T : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ z ∈ T, s z = z) → X.gal s f = f ∧ X.gal s g = g := by
  classical
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨A ∪ B, fun s hs => ⟨hA s fun z hz => hs z (Finset.mem_union_left _ hz),
    hB s fun z hz => hs z (Finset.mem_union_right _ hz)⟩⟩

private theorem nr_adj (X : Tower Ω ε) (f : X.K) (hf : f ∈ IntermediateField.adjoin Ω {X.jK}) : Nr X f := by
  induction hf using IntermediateField.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact nr_j X
  | algebraMap c => exact nr_c X c
  | add x y _ _ hx hy =>
    obtain ⟨T, hT⟩ := nr_two X hx hy
    exact ⟨T, fun s hs => by rw [map_add, (hT s hs).1, (hT s hs).2]⟩
  | inv x _ hx =>
    obtain ⟨T, hT⟩ := hx
    exact ⟨T, fun s hs => by rw [map_inv₀, hT s hs]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨T, hT⟩ := nr_two X hx hy
    exact ⟨T, fun s hs => by rw [map_mul, (hT s hs).1, (hT s hs).2]⟩

end

theorem UpperTheory.V.Z.Kato.Sym.PC.galNear :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (f : X.K), ∃ T : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ z ∈ T, s z = z) → X.gal s f = f := by
  intro Ω _ _ _ ε X f
  classical
  obtain ⟨p, hp0, hpf⟩ := X.alg_j f
  set q : Polynomial X.K := p.map (algebraMap _ X.K) with hq
  have hq0 : q ≠ 0 := Polynomial.map_ne_zero hp0
  have hqf : q.eval f = 0 := by
    rw [hq, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hpf
  have hc : ∀ i, Nr X (q.coeff i) := fun i => by
    rw [hq, Polynomial.coeff_map, IntermediateField.algebraMap_apply]
    exact nr_adj X _ (p.coeff i).2
  have hd : ∀ b, b ≠ f → ∃ r, (X.exp b).coeff r ≠ (X.exp f).coeff r := by
    intro b hb
    by_contra h
    push_neg at h
    exact hb (exp_inj X (HahnSeries.ext (funext h)))
  choose TC hTC using hc
  choose! rr hrr using hd
  refine ⟨(q.support.biUnion TC) ∪ ((q.roots.toFinset.erase f).image (fun b => (X.exp f).coeff (rr b))), ?_⟩
  intro s hs
  have hfix : ∀ i, X.gal s (q.coeff i) = q.coeff i := by
    intro i
    by_cases hi : i ∈ q.support
    · exact hTC i s fun z hz => hs z (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, hi, hz⟩))
    · rw [Polynomial.notMem_support_iff.mp hi, map_zero]
  have hmap : q.map (X.gal s).toRingHom = q := by
    ext i
    rw [Polynomial.coeff_map]
    exact hfix i
  have hroot : q.eval (X.gal s f) = 0 := by
    have h1 : (q.map (X.gal s).toRingHom).eval ((X.gal s).toRingHom f) = (X.gal s).toRingHom (q.eval f) := by
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rw [hmap, hqf, map_zero] at h1
    exact h1
  by_contra hne
  have hb : X.gal s f ∈ q.roots.toFinset.erase f :=
    Finset.mem_erase.mpr ⟨hne, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq0).mpr hroot)⟩
  have hsz := hs ((X.exp f).coeff (rr (X.gal s f)))
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hb, rfl⟩))
  apply hrr _ hne
  rw [X.gal_exp, hsz]
end

section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.PC.loc :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m c d M : ℕ), 0 < m → 1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → Lv c d M → ∀ t w, IsSec X m t → IsSymb X m c d M t w → ∃ T : Finset Ω, ∀ s s', (∀ z ∈ T, s z = s' z) → ∀ x y, Ok x y → Cgr m (w s x y) (w s' x y) := by
  intro Ω _ _ _ ε X m c d M hm hc hd hc6 hd6 hL t w ht hw
  unfold Lv at hL
  unfold IsSec at ht
  unfold IsSymb at hw
  obtain ⟨hM, hcM, hdM⟩ := hL
  obtain ⟨hgr, hok, -⟩ := rowB Ω M hM
  obtain ⟨-, hadm, -⟩ := admB Ω ε X
  classical
  haveI : NeZero M := ⟨by omega⟩
  have pt : ∀ a b : Row M, Ok a b → IsPt X m (sg X c M a) (sg X d M b) (t (sg X c M a) (sg X d M b)) := by
    intro a b hab
    exact (ht _ _ (sgB Ω ε X c M hc hc6 hM hcM a (hok a b hab).1).1 (sgB Ω ε X d M hd hd6 hM hdM b (hok a b hab).2.1).1).1
  have loc : ∀ a b : Row M, ∃ T : Finset Ω, ∀ r : Gal(Ω/ℚ), (∀ z ∈ T, r z = z) → Ok a b →
      (X.gal r) (sg X c M a) = sg X c M a ∧ (X.gal r) (sg X d M b) = sg X d M b ∧
      Mv X m (X.gal r) r (t (sg X c M a) (sg X d M b)) (t (sg X c M a) (sg X d M b)) 1 := by
    intro a b
    by_cases hab : Ok a b
    · obtain ⟨T1, h1⟩ := PC.galNear Ω ε X (sg X c M a)
      obtain ⟨T2, h2⟩ := PC.galNear Ω ε X (sg X d M b)
      obtain ⟨S, hS⟩ := mvNear Ω ε X m hm _ _ _ (pt a b hab)
      let Tf : X.K → Finset Ω := fun f => Classical.choose (PC.galNear Ω ε X f)
      refine ⟨T1 ∪ T2 ∪ S.biUnion Tf, fun r hr _ => ⟨h1 r (fun z hz => hr z (by simp [hz])), h2 r (fun z hz => hr z (by simp [hz])), ?_⟩⟩
      refine hS _ r (hadm r) (fun f hf => ?_)
      exact Classical.choose_spec (PC.galNear Ω ε X f) r (fun z hz => hr z (by simp only [Finset.mem_union, Finset.mem_biUnion]; exact Or.inr ⟨f, hf, hz⟩))
    · exact ⟨∅, fun r _ h => absurd h hab⟩
  let G : Row M × Row M → Finset Ω := fun p => Classical.choose (loc p.1 p.2)
  refine ⟨Finset.univ.biUnion G, ?_⟩
  intro s s' hss x y hxy
  set r := s'⁻¹ * s
  set a := gr M s⁻¹ x
  set b := gr M s⁻¹ y
  have hab : Ok a b := (hok x y hxy).2.2.1 s⁻¹
  have hr : ∀ z ∈ G (a, b), r z = z := by
    intro z hz
    have := hss z (Finset.mem_biUnion.2 ⟨(a, b), Finset.mem_univ _, hz⟩)
    show s'⁻¹ (s z) = z
    rw [this]
    exact s'.symm_apply_apply z
  obtain ⟨fa, fb, fm⟩ := Classical.choose_spec (loc a b) r hr hab
  have hsr : s' * r = s := by simp [r]
  have hrs : r * s⁻¹ = s'⁻¹ := by simp [r]
  have inv1 : ∀ (q : Gal(Ω/ℚ)) (e : Row M), gr M q (gr M q⁻¹ e) = e := by
    intro q e
    rw [← (hgr _ _ _).1, mul_inv_cancel, (hgr 1 1 e).2]
  have sa := sgB Ω ε X c M hc hc6 hM hcM a (hok a b hab).1
  have sb := sgB Ω ε X d M hd hd6 hM hdM b (hok a b hab).2.1
  have ex : sg X c M (gr M s'⁻¹ x) = sg X c M a := by
    rw [← hrs, (hgr _ _ _).1, ← sa.2.2.1 r, fa]
  have ey : sg X d M (gr M s'⁻¹ y) = sg X d M b := by
    rw [← hrs, (hgr _ _ _).1, ← sb.2.2.1 r, fb]
  have ws' := (hw s' x y hxy).2
  rw [ex, ey] at ws'
  have ws := (hw s x y hxy).2
  have gx : (X.gal s) (sg X c M a) = sg X c M x := by rw [sa.2.2.1 s, inv1]
  have gy : (X.gal s) (sg X d M b) = sg X d M y := by rw [sb.2.2.1 s, inv1]
  have q1 : IsPt X m ((X.gal r) (sg X c M a)) ((X.gal r) (sg X d M b)) (t (sg X c M a) (sg X d M b)) := by
    rw [fa, fb]
    exact pt a b hab
  have q2 : IsPt X m ((X.gal s') ((X.gal r) (sg X c M a))) ((X.gal s') ((X.gal r) (sg X d M b))) (t (sg X c M x) (sg X d M y)) := by
    rw [← gal_mul_apply, ← gal_mul_apply, hsr, gx, gy]
    exact pt x y hxy
  have comp := mvComp Ω ε X m hm (X.gal r) (X.gal s') r s' (hadm r) (hadm s') _ _ _ _ _ (pt a b hab) q1 q2 _ _ fm ws'
  rw [map_one, one_pow, one_mul] at comp
  have eg : (X.gal r).trans (X.gal s') = X.gal s := by
    ext f
    rw [← hsr, gal_mul_apply]
    rfl
  rw [eg, hsr] at comp
  have q3 : IsPt X m ((X.gal s) (sg X c M a)) ((X.gal s) (sg X d M b)) (t (sg X c M x) (sg X d M y)) := by
    rw [gx, gy]
    exact pt x y hxy
  exact ((mvEx Ω ε X m hm (X.gal s) s (hadm s) _ _ _ (pt a b hab)).2.2.2 _ q3 _ _ comp).1 ws
end
