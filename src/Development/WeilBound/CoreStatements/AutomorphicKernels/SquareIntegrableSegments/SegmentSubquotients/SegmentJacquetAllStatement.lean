import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportSubschemeEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetLengthOneStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.FineJacquetSegmentLengthTwoStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.FineJacquetSegmentInductionStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusReciprocityNonzeroStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.ExistsSegmentRepresentationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatenatedJacquetMultiplicityFactorizationStatement

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
open GlobalTheory.Parabolic (Embeds)

namespace GlobalTheory.CompanionTheory.LkSegUniq

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_ne_zero_of_injective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hρ : ρ.IsIrreducible)
    (φ : ρ.IntertwiningMap σ) (hφ : Function.Injective φ) : ∃ v, φ v ≠ 0 := by
  haveI := Model.nontrivial_of_isIrreducible hρ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact ⟨v, fun e => hv (hφ (e.trans (map_zero φ).symm))⟩

theorem exists_ne_zero_of_surjective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hσ : σ.IsIrreducible)
    (φ : ρ.IntertwiningMap σ) (hφ : Function.Surjective φ) : ∃ v, φ v ≠ 0 := by
  haveI := Model.nontrivial_of_isIrreducible hσ
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hφ u
  exact ⟨v, hu⟩

theorem bot_ne_top_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hσ : σ.IsIrreducible)
    (h : IsSubquotient σ ρ) : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
  obtain ⟨S, f, hf⟩ := h
  intro hb
  haveI := Model.nontrivial_of_isIrreducible hσ
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf u
  have hv : (v : V) ∈ (⊥ : Subrepresentation ρ) := hb ▸ trivial
  have hv0 : v = 0 := Subtype.ext hv
  exact hu (by rw [hv0, map_zero])

theorem fineJac_all (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation)
    (Δ : Segment k) : FineJac Δ := by
  induction h : Δ.len using Nat.strong_induction_on generalizing Δ with
  | _ n ih =>
    have h0 := Δ.len_pos
    obtain h1 | h2 | h3 : n = 1 ∨ n = 2 ∨ 3 ≤ n := by omega
    · exact @GlobalTheory.T.fine_jacquet_length_one k _ _ _ _ hA Δ (h.trans h1)
    · exact @GlobalTheory.TL.fine_jacquet_segment_length_two k _ _ _ _ hA hZ Δ (h.trans h2)
    · exact @GlobalTheory.TL.fine_jacquet_segment_induction k _ _ _ _ hA Δ (h ▸ h3) fun Δ' hlt => ih _ (h ▸ hlt) Δ' rfl

theorem exists_eq_of_embeds_one {c : ℕ} (hc : c = 1) (x : Fin c → IrrGL k) (y : IrrGL k)
    (hd : ∑ a, (x a).1 = y.1) (φ : y.rep.IntertwiningMap (prodIrr x hd)) (hφ : Function.Injective φ) :
    ∃ a, y = x a := by
  subst hc
  obtain ⟨z, rfl⟩ : ∃ z, x = fun _ => z := ⟨x 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  refine ⟨0, ?_⟩
  obtain ⟨n, c⟩ := y
  obtain ⟨m, c'⟩ := z
  have hnm : m = n := by simpa using hd
  subst hnm
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one (⟨m, c'⟩ : IrrGL k) hd
  have hS := (isSocle_self (⟨m, c'⟩ : IrrGL k).2.rep.irr).of_equiv (.refl _) ψ
  obtain ⟨a⟩ := hS.equiv_of_embeds (⟨m, c⟩ : IrrGL k).2.rep.irr ⟨φ, hφ⟩
  exact congrArg (Sigma.mk m) (irrCl_eq_iff.2 ⟨a⟩)

theorem sum_concat_fst {s N : ℕ} (y : Fin s → IrrGL k) (hy : ∑ a, (y a).1 = N) (c : Fin s → ℕ)
    (x : ∀ a, Fin (c a) → IrrGL k) (hx : ∀ a, ∑ i, (x a i).1 = (y a).1) :
    ∑ i, (concat c x i).1 = N := by
  have h1 : ∑ i, (concat c x i).1 = ∑ p : Σ a, Fin (c a), (x p.1 p.2).1 :=
    Equiv.sum_comp finSigmaFinEquiv.symm (fun p : Σ a, Fin (c a) => (x p.1 p.2).1)
  rw [h1, Fintype.sum_sigma, ← hy]
  exact Finset.sum_congr rfl fun a _ => hx a

theorem eq_dec_of_one_le_jm (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {Δ : Segment k} (fine : FineJac Δ) {N : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hL : IsLSeg Δ π)
    (hs : IsSmooth π) (hi : π.IsIrreducible) (y : Fin Δ.len → IrrGL k) (hy : ∑ a, (y a).1 = N)
    (hpos : ∀ a, 0 < (y a).1) (h1 : 1 ≤ jm y hy π) : y = dec Δ := by
  have hemb := fun a => GlobalTheory.T.support_subscheme_embedding k (y a).1 _ (y a).rep (y a).2.rep.smooth (y a).2.rep.irr
  choose c x hx hcusp φ hφ using hemb
  have hne : ∀ a, ∃ v, φ a v ≠ 0 := fun a =>
    exists_ne_zero_of_injective (y a).2.rep.irr (φ a) (hφ a)
  have hjm : ∀ a, 1 ≤ jm (x a) (hx a) (y a).rep := fun a =>
    GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA (x a) (hx a) (y a).rep (y a).2.rep.smooth (φ a) (hne a)
  have hcat := sum_concat_fst y hy c x hx
  have hle := GlobalTheory.T.jacquet_multiplicity_concat hA y hy c x hx hcat hjm π hs (hasFiniteLength_of_isIrreducible hi)
  have hcc : ∀ i, (concat c x i).IsCusp := fun i => hcusp _ _
  obtain ⟨hlen, -⟩ := (fine π hL).2 _ (concat c x) hcat hcc (h1.trans hle)
  have hc1 : ∀ a, 1 ≤ c a := fun a => by
    by_contra hc
    have hc0 : c a = 0 := by omega
    have h2 := hx a
    have h3 := hpos a
    have : IsEmpty (Fin (c a)) := by rw [hc0]; infer_instance
    rw [Fintype.sum_empty] at h2
    omega
  have hsum : ∑ a : Fin Δ.len, 1 = ∑ a, c a := by simpa using hlen.symm
  have hc : ∀ a, c a = 1 := fun a =>
    ((Finset.sum_eq_sum_iff_of_le fun a _ => hc1 a).1 hsum a (Finset.mem_univ a)).symm
  have hyc : ∀ a, (y a).IsCusp := fun a => by
    obtain ⟨b, hb⟩ := exists_eq_of_embeds_one (hc a) (x a) (y a) (hx a) (φ a) (hφ a)
    exact hb ▸ hcusp a b
  obtain ⟨h, hdec⟩ := (fine π hL).2 _ y hy hyc h1
  exact funext fun a => by simpa using hdec a

theorem isLSeg_of_dec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) (Δ : Segment k) {N : ℕ}
    (hd : ∑ a, (dec Δ a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth τ) (hi : τ.IsIrreducible)
    (f : τ.IntertwiningMap (prodIrr (dec Δ) hd)) (hf : Function.Injective f), IsLSeg Δ τ := by
  intro k _ _ _ _ hA hZ Δ N hd V _ _ τ hs hi f hf
  have fine : FineJac Δ := @fineJac_all k _ _ _ _ hA hZ Δ
  obtain ⟨L, hL⟩ := GlobalTheory.TL.exists_segment_representation hA Δ
  have hN : Δ.deg = N := by
    rw [← hd]
    show Δ.deg = ∑ _ : Fin Δ.len, Δ.d
    simp [Segment.deg]
  subst hN
  have hone := (fine L.ρ hL).1 hd
  let e := stdBlocks (fun a => (dec Δ a).1) hd
  have hfl : HasFiniteLength (jac e L.ρ) :=
    GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ e _ L.ρ L.smooth (hasFiniteLength_of_isIrreducible L.irr)
  haveI : WellFoundedGT (Subrepresentation (jac e L.ρ)) := ((hasFiniteLength_iff_wellFounded _).1 hfl).1
  have h0 : jm (dec Δ) hd L.ρ ≠ 0 := by rw [hone]; exact one_ne_zero
  have hne : (⊥ : Subrepresentation (jac e L.ρ)) ≠ ⊤ :=
    bot_ne_top_of_isSubquotient (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (dec Δ)) (jhMult_ne_zero_iff.1 h0)
  obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation (jac e L.ρ))).resolve_left hne
  let q : (jac e L.ρ).IntertwiningMap (subQuot ⊤ M) :=
    ⟨(Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation (jac e L.ρ)).toSubmodule
      LinearMap.id (fun v => trivial), fun g => rfl⟩
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨v, rfl⟩
  have hirr : (subQuot ⊤ M).IsIrreducible := isIrreducible_subQuot hM.covBy_top
  have hsq : IsSubquotient (subQuot ⊤ M) (jac e L.ρ) := .of_surjective q hq
  obtain ⟨σ, ⟨ψ⟩⟩ := GlobalTheory.T.levi_irreducible_tensor_decomposition hA (fun a => (dec Δ a).1)
    ⟨_, subQuot ⊤ M, hsq.isSmooth (isSmooth_jac e L.smooth), hirr⟩
  let y : Fin Δ.len → IrrGL k := fun a => ⟨(dec Δ a).1, σ a⟩
  have hy : ∑ a, (y a).1 = Δ.deg := hd
  let g : (jac (stdBlocks (fun a => (y a).1) hy) L.ρ).IntertwiningMap (piTensor fun a => (y a).rep) :=
    ψ.toIntertwiningMap.comp q
  have hg : Function.Surjective g := ψ.toLinearEquiv.surjective.comp hq
  have h1 : 1 ≤ jm y hy L.ρ :=
    ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 (IsSubquotient.of_surjective g hg))
  have hyeq : y = dec Δ := eq_dec_of_one_le_jm hA fine L.ρ hL L.smooth L.irr y hy
    (fun a => Δ.d_pos) h1
  obtain ⟨w, hw⟩ := exists_ne_zero_of_surjective (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA y) g hg
  have hfrob := GlobalTheory.T.frobenius_reciprocity_nonzero y hy L.ρ L.smooth g ⟨w, hw⟩
  have htr : ∀ (y' : Fin Δ.len → IrrGL k) (_ : y = y') (hy' : ∑ a, (y' a).1 = Δ.deg),
      (∃ g : L.ρ.IntertwiningMap (prodIrr y hy), ∃ v, g v ≠ 0) →
        ∃ g : L.ρ.IntertwiningMap (prodIrr y' hy'), ∃ v, g v ≠ 0 := by
    rintro _ rfl _ h
    exact h
  obtain ⟨g', v, hv⟩ := htr _ hyeq hd hfrob
  have hemb : Embeds L.ρ (prodIrr (dec Δ) hd) :=
    (isotypic_ne_bot_iff_embeds L.irr).1 (isotypic_ne_bot_iff.2 ⟨g', fun e' => hv (by rw [e']; rfl)⟩)
  obtain ⟨S, hS⟩ := GlobalTheory.TL.exists_socle_segment_product hA Δ hd
  obtain ⟨a⟩ := hS.equiv_of_embeds hi ⟨f, hf⟩
  obtain ⟨b⟩ := hS.equiv_of_embeds L.irr hemb
  exact hL.of_equiv (b.trans a.symm)

end GlobalTheory.CompanionTheory.LkSegUniq

end
end

section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
theorem _root_.GlobalTheory.TL.irreducible_sub_segment_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) (Δ : Segment k) {N : ℕ} (hd : ∑ a, (dec Δ a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth τ) (hi : τ.IsIrreducible) (f : τ.IntertwiningMap (prodIrr (dec Δ) hd)) (hf : Function.Injective f), IsLSeg Δ τ := by
  first | exact @GlobalTheory.CompanionTheory.LkSegUniq.isLSeg_of_dec | exact GlobalTheory.CompanionTheory.LkSegUniq.isLSeg_of_dec
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.LkSegCoarse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) : Fin s → Segment k := fun a =>
  Segment.ofFirst (Δ.first.nu ((∑ b ∈ Finset.univ.filter (fun b => a < b), c b : ℕ) : ℂ)) (Δ.isCusp_first.nu _)
    (c a) (hc a)

@[simp] theorem len_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (a : Fin s) :
    (topCut Δ c hc a).len = c a := rfl

theorem isTopCut_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (h : ∑ a, c a = Δ.len) :
    IsTopCut Δ (topCut Δ c hc) :=
  ⟨h, fun _ => rfl⟩

theorem eq_topCut {Δ : Segment k} {s : ℕ} {Γ : Fin s → Segment k} (h : IsTopCut Δ Γ) :
    Γ = topCut Δ (fun a => (Γ a).len) (fun a => (Γ a).len_pos) :=
  funext fun a => Segment.ext_first (by rw [h.2 a]; rfl) rfl

theorem sum_split {s : ℕ} (c : Fin s → ℕ) (a : Fin s) :
    ∑ b, c b = (∑ t : Fin a, c (Fin.castLE a.2.le t)) + c a + ∑ b ∈ Finset.univ.filter (fun b => a < b), c b := by
  have h1 : ∑ t : Fin a, c (Fin.castLE a.2.le t) = ∑ b ∈ Finset.univ.filter (fun b : Fin s => b < a), c b := by
    refine Finset.sum_bij (fun t _ => Fin.castLE a.2.le t)
      (fun t _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.lt_def.2 t.2⟩)
      (fun t _ u _ h => Fin.castLE_injective _ h) (fun b hb => ?_) (fun _ _ => rfl)
    have hb' : (b : ℕ) < a := Fin.lt_def.1 (Finset.mem_filter.1 hb).2
    exact ⟨⟨b, hb'⟩, Finset.mem_univ _, rfl⟩
  rw [h1]
  have h2 : ∑ b, c b = ∑ b, ((if b < a then c b else 0) + (if b = a then c b else 0) + (if a < b then c b else 0)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases lt_trichotomy b a with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  rw [h2, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    ← Finset.sum_filter, Finset.filter_eq', if_pos (Finset.mem_univ _), Finset.sum_singleton]

theorem concat_dec_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (h : ∑ a, c a = Δ.len)
    (i : Fin (∑ a, c a)) : concat c (fun a => dec (topCut Δ c hc a)) i = dec Δ (Fin.cast h i) := by
  show dec (topCut Δ c hc (finSigmaFinEquiv.symm i).1) (finSigmaFinEquiv.symm i).2 = dec Δ (Fin.cast h i)
  rcases hq : finSigmaFinEquiv.symm i with ⟨a, j⟩
  have hi : (i : ℕ) = (∑ t : Fin a, c (Fin.castLE a.2.le t)) + j := by
    rw [← Equiv.apply_symm_apply finSigmaFinEquiv i, hq, finSigmaFinEquiv_apply]
  have hs := sum_split c a
  have hj : (j : ℕ) < c a := j.2
  simp only [dec, Segment.term, topCut, Segment.first_ofFirst, IrrGL.nu_nu]
  congr 1
  simp only [Fin.val_rev, Fin.val_cast, Segment.len_ofFirst]
  have key : Δ.len - (i + 1) = (∑ b ∈ Finset.univ.filter (fun b => a < b), c b) + (c a - (j + 1)) := by
    rw [← h]; omega
  rw [key]
  push_cast
  ring

theorem concat_injective {s : ℕ} {c : Fin s → ℕ} {x x' : ∀ a, Fin (c a) → IrrGL k} (h : concat c x = concat c x') :
    x = x' := by
  funext a j
  have := congrFun h (finSigmaFinEquiv ⟨a, j⟩)
  change (fun p : (b : Fin s) × Fin (c b) => x p.1 p.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨a, j⟩)) =
    (fun p : (b : Fin s) × Fin (c b) => x' p.1 p.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨a, j⟩)) at this
  rw [Equiv.symm_apply_apply] at this
  exact this

theorem concat_apply_equiv {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL k) (p : (a : Fin s) × Fin (c a)) :
    concat c x (finSigmaFinEquiv p) = x p.1 p.2 := by
  change (fun q : (b : Fin s) × Fin (c b) => x q.1 q.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv p)) = _
  rw [Equiv.symm_apply_apply]

theorem sum_concat {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL k) :
    ∑ i, (concat c x i).1 = ∑ a, ∑ j, (x a j).1 := by
  rw [← Equiv.sum_comp finSigmaFinEquiv, Fintype.sum_sigma]
  simp only [concat_apply_equiv]

theorem sum_dec (Δ : Segment k) : ∑ a, (dec Δ a).1 = Δ.deg := by
  rw [← Segment.sum_term_fst]
  exact Equiv.sum_comp Fin.revPerm (fun a => (Δ.term a).1)

theorem deg_topCut (Δ : Segment k) {s : ℕ} (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (a : Fin s) :
    (topCut Δ c hc a).deg = c a * Δ.d := rfl

theorem jm_reindex {n m N : ℕ} (h : n = m) (x : Fin n → IrrGL k) (x' : Fin m → IrrGL k)
    (hx : ∀ i, x i = x' (Fin.cast h i)) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : jm x hd π = jm x' hd' π := by
  subst h
  obtain rfl : x = x' := funext fun i => by simpa using hx i
  rfl

theorem eq_of_isLSeg {Γ : Segment k} {x x' : IrrGL k} (h : IsLSeg Γ x.rep) (h' : IsLSeg Γ x'.rep) : x = x' := by
  obtain ⟨n, c⟩ := x
  obtain ⟨n', c'⟩ := x'
  have e1 := h.deg_eq
  have e2 := h'.deg_eq
  obtain rfl : n = n' := e1.symm.trans e2
  obtain ⟨φ⟩ := h.unique h'
  have := (IrrGL.of_eq_of (π := IrrGL.rep (k := k) ⟨n, c'⟩) (σ := IrrGL.rep (k := k) ⟨n, c⟩)
    (hs := c'.rep.smooth) (hi := c'.rep.irr) (hs' := c.rep.smooth) (hi' := c.rep.irr)).2 ⟨φ⟩
  rw [IrrGL.of_rep, IrrGL.of_rep] at this
  exact this.symm

end GlobalTheory.CompanionTheory.LkSegCoarse

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg GlobalTheory.CompanionTheory.LkSegCoarse

namespace GlobalTheory.CompanionTheory.LkSegCoarse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fineJac_all (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) :
    ∀ Δ : Segment k, FineJac Δ := by
  intro Δ
  induction h : Δ.len using Nat.strong_induction_on generalizing Δ with
  | _ n ih =>
    have hp := Δ.len_pos
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n
      · omega
      · exact @GlobalTheory.T.fine_jacquet_length_one k _ _ _ _ hA Δ h
      · exact @GlobalTheory.TL.fine_jacquet_segment_length_two k _ _ _ _ hA hZ Δ h
    · exact @GlobalTheory.TL.fine_jacquet_segment_induction k _ _ _ _ hA Δ (h ▸ h3) fun Δ' hlt => ih _ (h ▸ hlt) Δ' rfl

theorem occurs_topCut (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation)
    (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hπ : IsLSeg Δ π) {s : ℕ} (y : Fin s → IrrGL k) (hd : ∑ a, (y a).1 = N) (hpos : ∀ a, 0 < (y a).1)
    (h1 : 1 ≤ jm y hd π) :
    ∃ (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (_ : ∑ a, c a = Δ.len)
      (hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N),
      jm y hd π ≤ jm (concat c (fun a => dec (topCut Δ c hc a))) hcat π ∧
        ∀ a, IsLSeg (topCut Δ c hc a) (y a).rep := by
  choose c x hx hcusp hemb using fun a =>
    GlobalTheory.T.support_subscheme_embedding k (y a).1 _ (y a).rep (y a).2.rep.smooth (y a).2.rep.irr
  have hjx : ∀ a, 1 ≤ jm (x a) (hx a) (y a).rep := fun a => by
    obtain ⟨φ, hφ⟩ := hemb a
    have := Model.nontrivial_of_isIrreducible (y a).2.rep.irr
    obtain ⟨v, hv⟩ := exists_ne (0 : (y a).2.rep.V)
    exact GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA (x a) (hx a) (y a).rep (y a).2.rep.smooth φ
      ⟨v, fun e => hv (hφ (e.trans (map_zero φ).symm))⟩
  have hcat0 : ∑ i, (concat c x i).1 = N := by
    rw [sum_concat, ← hd]
    exact Finset.sum_congr rfl fun a _ => hx a
  have hirr : π.IsIrreducible := hπ.2.1
  have hsm : IsSmooth π := hπ.hasSupport.isSmooth
  have hle := GlobalTheory.T.jacquet_multiplicity_concat hA y hd c x hx hcat0 hjx π hsm (hasFiniteLength_of_isIrreducible hirr)
  have h1' : 1 ≤ jm (concat c x) hcat0 π := h1.trans hle
  obtain ⟨hl, hfine⟩ := (fineJac_all hA hZ Δ π hπ).2 _ (concat c x) hcat0 (fun i => hcusp _ _) h1'
  have hc : ∀ a, 0 < c a := fun a => by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have : IsEmpty (Fin (c a)) := by rw [h0]; infer_instance
    have := hx a
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact (hpos a).ne this
  have hxeq : x = fun a => dec (topCut Δ c hc a) :=
    concat_injective (funext fun i => (hfine i).trans (concat_dec_topCut Δ c hc hl i).symm)
  subst hxeq
  refine ⟨c, hc, hl, hcat0, hle, fun a => ?_⟩
  obtain ⟨φ, hφ⟩ := hemb a
  exact GlobalTheory.TL.irreducible_sub_segment_product hA hZ (topCut Δ c hc a) (hx a) (y a).rep (y a).2.rep.smooth (y a).2.rep.irr φ hφ

theorem lSegJacquet : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation), LSegJacquet k := by
  intro k _ _ _ _ hA hZ Δ N V _ _ π hπ s y hd hpos
  have hdΔ : ∑ a, (dec Δ a).1 = N := (sum_dec Δ).trans hπ.deg_eq
  have hone := (fineJac_all hA hZ Δ π hπ).1 hdΔ
  have hirr : π.IsIrreducible := hπ.2.1
  have hsm : IsSmooth π := hπ.hasSupport.isSmooth

  have hread : ∀ (c : Fin s → ℕ) (hc : ∀ a, 0 < c a) (hl : ∑ a, c a = Δ.len)
      (hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N),
      jm (concat c (fun a => dec (topCut Δ c hc a))) hcat π = 1 := fun c hc hl hcat =>
    (jm_reindex hl _ _ (concat_dec_topCut Δ c hc hl) hcat hdΔ π).trans hone
  have hB : 1 ≤ jm y hd π → ∃ Γ : Fin s → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (y a).rep := fun h1 => by
    obtain ⟨c, hc, hl, -, -, hL⟩ := occurs_topCut hA hZ Δ π hπ y hd hpos h1
    exact ⟨topCut Δ c hc, isTopCut_topCut Δ c hc hl, hL⟩
  have hC : jm y hd π ≤ 1 := by
    by_cases h0 : jm y hd π = 0
    · rw [h0]; exact zero_le_one
    · obtain ⟨c, hc, hl, hcat, hle, -⟩ := occurs_topCut hA hZ Δ π hπ y hd hpos (ENat.one_le_iff_ne_zero.2 h0)
      exact hle.trans (hread c hc hl hcat).le
  have hD : (∃ Γ : Fin s → Segment k, IsTopCut Δ Γ ∧ ∀ a, IsLSeg (Γ a) (y a).rep) → 1 ≤ jm y hd π := by
    rintro ⟨Γ, hΓ, hL⟩
    have hΓe := eq_topCut hΓ
    set c : Fin s → ℕ := fun a => (Γ a).len with hcdef
    have hc : ∀ a, 0 < c a := fun a => (Γ a).len_pos
    have hl : ∑ a, c a = Δ.len := hΓ.1
    have hcat : ∑ i, (concat c (fun a => dec (topCut Δ c hc a)) i).1 = N :=
      (Fintype.sum_equiv (finCongr hl) _ _ fun i => by rw [concat_dec_topCut Δ c hc hl]; rfl).trans hdΔ
    have hxpos : ∀ a, 0 < ∑ i, (dec (topCut Δ c hc a) i).1 := fun a => by
      rw [sum_dec, deg_topCut]; exact Nat.mul_pos (hc a) Δ.d_pos
    obtain ⟨σ, hσ, hσd, h1σ⟩ := GlobalTheory.T.concatenated_jacquet_multiplicity_factorization hA c (fun a => dec (topCut Δ c hc a)) hxpos hcat π hsm
      (hasFiniteLength_of_isIrreducible hirr) (hread c hc hl hcat).ge
    have hσpos : ∀ a, 0 < (σ a).1 := fun a => (hσd a).symm ▸ hxpos a
    obtain ⟨c', hc', hl', -, -, hL'⟩ := occurs_topCut hA hZ Δ π hπ σ hσ hσpos h1σ
    have hsd : ∀ a, ∑ i : Fin (c a), (dec (topCut Δ c hc a) i).1 = c a * Δ.d := fun a =>
      (sum_dec _).trans (deg_topCut Δ c hc a)
    have hcc : c' = c := funext fun a => by
      have e1 := (hL' a).deg_eq
      rw [deg_topCut, hσd a, hsd a] at e1
      exact Nat.eq_of_mul_eq_mul_right Δ.d_pos e1
    subst hcc
    have hσy : σ = y := funext fun a => by
      have h2 : IsLSeg (topCut Δ c hc' a) (y a).rep := by
        have := hL a
        rw [hΓe] at this
        exact this
      exact eq_of_isLSeg (hL' a) h2
    subst hσy
    exact h1σ
  refine ⟨fun h => le_antisymm hC (hD h), fun h => ?_⟩
  by_contra h0
  exact h (hB (ENat.one_le_iff_ne_zero.2 h0))

end GlobalTheory.CompanionTheory.LkSegCoarse

end
end

section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
theorem _root_.GlobalTheory.TL.segment_jacquet_all : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation), LSegJacquet k := by
  first | exact @GlobalTheory.CompanionTheory.LkSegCoarse.lSegJacquet | exact GlobalTheory.CompanionTheory.LkSegCoarse.lSegJacquet
end
