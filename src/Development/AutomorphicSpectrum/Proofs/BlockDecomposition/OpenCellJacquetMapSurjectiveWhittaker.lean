import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalDecompositionNormalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionToTwistedEigenfunctionSupportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorCompactUnipotentFixerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSupport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellFunctionCompactSupportUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalDecompositionNormal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellUnipotentUniquenessClosed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactSubgroupOfFinset

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.LeviPart

section Order

variable {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

def pos : (Σ a, Fin (d a)) ≃ Fin N := (stdBlocks d hd).trans (wOpen d hd).symm

theorem wOpen_pos (x : Σ a, Fin (d a)) : wOpen d hd (pos d hd x) = stdBlocks d hd x := by
  simp [pos]

theorem wKey_injective : Function.Injective (wKey d hd) := by
  intro x y hxy
  exact congrArg (fun z => (ofLex z).2) hxy

theorem key_strictMono : StrictMono (wKey d hd ∘ wOpen d hd) :=
  (Tuple.monotone_sort (wKey d hd)).strictMono_of_injective
    ((wKey_injective d hd).comp (wOpen d hd).injective)

theorem blk_std (x : Σ a, Fin (d a)) : blk (stdBlocks d hd) (stdBlocks d hd x) = x.1 := by
  simp [blk]

theorem key_lt (x y : Σ a, Fin (d a)) :
    wKey d hd (stdBlocks d hd x) < wKey d hd (stdBlocks d hd y) ↔
      y.1 < x.1 ∨ x.1 = y.1 ∧ stdBlocks d hd x < stdBlocks d hd y := by
  rw [wKey, wKey, Prod.Lex.lt_iff]
  simp [blk_std]

theorem std_lt (a : Fin h) (i j : Fin (d a)) :
    stdBlocks d hd ⟨a, i⟩ < stdBlocks d hd ⟨a, j⟩ ↔ i < j := by
  rw [Fin.lt_def, stdBlocks_val, stdBlocks_val, Fin.lt_def]
  omega

theorem pos_lt_iff (x y : Σ a, Fin (d a)) :
    pos d hd x < pos d hd y ↔ y.1 < x.1 ∨ x.1 = y.1 ∧ stdBlocks d hd x < stdBlocks d hd y := by
  rw [← (key_strictMono d hd).lt_iff_lt, Function.comp, Function.comp, wOpen_pos, wOpen_pos, key_lt]

theorem pos_lt (a : Fin h) (i j : Fin (d a)) : pos d hd ⟨a, i⟩ < pos d hd ⟨a, j⟩ ↔ i < j := by
  rw [pos_lt_iff, std_lt]
  simp

theorem pos_succ (a : Fin h) (i j : Fin (d a)) (hij : (j : ℕ) = i + 1) :
    (pos d hd ⟨a, j⟩ : ℕ) = pos d hd ⟨a, i⟩ + 1 := by
  have hlt : pos d hd ⟨a, i⟩ < pos d hd ⟨a, j⟩ := (pos_lt d hd a i j).2 (Fin.lt_def.2 (by omega))
  by_contra hne
  have hlt' := Fin.lt_def.1 hlt
  have hN := (pos d hd ⟨a, j⟩).2
  let t : Fin N := ⟨pos d hd ⟨a, i⟩ + 1, by omega⟩
  obtain ⟨⟨b, l⟩, hl⟩ := (pos d hd).surjective t
  have h1 : pos d hd ⟨a, i⟩ < pos d hd ⟨b, l⟩ := by
    rw [hl]; exact Fin.lt_def.2 (by simp [t])
  have h2 : pos d hd ⟨b, l⟩ < pos d hd ⟨a, j⟩ := by
    rw [hl]; exact Fin.lt_def.2 (by simp only [t]; omega)
  rw [pos_lt_iff] at h1 h2
  have hab : a = b := by
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact absurd h1 (lt_asymm h2)
      · exact absurd h2.1 (ne_of_lt h1)
    · exact h1.1
  subst hab
  have h3 := (std_lt d hd a i l).1 (h1.elim (fun e => absurd e (lt_irrefl _)) (·.2))
  have h4 := (std_lt d hd a l j).1 (h2.elim (fun e => absurd e (lt_irrefl _)) (·.2))
  have := Fin.lt_def.1 h3
  have := Fin.lt_def.1 h4
  omega

theorem pos_succ' (a : Fin h) (i j : Fin (d a)) (hij : (pos d hd ⟨a, j⟩ : ℕ) = pos d hd ⟨a, i⟩ + 1) :
    (j : ℕ) = i + 1 := by
  have hlt : i < j := (pos_lt d hd a i j).1 (Fin.lt_def.2 (by omega))
  by_contra hne
  have hlt' := Fin.lt_def.1 hlt
  have hj := j.2
  let l : Fin (d a) := ⟨i + 1, by omega⟩
  have h1 := Fin.lt_def.1 ((pos_lt d hd a i l).2 (Fin.lt_def.2 (by simp [l])))
  have h2 := Fin.lt_def.1 ((pos_lt d hd a l j).2 (Fin.lt_def.2 (by simp only [l]; omega)))
  omega

theorem sum_superdiag {R : Type} [AddCommMonoid R] (A : Fin N → Fin N → R)
    (hA : ∀ x y : Σ a, Fin (d a), x.1 ≠ y.1 → A (pos d hd x) (pos d hd y) = 0) :
    ∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1, A p.1 p.2 =
      ∑ b, ∑ p : Fin (d b) × Fin (d b) with (p.2 : ℕ) = p.1 + 1, A (pos d hd ⟨b, p.1⟩) (pos d hd ⟨b, p.2⟩) := by
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => (pos d hd ⟨x.1, x.2.1⟩, pos d hd ⟨x.1, x.2.2⟩)) ?_ ?_ ?_ ?_
  · rintro ⟨b, i, j⟩ hx -
    have hx' : (j : ℕ) = i + 1 := by simpa using hx
    simpa using pos_succ d hd b i j hx'
  · rintro ⟨b, i, j⟩ - - ⟨c, i', j'⟩ - - hxy
    have h1 := (pos d hd).injective (Prod.ext_iff.1 hxy).1
    have h2 := (pos d hd).injective (Prod.ext_iff.1 hxy).2
    simp only [Sigma.mk.injEq] at h1 h2
    obtain ⟨rfl, h1⟩ := h1
    obtain ⟨-, h2⟩ := h2
    obtain rfl := eq_of_heq h1
    obtain rfl := eq_of_heq h2
    rfl
  · rintro ⟨p, q⟩ hpq hne
    have hpq' : (q : ℕ) = p + 1 := by simpa using hpq
    obtain ⟨⟨b, i⟩, rfl⟩ := (pos d hd).surjective p
    obtain ⟨⟨c, j⟩, rfl⟩ := (pos d hd).surjective q
    have hbc : b = c := by
      by_contra hbc
      exact hne (hA _ _ hbc)
    subst hbc
    refine ⟨⟨b, i, j⟩, ?_, hne, rfl⟩
    simpa using pos_succ' d hd b i j hpq'
  · intro x _ _
    rfl

end Order

section Entries

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

theorem conj_apply (w : Equiv.Perm (Fin N)) (A : GL (Fin N) k) (p q : Fin N) :
    ((pm k w * A * (pm k w)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (w p) (w q) =
      (A : Matrix (Fin N) (Fin N) k) p q := by
  rw [← map_inv, Units.val_mul, GroundTheory.Automorphic.mul_permGL_apply, Units.val_mul,
    GroundTheory.Automorphic.permGL_mul_apply]
  simp

variable {d hd}
variable {A : GL (Fin N) k} {m : Levi k fun a => Fin (d a)}

theorem ent_same (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m)
    (b : Fin h) (i j : Fin (d b)) :
    (m b : Matrix (Fin (d b)) (Fin (d b)) k) i j =
      (A : Matrix (Fin N) (Fin N) k) (pos d hd ⟨b, i⟩) (pos d hd ⟨b, j⟩) := by
  rw [← leviEmb_apply_same k (stdBlocks d hd) m b i j, ← hm, ← wOpen_pos d hd, ← wOpen_pos d hd, conj_apply]

theorem ent_ne (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m)
    (x y : Σ a, Fin (d a)) (hxy : x.1 ≠ y.1) :
    (A : Matrix (Fin N) (Fin N) k) (pos d hd x) (pos d hd y) = 0 := by
  obtain ⟨b, i⟩ := x
  obtain ⟨c, j⟩ := y
  rw [← conj_apply (wOpen d hd) A, wOpen_pos, wOpen_pos, hm]
  exact leviEmb_apply_ne k (stdBlocks d hd) m hxy i j

theorem mem_unipM_of (hA : A ∈ unipB k (Fin N))
    (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m) :
    m ∈ unipM k d := by
  obtain ⟨h1, h2⟩ := (mem_unipB k).1 hA
  refine fun b _ => (mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [ent_same hm]
    exact h1 _ _ ((pos_lt d hd b j i).2 hij)
  · rw [ent_same hm]
    exact h2 _

theorem addChar_sum {ι : Type} (ψ : AddChar k Circle) (s : Finset ι) (f : ι → k) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem whit_eq (ψ : AddChar k Circle) (hA : A ∈ unipB k (Fin N)) (hm' : m ∈ unipM k d)
    (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m) :
    whitChar ψ N ⟨A, hA⟩ = whitM d ψ ⟨m, hm'⟩ := by
  show Circle.toUnits (ψ _) = ∏ a : Fin h, Circle.toUnits (ψ _)
  rw [← map_prod, ← addChar_sum]
  refine congrArg _ (congrArg _ ?_)
  refine (sum_superdiag d hd (fun p q => (A : Matrix (Fin N) (Fin N) k) p q) (ent_ne hm)).trans ?_
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun p _ => (ent_same hm b p.1 p.2).symm

theorem mem_unipB_of (hm' : m ∈ unipM k d)
    (hm : pm k (wOpen d hd) * A * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m) :
    A ∈ unipB k (Fin N) := by
  refine (mem_unipB k).2 ⟨fun p q hpq => ?_, fun p => ?_⟩
  · obtain ⟨⟨b, i⟩, rfl⟩ := (pos d hd).surjective p
    obtain ⟨⟨c, j⟩, rfl⟩ := (pos d hd).surjective q
    by_cases hbc : b = c
    · subst hbc
      rw [← ent_same hm]
      exact ((mem_unipB k).1 (hm' b (Set.mem_univ b))).1 i j ((pos_lt d hd b j i).1 hpq)
    · exact ent_ne hm _ _ hbc
  · obtain ⟨⟨b, i⟩, rfl⟩ := (pos d hd).surjective p
    rw [← ent_same hm]
    exact ((mem_unipB k).1 (hm' b (Set.mem_univ b))).2 i

end Entries

theorem levi_part : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ (a : GL (Fin N) k) (ha : a ∈ unipL k d hd) (hb : a ∈ unipB k (Fin N)), ∃ m : unipM k d, pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 ∧ whitChar ψ N ⟨a, hb⟩ = whitM d ψ m) ∧ ∀ m : unipM k d, ∃ a ∈ unipL k d hd, pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 := by
  intro k _ _ _ _ ψ h N d hd
  refine ⟨fun a ha hb => ?_, fun m => ?_⟩
  · obtain ⟨m₀, hm₀⟩ := (Subgroup.mem_inf.1 ha).2
    have hm : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m₀ := hm₀.symm
    have hm' := mem_unipM_of hb hm
    exact ⟨⟨m₀, hm'⟩, hm, whit_eq ψ hb hm' hm⟩
  · have hc : pm k (wOpen d hd) * ((pm k (wOpen d hd))⁻¹ * leviEmb k (stdBlocks d hd) m.1 * pm k (wOpen d hd)) *
        (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 := by group
    exact ⟨_, Subgroup.mem_inf.2 ⟨mem_unipB_of m.2 hc, ⟨m.1, hc.symm⟩⟩, hc⟩

end GlobalTheory.CompanionTheory.Rodier.LeviPart
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_cell_levi_unipotent_conjugation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ (a : GL (Fin N) k) (ha : a ∈ unipL k d hd) (hb : a ∈ unipB k (Fin N)), ∃ m : unipM k d, pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 ∧ whitChar ψ N ⟨a, hb⟩ = whitM d ψ m) ∧ ∀ m : unipM k d, ∃ a ∈ unipL k d hd, pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Rodier.LeviPart.levi_part
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.OpenExact

theorem mem_span_openFns_of_mem_twKer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (Q : Subgroup (GL (Fin N) k)), Q ≤ unipB k (Fin N) → (∀ s : Finset (GL (Fin N) k), (↑s : Set (GL (Fin N) k)) ⊆ Q → ∃ L : Subgroup (GL (Fin N) k), L ≤ Q ∧ (↑s : Set (GL (Fin N) k)) ⊆ L ∧ IsCompact (L : Set (GL (Fin N) k))) → ∀ θ : Q →* ℂˣ, (∀ (q : Q) (hq : (q : GL (Fin N) k) ∈ unipB k (Fin N)), θ q = whitChar ψ N ⟨q, hq⟩) → ∀ f ∈ openFns d hd ρ, f ∈ twKer (parInd (stdBlocks d hd) ρ) Q θ → f ∈ Submodule.span ℂ {x | ∃ (q : Q), ∃ g ∈ openFns d hd ρ, x = parInd (stdBlocks d hd) ρ q g - (θ q : ℂ) • g} := by
  intro k _ _ _ _ ψ hψ h N d hd W _ _ ρ Q hQ hex θ hθ f hf hker
  let σ : Representation ℂ Q (IndSp (stdBlocks d hd) ρ) := (parInd (stdBlocks d hd) ρ).comp Q.subtype
  have hI : ∀ t : Q, ∀ v ∈ openFns d hd ρ, σ t v ∈ openFns d hd ρ := by
    intro t v hv g hg
    have h1 : v.1.1 (g * (t : GL (Fin N) k)) ≠ 0 := hg
    obtain ⟨p, hp, n, hn, e⟩ := hv _ h1
    show ∃ p ∈ parab k (stdBlocks d hd), ∃ n ∈ unipB k (Fin N), g = p * pm k (wOpen d hd) * n
    refine ⟨p, hp, n * (t : GL (Fin N) k)⁻¹, mul_mem hn (inv_mem (hQ t.2)), ?_⟩
    rw [← mul_assoc, ← e]
    group
  have hσs : IsSmooth σ := fun v => (isSmooth_parInd (stdBlocks d hd) ρ v).preimage continuous_subtype_val
  let ρ' : Representation ℂ Q (openFns d hd ρ) := GlobalTheory.PRep.sub σ (openFns d hd ρ) hI
  have hρs : IsSmooth ρ' := by
    intro v
    have : {t : Q | ρ' t v = v} = {t : Q | σ t (v : IndSp (stdBlocks d hd) ρ) = v} := by
      ext t
      simp only [Set.mem_setOf_eq, Subtype.ext_iff]
      rfl
    rw [this]
    exact hσs _
  let θ' : (⊤ : Subgroup Q) →* ℂˣ := θ.comp (⊤ : Subgroup Q).subtype
  have hopen : IsOpen (θ'.ker : Set (⊤ : Subgroup Q)) := by
    have hw : IsOpen ((whitChar ψ N).ker : Set (unipB k (Fin N))) :=
      GlobalTheory.Whittaker.isSmoothChar_whitChar hψ
    let j : (⊤ : Subgroup Q) → unipB k (Fin N) := fun x => ⟨x.1.1, hQ x.1.2⟩
    have hj : Continuous j :=
      Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    have hset : (θ'.ker : Set (⊤ : Subgroup Q)) = j ⁻¹' ((whitChar ψ N).ker : Set (unipB k (Fin N))) := by
      ext x
      show θ x.1 = 1 ↔ whitChar ψ N (j x) = 1
      rw [hθ x.1 (hQ x.1.2)]
    rw [hset]
    exact hw.preimage hj
  have hexh : ∀ s : Finset Q, (↑s : Set Q) ⊆ (⊤ : Subgroup Q) →
      ∃ L : Subgroup Q, L ≤ ⊤ ∧ (↑s : Set Q) ⊆ L ∧ IsCompact (L : Set Q) := by
    classical
    intro s _
    obtain ⟨L, hLQ, hsL, hLc⟩ := hex (s.image Subtype.val) (by
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨a, -, rfl⟩ := hx
      exact a.2)
    refine ⟨L.subgroupOf Q, le_top, ?_, ?_⟩
    · intro x hx
      refine Subgroup.mem_subgroupOf.2 (hsL ?_)
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨x, hx, rfl⟩
    · rw [Subtype.isCompact_iff]
      have himg : ((↑) : Q → GL (Fin N) k) '' (L.subgroupOf Q : Set Q) = (L : Set (GL (Fin N) k)) := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact Subgroup.mem_subgroupOf.1 hy
        · intro hx
          exact ⟨⟨x, hLQ hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
      rw [himg]
      exact hLc
  have hle : twKer (parInd (stdBlocks d hd) ρ) Q θ ≤ twKer σ ⊤ θ' :=
    Submodule.span_le.2 (by
      rintro w ⟨q, v, rfl⟩
      exact Submodule.subset_span ⟨⟨q, trivial⟩, v, rfl⟩)
  have key : (⟨f, hf⟩ : openFns d hd ρ) ∈ twKer ρ' ⊤ θ' :=
    GlobalTheory.CompanionTheory.PRep.JacExact.twKer_reflect ρ' σ hρs hσs ⊤ θ' hopen hexh (openFns d hd ρ).subtype
      (Submodule.injective_subtype _) (fun _ _ => rfl) ⟨f, hf⟩ (hle hker)
  have hle2 : twKer ρ' ⊤ θ' ≤ (Submodule.span ℂ {x | ∃ (q : Q), ∃ g ∈ openFns d hd ρ,
      x = parInd (stdBlocks d hd) ρ q g - (θ q : ℂ) • g}).comap (openFns d hd ρ).subtype :=
    Submodule.span_le.2 (by
      rintro _ ⟨q, g, rfl⟩
      exact Submodule.subset_span ⟨q.1, g.1, g.2, rfl⟩)
  exact hle2 key

end GlobalTheory.CompanionTheory.Rodier.OpenExact
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_unipotent_subgroup_finite_generation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (Q : Subgroup (GL (Fin N) k)), Q ≤ unipB k (Fin N) → (∀ s : Finset (GL (Fin N) k), (↑s : Set (GL (Fin N) k)) ⊆ Q → ∃ L : Subgroup (GL (Fin N) k), L ≤ Q ∧ (↑s : Set (GL (Fin N) k)) ⊆ L ∧ IsCompact (L : Set (GL (Fin N) k))) → ∀ θ : Q →* ℂˣ, (∀ (q : Q) (hq : (q : GL (Fin N) k) ∈ unipB k (Fin N)), θ q = whitChar ψ N ⟨q, hq⟩) → ∀ f ∈ openFns d hd ρ, f ∈ twKer (parInd (stdBlocks d hd) ρ) Q θ → f ∈ Submodule.span ℂ {x | ∃ (q : Q), ∃ g ∈ openFns d hd ρ, x = parInd (stdBlocks d hd) ρ q g - (θ q : ℂ) • g} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Rodier.OpenExact.mem_span_openFns_of_mem_twKer
end

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HaarConj

theorem conj_measurePreserving : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] (U N : Subgroup G), IsClosed (U : Set G) → (∀ n ∈ N, ∀ u ∈ U, n * u * n⁻¹ ∈ U) → (∀ n ∈ N, ∃ L : Subgroup G, n ∈ L ∧ L ≤ N ∧ IsCompact (L : Set G)) → ∀ [MeasurableSpace U] [BorelSpace U] (μ : MeasureTheory.Measure U) [μ.IsHaarMeasure], ∀ n ∈ N, ∀ c : U → U, (∀ u, (c u : G) = n * u * n⁻¹) → MeasureTheory.MeasurePreserving c μ μ := by
  intro G _ _ _ _ _ _ U N hU hN hL _ _ μ _ n hn c hc
  have hninv : n⁻¹ ∈ N := N.inv_mem hn
  let d : U → U := fun u => ⟨n⁻¹ * u * n⁻¹⁻¹, hN _ hninv _ u.2⟩
  have hdc : ∀ u, d (c u) = u := fun u => Subtype.ext (by simp [d, hc, mul_assoc])
  have hcd : ∀ u, c (d u) = u := fun u => Subtype.ext (by simp [d, hc, mul_assoc])
  have hcmul : ∀ u v, c (u * v) = c u * c v := fun u v => Subtype.ext (by simp [hc, mul_assoc])
  have hcc : Continuous c := by
    refine Topology.IsEmbedding.subtypeVal.continuous_iff.2 ?_
    have : (Subtype.val ∘ c) = fun u : U => n * (u : G) * n⁻¹ := funext hc
    rw [this]
    fun_prop
  have hdc' : Continuous d := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  let e : U ≃* U :=
    { toFun := c, invFun := d, left_inv := hdc, right_inv := hcd, map_mul' := hcmul }
  haveI hH : (μ.map c).IsHaarMeasure := e.isHaarMeasure_map μ hcc hdc'
  haveI : LocallyCompactSpace U := hU.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology U := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨L, hnL, -, hLc⟩ := hL n hn
  obtain ⟨Q, hQc, hQn⟩ := exists_compact_mem_nhds (1 : U)
  let K : Set G := (fun p : G × G => p.1 * p.2 * p.1⁻¹) '' ((L : Set G) ×ˢ (Subtype.val '' Q))
  have hK : IsCompact K := (hLc.prod (hQc.image continuous_subtype_val)).image (by fun_prop)
  let Q' : Set U := Subtype.val ⁻¹' K
  have hQ'c : IsCompact Q' := hU.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hQQ' : Q ⊆ Q' := fun q hq =>
    ⟨(1, (q : G)), ⟨L.one_mem, ⟨q, hq, rfl⟩⟩, by simp⟩
  have hpos : 0 < μ Q' :=
    (MeasureTheory.Measure.measure_pos_of_mem_nhds μ hQn).trans_le (MeasureTheory.measure_mono hQQ')
  have hfin : μ Q' ≠ ⊤ := hQ'c.measure_lt_top.ne
  have hpre : c ⁻¹' Q' = Q' := by
    ext u
    constructor
    · rintro ⟨⟨l, q⟩, ⟨hl, hq⟩, h⟩
      refine ⟨(n⁻¹ * l, q), ⟨L.mul_mem (L.inv_mem hnL) hl, hq⟩, ?_⟩
      have h' : l * q * l⁻¹ = n * (u : G) * n⁻¹ := by
        rw [← hc]
        exact h
      change n⁻¹ * l * q * (n⁻¹ * l)⁻¹ = (u : G)
      calc n⁻¹ * l * q * (n⁻¹ * l)⁻¹ = n⁻¹ * (l * q * l⁻¹) * n := by group
        _ = (u : G) := by rw [h']; group
    · rintro ⟨⟨l, q⟩, ⟨hl, hq⟩, h⟩
      refine ⟨(n * l, q), ⟨L.mul_mem hnL hl, hq⟩, ?_⟩
      have h' : l * q * l⁻¹ = (u : G) := h
      change n * l * q * (n * l)⁻¹ = (c u : G)
      rw [hc, ← h']
      group
  have hmeas : MeasurableSet Q' := hQ'c.measurableSet
  have h1 : μ.map c Q' = μ Q' := by
    rw [MeasureTheory.Measure.map_apply hcc.measurable hmeas, hpre]
  have heq := MeasureTheory.Measure.isMulLeftInvariant_eq_smul (μ.map c) μ
  have h2 : ((MeasureTheory.Measure.haarScalarFactor (μ.map c) μ : NNReal) : ENNReal) * μ Q'
      = 1 * μ Q' := by
    have h3 := congrArg (fun ν : MeasureTheory.Measure U => ν Q') heq
    simp only [MeasureTheory.Measure.smul_apply, h1] at h3
    rw [one_mul]
    exact h3.symm.trans (by simp [ENNReal.smul_def])
  have hκ : MeasureTheory.Measure.haarScalarFactor (μ.map c) μ = 1 := by
    have := (ENNReal.mul_left_inj hpos.ne' hfin).1 h2
    exact_mod_cast this
  refine ⟨hcc.measurable, ?_⟩
  rw [heq, hκ, one_smul]

end GlobalTheory.CompanionTheory.HaarConj
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Rodier.RadInt

open MeasureTheory

theorem isLocallyConstant_of_right {X Y : Type} [TopologicalSpace X] [Group X] [IsTopologicalGroup X] (φ : X → Y)
    (S : Set X) (hS : IsOpen S) (h1 : (1 : X) ∈ S) (h : ∀ x, ∀ s ∈ S, φ (x * s) = φ x) : IsLocallyConstant φ := by
  refine (IsLocallyConstant.iff_eventually_eq φ).2 fun x => ?_
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' S) := hS.preimage (by fun_prop)
  filter_upwards [ho.mem_nhds (by simpa using h1)] with y hy
  have := h x _ hy
  simpa using this

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N}
variable {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (Levi k fun a => Fin (d a)) W}

theorem unipU_le : unipU k d hd ≤ unipB k (Fin N) := inf_le_left

theorem unipL_le : unipL k d hd ≤ unipB k (Fin N) := inf_le_left

def thetaU (ψ : AddChar k Circle) : unipU k d hd →* ℂˣ :=
  (whitChar ψ N).comp (Subgroup.inclusion unipU_le)

def phi (ψ : AddChar k Circle) (f : IndSp (stdBlocks d hd) ρ) (u : unipU k d hd) : W :=
  (((thetaU ψ u)⁻¹ : ℂˣ) : ℂ) • f.1.1 (pm k (wOpen d hd) * u.1)

theorem phi_add (ψ : AddChar k Circle) (f g : IndSp (stdBlocks d hd) ρ) :
    phi ψ (f + g) = phi ψ f + phi ψ g := by
  funext u
  show _ • (f.1.1 _ + g.1.1 _) = _
  simp [phi, smul_add]

theorem phi_smul (ψ : AddChar k Circle) (c : ℂ) (f : IndSp (stdBlocks d hd) ρ) :
    phi ψ (c • f) = (c • LinearMap.id : W →ₗ[ℂ] W) ∘ phi ψ f := by
  funext u
  exact smul_comm _ c _

theorem isLocallyConstant_phi {ψ : AddChar k Circle} (hψ : Continuous ψ) (f : IndSp (stdBlocks d hd) ρ) :
    IsLocallyConstant (phi ψ f) := by
  have h1 : IsOpen {g | parInd (stdBlocks d hd) ρ g f = f} := isSmooth_parInd _ _ f
  have h2 : IsOpen ((whitChar ψ N).ker : Set (unipB k (Fin N))) := GlobalTheory.Whittaker.isSmoothChar_whitChar hψ
  have hi : Continuous (Subgroup.inclusion (unipU_le (k := k) (d := d) (hd := hd))) :=
    continuous_subtype_val.subtype_mk _
  refine isLocallyConstant_of_right _
    ((Subtype.val ⁻¹' {g | parInd (stdBlocks d hd) ρ g f = f}) ∩
      (Subgroup.inclusion (unipU_le (k := k) (d := d) (hd := hd)) ⁻¹' ((whitChar ψ N).ker : Set _)))
    ((h1.preimage continuous_subtype_val).inter (h2.preimage hi)) ?_ ?_
  · refine ⟨?_, ?_⟩
    · simp
    · simp [one_mem]
  · rintro x s ⟨hs1, hs2⟩
    have e1 : thetaU ψ s = 1 := hs2
    have e2 : f.1.1 (pm k (wOpen d hd) * x.1 * s.1) = f.1.1 (pm k (wOpen d hd) * x.1) := by
      have : parInd (stdBlocks d hd) ρ s.1 f = f := hs1
      conv_rhs => rw [← this]
      rfl
    simp only [phi, map_mul, e1, mul_one, Subgroup.coe_mul, ← mul_assoc, e2]

theorem isClosed_unipU : IsClosed (unipU k d hd : Set (GL (Fin N) k)) := (GlobalTheory.CompanionTheory.Rodier.unipU_open_cell k h N d hd).2.2

theorem hasCompactSupport_phi (ψ : AddChar k Circle) (hρ : IsSmooth ρ) (f : IndSp (stdBlocks d hd) ρ)
    (hf : f ∈ openFns d hd ρ) : HasCompactSupport (phi ψ f) := by
  obtain ⟨L, hLU, hLc, -, hL⟩ := GlobalTheory.T.open_cell_function_compact_support_unipotent k h N d hd ρ hρ f hf
  refine HasCompactSupport.of_support_subset_isCompact (K := Subtype.val ⁻¹' (L : Set (GL (Fin N) k)))
    ((isClosed_unipU (k := k) (d := d) (hd := hd)).isClosedEmbedding_subtypeVal.isCompact_preimage hLc) ?_
  intro u hu
  have h0 : f.1.1 (pm k (wOpen d hd) * u.1) ≠ 0 := by
    intro e
    exact hu (by simp [phi, e])
  obtain ⟨p, hp, l, hl, e⟩ := hL _ h0
  have := (GlobalTheory.CompanionTheory.Rodier.unipU_open_cell k h N d hd).2.1 p hp l (hLU hl) u.1 u.2 e.symm
  show u.1 ∈ L
  rw [← this]
  exact hl

variable [MeasurableSpace (unipU k d hd)] [BorelSpace (unipU k d hd)]

def conjU (n : GL (Fin N) k) (hn : n ∈ unipB k (Fin N)) (u : unipU k d hd) : unipU k d hd :=
  ⟨n * u.1 * n⁻¹, (GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad k h N d hd).2 n hn u.1 u.2⟩

theorem measurePreserving_conjU (μ : Measure (unipU k d hd)) [μ.IsHaarMeasure] (n : GL (Fin N) k)
    (hn : n ∈ unipB k (Fin N)) : MeasurePreserving (conjU (d := d) (hd := hd) n hn) μ μ := by
  refine GlobalTheory.CompanionTheory.HaarConj.conj_measurePreserving (unipU k d hd) (unipB k (Fin N)) isClosed_unipU (GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad k h N d hd).2 ?_ μ n hn _
    fun _ => rfl
  intro n hn
  obtain ⟨L, h1, h2, h3⟩ := GlobalTheory.CompanionTheory.UnipExhaust.exists_compact_subgroup_of_finset k N {n} (by simpa using hn)
  exact ⟨L, h2 (by simp), h1, h3⟩

theorem measurePreserving_mul_right' (μ : Measure (unipU k d hd)) [μ.IsHaarMeasure] (u₀ : unipU k d hd) :
    MeasurePreserving (fun u => u * u₀) μ μ := by
  have h1 := measurePreserving_conjU μ (u₀.1)⁻¹ (inv_mem (unipU_le u₀.2))
  have h2 := measurePreserving_mul_left μ u₀
  convert h2.comp h1 using 1
  funext u
  apply Subtype.ext
  simp [conjU, mul_assoc]

theorem smInt_comp {X W' : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] [AddCommGroup W'] [Module ℂ W'] (T : W →ₗ[ℂ] W') (c : X → X) (φ : X → W)
    (hc : MeasurePreserving c μ μ) (h1 : IsLocallyConstant φ) (h2 : HasCompactSupport φ) :
    smInt μ (fun x => T (φ (c x))) = T (smInt μ φ) := by
  have a := (GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_properties (W := W) (W' := W') μ).2.1 T φ h1 h2
  have b := (GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_properties (W := W') (W' := W') μ).2.2.1 c (T ∘ φ) hc (h1.comp T)
  rw [← a, ← b]
  rfl

def radInt {ψ : AddChar k Circle} (hψ : Continuous ψ) (hρ : IsSmooth ρ) (μ : Measure (unipU k d hd)) [μ.IsHaarMeasure] :
    openFns d hd ρ →ₗ[ℂ] W where
  toFun f := smInt μ (phi ψ f.1)
  map_add' f g := by
    show smInt μ (phi ψ (f.1 + g.1)) = _
    rw [phi_add]
    exact (GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_properties (W := W) (W' := W) μ).1 _ _ (isLocallyConstant_phi hψ _)
      (hasCompactSupport_phi ψ hρ _ f.2) (isLocallyConstant_phi hψ _) (hasCompactSupport_phi ψ hρ _ g.2)
  map_smul' c f := by
    show smInt μ (phi ψ (c • f.1)) = _
    rw [phi_smul]
    exact (GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_properties (W := W) (W' := W) μ).2.1 _ _ (isLocallyConstant_phi hψ _)
      (hasCompactSupport_phi ψ hρ _ f.2)

theorem phi_right (ψ : AddChar k Circle) (f f' : IndSp (stdBlocks d hd) ρ) (u₀ : unipU k d hd)
    (hf' : f' = parInd (stdBlocks d hd) ρ u₀.1 f) :
    phi ψ f' = fun x => (((thetaU ψ u₀ : ℂˣ) : ℂ) • LinearMap.id : W →ₗ[ℂ] W) (phi ψ f (x * u₀)) := by
  subst hf'
  funext x
  have e : ((thetaU ψ x)⁻¹ : ℂˣ) = thetaU ψ u₀ * (thetaU ψ (x * u₀))⁻¹ := by
    rw [map_mul, mul_inv, mul_left_comm, mul_inv_cancel, mul_one]
  have e2 : (parInd (stdBlocks d hd) ρ u₀.1 f).1.1 (pm k (wOpen d hd) * x.1) =
      f.1.1 (pm k (wOpen d hd) * (x * u₀).1) := by
    rw [parInd_apply, Subgroup.coe_mul, mul_assoc]
  show (((thetaU ψ x)⁻¹ : ℂˣ) : ℂ) • (parInd (stdBlocks d hd) ρ u₀.1 f).1.1 (pm k (wOpen d hd) * x.1) =
    ((thetaU ψ u₀ : ℂˣ) : ℂ) • ((((thetaU ψ (x * u₀))⁻¹ : ℂˣ) : ℂ) • f.1.1 (pm k (wOpen d hd) * (x * u₀).1))
  rw [e, e2, Units.val_mul, mul_smul]

theorem radInt_right {ψ : AddChar k Circle} (hψ : Continuous ψ) (hρ : IsSmooth ρ) (μ : Measure (unipU k d hd))
    [μ.IsHaarMeasure] (u : GL (Fin N) k) (hu : u ∈ unipU k d hd) (hb : u ∈ unipB k (Fin N))
    (f f' : openFns d hd ρ) (hf : (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ u f) :
    radInt hψ hρ μ f' = (whitChar ψ N ⟨u, hb⟩ : ℂ) • radInt hψ hρ μ f := by
  have key := smInt_comp μ (((thetaU ψ ⟨u, hu⟩ : ℂˣ) : ℂ) • LinearMap.id : W →ₗ[ℂ] W) (fun x => x * ⟨u, hu⟩)
    (phi ψ f.1) (measurePreserving_mul_right' μ _) (isLocallyConstant_phi hψ _) (hasCompactSupport_phi ψ hρ _ f.2)
  show smInt μ (phi ψ f'.1) = _
  rw [phi_right ψ f.1 f'.1 ⟨u, hu⟩ hf, key]
  rfl

theorem deltaHalf_unipM (m : unipM k d) : deltaHalf k (fun a => Fin (d a)) m.1 = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [det_eq_one_of_mem_unipRad k (e := points (Fin (d a))) (m.2 a (Set.mem_univ a)), map_one]

theorem thetaU_conjU (ψ : AddChar k Circle) (n : GL (Fin N) k) (hn : n ∈ unipB k (Fin N)) (x : unipU k d hd) :
    thetaU ψ (conjU n hn x) = thetaU ψ x := by
  have e : Subgroup.inclusion (unipU_le (k := k) (d := d) (hd := hd)) (conjU n hn x) =
      (⟨n, hn⟩ : unipB k (Fin N)) * Subgroup.inclusion unipU_le x * (⟨n, hn⟩ : unipB k (Fin N))⁻¹ := rfl
  show whitChar ψ N (Subgroup.inclusion _ _) = whitChar ψ N (Subgroup.inclusion _ _)
  rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]

theorem phi_levi (ψ : AddChar k Circle) (f f' : IndSp (stdBlocks d hd) ρ) (a : GL (Fin N) k)
    (ha : a ∈ unipL k d hd) (m : unipM k d)
    (hm : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1)
    (hf' : f' = parInd (stdBlocks d hd) ρ a f) :
    phi ψ f' = fun x => ρ m.1 (phi ψ f (conjU a⁻¹ (inv_mem (unipL_le ha)) x)) := by
  subst hf'
  funext x
  have e1 : pm k (wOpen d hd) * x.1 * a = leviEmb k (stdBlocks d hd) m.1 *
      (pm k (wOpen d hd) * (conjU (d := d) (hd := hd) a⁻¹ (inv_mem (unipL_le ha)) x).1) := by
    rw [← hm]
    show _ = pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ * (pm k (wOpen d hd) * (a⁻¹ * x.1 * a⁻¹⁻¹))
    group
  have e2 := parInd_law (stdBlocks d hd) ρ f
    ⟨leviEmb k (stdBlocks d hd) m.1, leviEmb_mem_parab k (stdBlocks d hd) m.1⟩
    (pm k (wOpen d hd) * (conjU (d := d) (hd := hd) a⁻¹ (inv_mem (unipL_le ha)) x).1)
  rw [leviProj_leviEmb, deltaHalf_unipM m, Units.val_one, one_smul] at e2
  show (((thetaU ψ x)⁻¹ : ℂˣ) : ℂ) • (parInd (stdBlocks d hd) ρ a f).1.1 (pm k (wOpen d hd) * x.1) =
    ρ m.1 ((((thetaU ψ (conjU a⁻¹ (inv_mem (unipL_le ha)) x))⁻¹ : ℂˣ) : ℂ) •
      f.1.1 (pm k (wOpen d hd) * (conjU (d := d) (hd := hd) a⁻¹ (inv_mem (unipL_le ha)) x).1))
  rw [parInd_apply, e1, thetaU_conjU, map_smul]
  exact congrArg _ e2

theorem radInt_levi {ψ : AddChar k Circle} (hψ : Continuous ψ) (hρ : IsSmooth ρ) (μ : Measure (unipU k d hd))
    [μ.IsHaarMeasure] (a : GL (Fin N) k) (ha : a ∈ unipL k d hd) (m : unipM k d)
    (hm : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1)
    (f f' : openFns d hd ρ) (hf : (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ a f) :
    radInt hψ hρ μ f' = ρ m.1 (radInt hψ hρ μ f) := by
  have key := smInt_comp μ (ρ m.1) (conjU a⁻¹ (inv_mem (unipL_le ha))) (phi ψ f.1)
    (measurePreserving_conjU μ _ _) (isLocallyConstant_phi hψ _) (hasCompactSupport_phi ψ hρ _ f.2)
  show smInt μ (phi ψ f'.1) = _
  rw [phi_levi ψ f.1 f'.1 a ha m hm hf, key]
  rfl

def volU (μ : Measure (unipU k d hd)) (L₀ : Subgroup (GL (Fin N) k)) : ℝ :=
  (μ (Subtype.val ⁻¹' (L₀ : Set (GL (Fin N) k)))).toReal

theorem radInt_indicator {ψ : AddChar k Circle} (hψ : Continuous ψ) (hρ : IsSmooth ρ) (μ : Measure (unipU k d hd))
    [μ.IsHaarMeasure] (L₀ : Subgroup (GL (Fin N) k)) (hLU : L₀ ≤ unipU k d hd) (hLc : IsCompact (L₀ : Set (GL (Fin N) k)))
    (hLo : ∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) :
    0 < volU μ L₀ ∧ ∀ (f : openFns d hd ρ) (v : W),
      (∀ (u : GL (Fin N) k) (hb : u ∈ unipB k (Fin N)), u ∈ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = (whitChar ψ N ⟨u, hb⟩ : ℂ) • v) →
      (∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = 0) → radInt hψ hρ μ f = (volU μ L₀ : ℂ) • v := by
  set A : Set (unipU k d hd) := Subtype.val ⁻¹' (L₀ : Set (GL (Fin N) k)) with hA
  have hAc : IsCompact A :=
    (isClosed_unipU (k := k) (d := d) (hd := hd)).isClosedEmbedding_subtypeVal.isCompact_preimage hLc
  have hAo : IsOpen A := by
    obtain ⟨O, hO, e⟩ := hLo
    have : A = Subtype.val ⁻¹' O := by
      ext x
      simp only [hA, Set.mem_preimage, SetLike.mem_coe, ← e, Set.mem_inter_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
    rw [this]
    exact hO.preimage continuous_subtype_val
  refine ⟨?_, fun f v h1 h2 => ?_⟩
  · have hne : A.Nonempty := ⟨1, one_mem L₀⟩
    exact ENNReal.toReal_pos (hAo.measure_pos μ hne).ne' hAc.measure_lt_top.ne
  · have e : phi ψ f.1 = A.indicator fun _ => v := by
      funext x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]
        show (((thetaU ψ x)⁻¹ : ℂˣ) : ℂ) • f.1.1.1 (pm k (wOpen d hd) * x.1) = v
        rw [h1 x.1 (unipU_le x.2) hx, smul_smul]
        have : (((thetaU ψ x)⁻¹ : ℂˣ) : ℂ) * ((thetaU ψ x : ℂˣ) : ℂ) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        exact (congrArg (· • v) this).trans (one_smul _ _)
      · rw [Set.indicator_of_notMem hx]
        show (((thetaU ψ x)⁻¹ : ℂˣ) : ℂ) • f.1.1.1 (pm k (wOpen d hd) * x.1) = 0
        rw [h2 x.1 x.2 hx, smul_zero]
    show smInt μ (phi ψ f.1) = _
    rw [e]
    exact (GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_properties (W := W) (W' := W) μ).2.2.2 A v hAc hAo hAc.isClosed

end GlobalTheory.CompanionTheory.Rodier.RadInt

theorem GlobalTheory.CompanionTheory.Rodier.radical_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∃ (J : openFns d hd ρ →ₗ[ℂ] W) (vol : Subgroup (GL (Fin N) k) → ℝ), (∀ (u : GL (Fin N) k) (hu : u ∈ unipU k d hd) (hb : u ∈ unipB k (Fin N)) (f f' : openFns d hd ρ), (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ u f → J f' = (whitChar ψ N ⟨u, hb⟩ : ℂ) • J f) ∧ (∀ (a : GL (Fin N) k) (ha : a ∈ unipL k d hd) (m : unipM k d), pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 → ∀ f f' : openFns d hd ρ, (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ a f → J f' = ρ m.1 (J f)) ∧ ∀ L₀ : Subgroup (GL (Fin N) k), L₀ ≤ unipU k d hd → IsCompact (L₀ : Set (GL (Fin N) k)) → (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) → 0 < vol L₀ ∧ ∀ (f : openFns d hd ρ) (v : W), (∀ (u : GL (Fin N) k) (hb : u ∈ unipB k (Fin N)), u ∈ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = (whitChar ψ N ⟨u, hb⟩ : ℂ) • v) → (∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = 0) → J f = (vol L₀ : ℂ) • v := by
  intro k _ _ _ _ ψ hψ h N d hd W _ _ ρ hρ
  letI : MeasurableSpace (unipU k d hd) := borel _
  haveI : BorelSpace (unipU k d hd) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unipU k d hd) :=
    (RadInt.isClosed_unipU (k := k) (d := d) (hd := hd)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μ : MeasureTheory.Measure (unipU k d hd) := MeasureTheory.Measure.haar
  exact ⟨RadInt.radInt hψ hρ μ, RadInt.volU μ,
    fun u hu hb f f' hf => RadInt.radInt_right hψ hρ μ u hu hb f f' hf,
    fun a ha m hm f f' hf => RadInt.radInt_levi hψ hρ μ a ha m hm f f' hf,
    fun L₀ h1 h2 h3 => RadInt.radInt_indicator hψ hρ μ L₀ h1 h2 h3⟩
end
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_cell_jacquet_integral_volume : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∃ (J : openFns d hd ρ →ₗ[ℂ] W) (vol : Subgroup (GL (Fin N) k) → ℝ), (∀ (u : GL (Fin N) k) (hu : u ∈ unipU k d hd) (hb : u ∈ unipB k (Fin N)) (f f' : openFns d hd ρ), (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ u f → J f' = (whitChar ψ N ⟨u, hb⟩ : ℂ) • J f) ∧ (∀ (a : GL (Fin N) k) (ha : a ∈ unipL k d hd) (m : unipM k d), pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 → ∀ f f' : openFns d hd ρ, (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ a f → J f' = ρ m.1 (J f)) ∧ ∀ L₀ : Subgroup (GL (Fin N) k), L₀ ≤ unipU k d hd → IsCompact (L₀ : Set (GL (Fin N) k)) → (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) → 0 < vol L₀ ∧ ∀ (f : openFns d hd ρ) (v : W), (∀ (u : GL (Fin N) k) (hb : u ∈ unipB k (Fin N)), u ∈ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = (whitChar ψ N ⟨u, hb⟩ : ℂ) • v) → (∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = 0) → J f = (vol L₀ : ℂ) • v := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Rodier.radical_integral
end

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.OpenCoinv

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W)

theorem translate_mem {n : GL (Fin N) k} (hn : n ∈ unipB k (Fin N)) {g : IndSp (stdBlocks d hd) ρ}
    (hg : g ∈ openFns d hd ρ) : parInd (stdBlocks d hd) ρ n g ∈ openFns d hd ρ := by
  intro x hx
  obtain ⟨p, hp, n', hn', e⟩ := hg (x * n) hx
  refine ⟨p, hp, n' * n⁻¹, mul_mem hn' (inv_mem hn), ?_⟩
  rw [← mul_assoc, ← e]
  group

theorem span_mem (J : openFns d hd ρ →ₗ[ℂ] W) (S : Submodule ℂ W) (X : Set (IndSp (stdBlocks d hd) ρ))
    (hX : ∀ x ∈ X, ∃ hx : x ∈ openFns d hd ρ, J ⟨x, hx⟩ ∈ S) {f : IndSp (stdBlocks d hd) ρ}
    (hf : f ∈ Submodule.span ℂ X) : ∃ hx : f ∈ openFns d hd ρ, J ⟨f, hx⟩ ∈ S := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hX x hx
  | zero =>
    refine ⟨zero_mem _, ?_⟩
    have e : J ⟨0, zero_mem _⟩ = 0 := map_zero J
    rw [e]
    exact S.zero_mem
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨add_mem a b, ?_⟩
    have e : J ⟨x + y, add_mem a b⟩ = J ⟨x, a⟩ + J ⟨y, b⟩ := (map_add J ⟨x, a⟩ ⟨y, b⟩)
    rw [e]
    exact add_mem ha hb
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨Submodule.smul_mem _ c a, ?_⟩
    have e : J ⟨c • x, Submodule.smul_mem _ c a⟩ = c • J ⟨x, a⟩ := (map_smul J c ⟨x, a⟩)
    rw [e]
    exact S.smul_mem c ha

theorem leviEmb_inj {x y : Levi k fun a => Fin (d a)}
    (e : leviEmb k (stdBlocks d hd) x = leviEmb k (stdBlocks d hd) y) : x = y := by
  rw [← leviProj_leviEmb k (stdBlocks d hd) x, ← leviProj_leviEmb k (stdBlocks d hd) y]
  exact congrArg _ (Subtype.ext e)

end SlopeTestRemainingChoices

end GlobalTheory.CompanionTheory.Rodier.OpenCoinv

namespace GlobalTheory.CompanionTheory.Rodier.OpenCoinv

set_option maxHeartbeats 2000000 in

theorem openFns_whittaker : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∃ J : openFns d hd ρ →ₗ[ℂ] W, Function.Surjective J ∧ ∀ f : openFns d hd ρ, J f ∈ twKer ρ (unipM k d) (whitM d ψ) ↔ (f : IndSp (stdBlocks d hd) ρ) ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) := by
  intro k _ _ _ _ ψ hψ h N d hd W _ _ ρ hρ
  obtain ⟨J, vol, hU, hL, hV⟩ := GlobalTheory.T.open_cell_jacquet_integral_volume k ψ hψ h N d hd ρ hρ
  obtain ⟨hfac, -⟩ := GlobalTheory.T.unipotent_radical_decomposition_normal k h N d hd
  obtain ⟨hl1, hl2⟩ := GlobalTheory.T.open_cell_levi_unipotent_conjugation k ψ h N d hd
  obtain ⟨-, huniq, -⟩ := GlobalTheory.T.open_cell_unipotent_uniqueness_closed k h N d hd
  have hUB : unipU k d hd ≤ unipB k (Fin N) := inf_le_left
  have hLB : unipL k d hd ≤ unipB k (Fin N) := inf_le_left
  have surj : Function.Surjective J := by
    intro v
    obtain ⟨L₀, hL₀U, hc, hO, hθ, f, hf, h1, h2⟩ := GlobalTheory.T.exists_bump_section_on_compact_unipotent k ψ hψ h N d hd ρ hρ v
    obtain ⟨hpos, hJ⟩ := hV L₀ hL₀U hc hO
    have e := hJ ⟨f, hf⟩ v (fun u hb hu => by
      show f.1.1 (pm k (wOpen d hd) * u) = _
      rw [h1 u hu, hθ u hb hu]
      simp) h2
    refine ⟨((vol L₀ : ℂ))⁻¹ • ⟨f, hf⟩, ?_⟩
    have hne : (vol L₀ : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [map_smul, e, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have gen : ∀ (n : GL (Fin N) k) (hn : n ∈ unipB k (Fin N)) (g : openFns d hd ρ),
      ∃ hx : parInd (stdBlocks d hd) ρ n g.1 - ((whitChar ψ N ⟨n, hn⟩ : ℂˣ) : ℂ) • g.1 ∈ openFns d hd ρ,
        J ⟨_, hx⟩ ∈ twKer ρ (unipM k d) (whitM d ψ) := by
    intro n hn g
    obtain ⟨a, ha, u, hu, rfl⟩ := hfac n hn
    have hub := hUB hu
    have hab := hLB ha
    obtain ⟨m, hm, hθm⟩ := hl1 a ha hab
    let g1 : openFns d hd ρ := ⟨parInd (stdBlocks d hd) ρ u g.1, translate_mem d hd ρ hub g.2⟩
    let g2 : openFns d hd ρ := ⟨parInd (stdBlocks d hd) ρ a g1.1, translate_mem d hd ρ hab g1.2⟩
    have e1 : J g1 = ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ) • J g := hU u hu hub g g1 rfl
    have e2 : J g2 = ρ m.1 (J g1) := hL a ha m hm g1 g2 rfl
    have e3 : parInd (stdBlocks d hd) ρ (a * u) g.1 = g2.1 := by
      rw [map_mul]
      rfl
    have hθ : whitChar ψ N ⟨a * u, hn⟩ = whitChar ψ N ⟨a, hab⟩ * whitChar ψ N ⟨u, hub⟩ := by
      rw [← map_mul]
      rfl
    have hx : parInd (stdBlocks d hd) ρ (a * u) g.1 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g.1 ∈ openFns d hd ρ :=
      sub_mem (translate_mem d hd ρ hn g.2) (Submodule.smul_mem _ _ g.2)
    refine ⟨hx, ?_⟩
    have e4 : (⟨_, hx⟩ : openFns d hd ρ) = g2 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g :=
      Subtype.ext (by
        show parInd (stdBlocks d hd) ρ (a * u) g.1 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g.1 =
          g2.1 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g.1
        rw [e3])
    rw [e4, map_sub, map_smul, e2, e1, map_smul, hθ, hθm, Units.val_mul]
    have e5 : ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ) • ρ m.1 (J g) -
        (((whitM d ψ m : ℂˣ) : ℂ) * ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ)) • J g =
        ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ) • (ρ m.1 (J g) - ((whitM d ψ m : ℂˣ) : ℂ) • J g) := by
      rw [smul_sub, smul_smul, mul_comm]
    rw [e5]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, J g, rfl⟩)
  have bwd : ∀ f : openFns d hd ρ, f.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) →
      J f ∈ twKer ρ (unipM k d) (whitM d ψ) := by
    intro f hf
    have hs := GlobalTheory.T.compact_unipotent_subgroup_finite_generation k ψ hψ h N d hd ρ (unipB k (Fin N)) le_rfl
      (fun s hs => GlobalTheory.CompanionTheory.UnipExhaust.exists_compact_subgroup_of_finset k N s hs) (whitChar ψ N)
      (fun q hq => rfl) f.1 f.2 hf
    obtain ⟨_, h2⟩ := span_mem d hd ρ J (twKer ρ (unipM k d) (whitM d ψ)) _ (by
      rintro _ ⟨q, g, hg, rfl⟩
      exact gen q.1 q.2 ⟨g, hg⟩) hs
    exact h2
  have key : ∀ f : openFns d hd ρ, J f = 0 →
      f.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) := by
    intro f hf
    obtain ⟨L, hLU, hLc, hLO, hsupp⟩ := GlobalTheory.T.open_cell_function_compact_support_unipotent k h N d hd ρ hρ f.1 f.2
    have hLB' : L ≤ unipB k (Fin N) := hLU.trans hUB
    let θL : L →* ℂˣ := (whitChar ψ N).comp (Subgroup.inclusion hLB')
    have hopen : IsOpen (θL.ker : Set L) :=
      (GlobalTheory.Whittaker.isSmoothChar_whitChar (N := N) hψ).preimage (f := Subgroup.inclusion hLB') (continuous_subtype_val.subtype_mk fun x => hLB' x.2)
    obtain ⟨f', hd1, hd2, hd3⟩ := GlobalTheory.T.projection_to_twisted_eigenfunction_support _ _ L hLc θL hopen f.1
    have hsupp' : ∀ g, f'.1.1 g ≠ 0 → ∃ p ∈ parab k (stdBlocks d hd), ∃ u ∈ L, g = p * pm k (wOpen d hd) * u := by
      intro g hg
      obtain ⟨l, hl, hne⟩ := hd2 g hg
      obtain ⟨p, hp, u, hu, e⟩ := hsupp _ hne
      refine ⟨p, hp, u * l⁻¹, mul_mem hu (inv_mem hl), ?_⟩
      rw [← mul_assoc, ← e]
      group
    have hf'o : f' ∈ openFns d hd ρ := fun g hg => by
      obtain ⟨p, hp, u, hu, e⟩ := hsupp' g hg
      exact ⟨p, hp, u, hLB' hu, e⟩
    have hdiff := GlobalTheory.T.compact_unipotent_subgroup_finite_generation k ψ hψ h N d hd ρ L hLB' (fun s hs => ⟨L, le_rfl, hs, hLc⟩) θL
      (fun q hq => rfl) (f.1 - f') (sub_mem f.2 hf'o) hd1
    obtain ⟨hx, hJ0⟩ := span_mem d hd ρ J ⊥ _ (by
      rintro _ ⟨q, g, hg, rfl⟩
      have hqb := hLB' q.2
      have hx : parInd (stdBlocks d hd) ρ q.1 g - ((θL q : ℂˣ) : ℂ) • g ∈ openFns d hd ρ :=
        sub_mem (translate_mem d hd ρ hqb hg) (Submodule.smul_mem _ _ hg)
      refine ⟨hx, ?_⟩
      let g1 : openFns d hd ρ := ⟨parInd (stdBlocks d hd) ρ q.1 g, translate_mem d hd ρ hqb hg⟩
      have e1 : J g1 = ((whitChar ψ N ⟨q.1, hqb⟩ : ℂˣ) : ℂ) • J ⟨g, hg⟩ := hU q.1 (hLU q.2) hqb ⟨g, hg⟩ g1 rfl
      have e2 : (⟨_, hx⟩ : openFns d hd ρ) = g1 - ((θL q : ℂˣ) : ℂ) • ⟨g, hg⟩ := rfl
      rw [e2, map_sub, map_smul, e1]
      exact (sub_self _ : _ = (0 : W))) hdiff
    let F' : openFns d hd ρ := ⟨f', hf'o⟩
    have hJF : J F' = 0 := by
      have e : (⟨_, hx⟩ : openFns d hd ρ) = f - F' := rfl
      rw [e, map_sub, hf] at hJ0
      simpa using hJ0
    obtain ⟨hpos, hJ⟩ := hV L hLU hLc hLO
    have hv := hJ F' (f'.1.1 (pm k (wOpen d hd))) (fun u hb hu => hd3 ⟨u, hu⟩ _) (fun u hu hnot => by
      by_contra hne
      obtain ⟨p, hp, l, hl, e⟩ := hsupp' _ hne
      exact hnot (huniq p hp l (hLU hl) u hu e.symm ▸ hl))
    have hne : (vol L : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hv0 : f'.1.1 (pm k (wOpen d hd)) = 0 := by
      rw [hJF] at hv
      exact (smul_eq_zero.1 hv.symm).resolve_left hne
    have hf0 : f' = 0 := by
      refine Subtype.ext (Subtype.ext (funext fun g => ?_))
      by_contra hg
      obtain ⟨p, hp, l, hl, e⟩ := hsupp' g hg
      apply hg
      have h1 := f'.1.2 ⟨p, hp⟩ (pm k (wOpen d hd))
      rw [hv0, map_zero] at h1
      rw [e]
      have h2 := hd3 ⟨l, hl⟩ (p * pm k (wOpen d hd))
      rw [show f'.1.1 (p * pm k (wOpen d hd)) = 0 from h1, smul_zero] at h2
      exact h2
    rw [hf0, sub_zero] at hd1
    refine (Submodule.span_le.2 ?_ : twKer (parInd (stdBlocks d hd) ρ) L θL ≤ _) hd1
    rintro _ ⟨n, v, rfl⟩
    exact Submodule.subset_span ⟨⟨n.1, hLB' n.2⟩, v, rfl⟩
  have lift : ∀ s ∈ twKer ρ (unipM k d) (whitM d ψ), ∃ F : openFns d hd ρ,
      F.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) ∧ J F = s := by
    intro s hs
    refine Submodule.span_induction (p := fun s _ => ∃ F : openFns d hd ρ,
      F.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) ∧ J F = s) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨m, v, rfl⟩
      obtain ⟨g, rfl⟩ := surj v
      obtain ⟨a, ha, hm⟩ := hl2 m
      have hab := hLB ha
      obtain ⟨m', hm', hθ⟩ := hl1 a ha hab
      have hmm : m = m' := Subtype.ext (leviEmb_inj d hd (hm.symm.trans hm'))
      subst hmm
      let g1 : openFns d hd ρ := ⟨parInd (stdBlocks d hd) ρ a g.1, translate_mem d hd ρ hab g.2⟩
      refine ⟨g1 - ((whitChar ψ N ⟨a, hab⟩ : ℂˣ) : ℂ) • g, Submodule.subset_span ⟨⟨a, hab⟩, g.1, rfl⟩, ?_⟩
      rw [map_sub, map_smul, hL a ha m hm g g1 rfl, hθ]
    · exact ⟨0, zero_mem _, map_zero J⟩
    · rintro x y _ _ ⟨F, hF, rfl⟩ ⟨F', hF', rfl⟩
      exact ⟨F + F', add_mem hF hF', map_add J F F'⟩
    · rintro c x _ ⟨F, hF, rfl⟩
      exact ⟨c • F, Submodule.smul_mem _ c hF, map_smul J c F⟩
  refine ⟨J, surj, fun f => ⟨fun hf => ?_, bwd f⟩⟩
  obtain ⟨F, hF, e⟩ := lift _ hf
  have h0 := key (f - F) (by rw [map_sub, e, sub_self])
  have h1 : (f : IndSp (stdBlocks d hd) ρ) = (f - F).1 + F.1 := by
    show (f : IndSp (stdBlocks d hd) ρ) = (f.1 - F.1) + F.1
    rw [sub_add_cancel]
  rw [h1]
  exact add_mem h0 hF

end GlobalTheory.CompanionTheory.Rodier.OpenCoinv
end
