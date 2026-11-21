import Mathlib
import Development.AutomorphicSpectrum.Definitions.JetCones.SymCapRev
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.RealPlaceAnalysis.FinalF

section
open GlobalTheory.CompanionTheory.AlgRepEndIrreducible PI.UpqRep Matrix
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.AlgRepEndIrreducible.Vev

private noncomputable def ev {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (D : Fin n → Fin n → Module.End ℂ V) (v : V) (l : List (Fin n × Fin n)) : ℂ :=
  ⟪v, (l.map fun x => D x.1 x.2).prod v⟫_ℂ

private theorem ev_swap {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {D : Fin n → Fin n → Module.End ℂ V} (h : KRel ε D) (v : V)
    (l₁ l₂ : List (Fin n × Fin n)) (x y : Fin n × Fin n) (hx : ε x.1 = ε x.2) (hy : ε y.1 = ε y.2) :
    ev D v (l₁ ++ x :: y :: l₂) = ev D v ((l₁ ++ [y]) ++ x :: l₂)
      + (if x.2 = y.1 then ev D v (l₁ ++ (x.1, y.2) :: l₂) else 0)
      - (if y.2 = x.1 then ev D v (l₁ ++ (y.1, x.2) :: l₂) else 0) := by
  have h1 := h x.1 x.2 y.1 y.2 hx hy
  have h2 : D x.1 x.2 * D y.1 y.2 = D y.1 y.2 * D x.1 x.2 + (if x.2 = y.1 then D x.1 y.2 else 0)
      - (if y.2 = x.1 then D y.1 x.2 else 0) := by
    rw [add_sub_assoc, ← h1]; abel
  simp only [ev, List.map_append, List.map_cons, List.prod_append, List.prod_cons, List.map_nil,
    List.prod_nil, mul_one]
  rw [← mul_assoc (D x.1 x.2), h2]
  split_ifs <;>
    simp [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, inner_add_right, inner_sub_right]

private theorem ev_last {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {D : Fin n → Fin n → Module.End ℂ V} {μ : Fin n → ℝ} {v : V}
    (h : Formalism.REAL.KHighest ε D μ v)
    (l₁ : List (Fin n × Fin n)) (x : Fin n × Fin n) (hx : ε x.1 = ε x.2) (hle : x.1 ≤ x.2) :
    ev D v (l₁ ++ [x]) = (if x.1 = x.2 then (μ x.1 : ℂ) else 0) * ev D v l₁ := by
  simp only [ev, List.map_append, List.map_cons, List.prod_append, List.prod_cons, List.map_nil,
    List.prod_nil, mul_one, Module.End.mul_apply]
  split_ifs with he
  · rw [← he, h.1 x.1, map_smul, inner_smul_right]
  · rw [h.2 x.1 x.2 (lt_of_le_of_ne hle he) hx]; simp

private theorem ev_first {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {D : Fin n → Fin n → Module.End ℂ V} {μ : Fin n → ℝ} {v : V}
    (ha : KAdj ε D) (h : Formalism.REAL.KHighest ε D μ v)
    (l : List (Fin n × Fin n)) (x : Fin n × Fin n) (hx : ε x.1 = ε x.2) (hlt : x.2 < x.1) :
    ev D v (x :: l) = 0 := by
  simp only [ev, List.map_cons, List.prod_cons, Module.End.mul_apply]
  rw [← ha x.2 x.1 hx.symm, h.2 x.2 x.1 hlt hx.symm, inner_zero_left]

theorem vev_eq : ∀ (n : ℕ) (ε : Fin n → Bool) (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (D : Fin n → Fin n → Module.End ℂ V) (D' : Fin n → Fin n → Module.End ℂ V') (μ : Fin n → ℝ) (v : V) (v' : V'), KRel ε D → KRel ε D' → KAdj ε D → KAdj ε D' → Formalism.REAL.KHighest ε D μ v → Formalism.REAL.KHighest ε D' μ v' → ∀ l : List (Fin n × Fin n), (∀ x ∈ l, ε x.1 = ε x.2) → ⟪v, (l.map fun x => D x.1 x.2).prod v⟫_ℂ * ⟪v', v'⟫_ℂ = ⟪v', (l.map fun x => D' x.1 x.2).prod v'⟫_ℂ * ⟪v, v⟫_ℂ := by
  intro n ε V V' _ _ _ _ D D' μ v v' hR hR' hA hA' hH hH'
  suffices H : ∀ (N : ℕ) (l : List (Fin n × Fin n)), l.length = N → (∀ x ∈ l, ε x.1 = ε x.2) →
      ev D v l * ⟪v', v'⟫_ℂ = ev D' v' l * ⟪v, v⟫_ℂ from fun l hl => H _ l rfl hl
  intro N
  induction N with
  | zero =>
    intro l hl _
    obtain rfl := List.length_eq_zero_iff.mp hl
    simp only [ev, List.map_nil, List.prod_nil, Module.End.one_apply]
    ring
  | succ N ih =>
    have key : ∀ (x : Fin n × Fin n), ε x.1 = ε x.2 → x.1 ≤ x.2 → ∀ (l₂ l₁ : List (Fin n × Fin n)),
        l₁.length + l₂.length = N → (∀ z ∈ l₁, ε z.1 = ε z.2) → (∀ z ∈ l₂, ε z.1 = ε z.2) →
        ev D v (l₁ ++ x :: l₂) * ⟪v', v'⟫_ℂ = ev D' v' (l₁ ++ x :: l₂) * ⟪v, v⟫_ℂ := by
      intro x hx hle l₂
      induction l₂ with
      | nil =>
        intro l₁ hl h₁ _
        rw [ev_last hH l₁ x hx hle, ev_last hH' l₁ x hx hle, mul_assoc, mul_assoc,
          ih l₁ (by simpa using hl) h₁]
      | cons y l₂ ih₂ =>
        intro l₁ hl h₁ h₂
        have hy : ε y.1 = ε y.2 := h₂ y (by simp)
        have h₂' : ∀ z ∈ l₂, ε z.1 = ε z.2 := fun z hz => h₂ z (by simp [hz])
        have hs : ∀ w : Fin n × Fin n, ε w.1 = ε w.2 →
            ev D v (l₁ ++ w :: l₂) * ⟪v', v'⟫_ℂ = ev D' v' (l₁ ++ w :: l₂) * ⟪v, v⟫_ℂ := by
          intro w hw
          refine ih _ (by simpa using hl) ?_
          intro z hz
          simp only [List.mem_append, List.mem_cons] at hz
          rcases hz with hz | rfl | hz
          exacts [h₁ z hz, hw, h₂' z hz]
        have hm := ih₂ (l₁ ++ [y]) (by simp at hl ⊢; omega) (by
          intro z hz
          simp only [List.mem_append, List.mem_singleton] at hz
          rcases hz with hz | rfl
          exacts [h₁ z hz, hy]) h₂'
        rw [ev_swap hR v l₁ l₂ x y hx hy, ev_swap hR' v' l₁ l₂ x y hx hy]
        simp only [sub_mul, add_mul, hm, ite_mul, zero_mul]
        congr 1
        · congr 1
          split_ifs with e
          · exact hs _ (by simp only; rw [hx, e, hy])
          · rfl
        · split_ifs with e
          · exact hs _ (by simp only; rw [hy, e, hx])
          · rfl
    intro l hl hc
    cases l with
    | nil => simp at hl
    | cons x l =>
      have hx : ε x.1 = ε x.2 := hc x (by simp)
      rcases le_or_gt x.1 x.2 with hle | hlt
      · exact key x hx hle l [] (by simpa using hl) (by simp) (fun z hz => hc z (by simp [hz]))
      · rw [ev_first hA hH l x hx hlt, ev_first hA' hH' l x hx hlt]; simp

end GlobalTheory.CompanionTheory.AlgRepEndIrreducible.Vev
end

section
open GlobalTheory.CompanionTheory.AlgRepEndIrreducible PI.UpqRep Matrix
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.AlgRepEndIrreducible.HwMap

theorem word_adj {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {D : Fin n → Fin n → Module.End ℂ V} (h : KAdj ε D) (l : List (Fin n × Fin n))
    (hl : ∀ x ∈ l, ε x.1 = ε x.2) (x y : V) :
    ⟪(l.map fun x => D x.1 x.2).prod x, y⟫_ℂ =
      ⟪x, (((l.map Prod.swap).reverse).map fun x => D x.1 x.2).prod y⟫_ℂ := by
  induction l generalizing y with
  | nil => simp
  | cons a l ih =>
    have ha := hl a (by simp)
    have ih' := ih (fun x hx => hl x (by simp [hx])) (D a.2 a.1 y)
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.reverse_cons,
      List.map_append, List.prod_append, List.map_nil, List.prod_nil, mul_one, Prod.fst_swap,
      Prod.snd_swap]
    rw [h _ _ ha, ih']

theorem graph_extend {n : ℕ} {ε : Fin n → Bool} {V V' : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
    {D : Fin n → Fin n → Module.End ℂ V} {D' : Fin n → Fin n → Module.End ℂ V'} (h : KAdj ε D)
    (G : Submodule ℂ (V × V')) (hG : ∀ g ∈ G, g.1 = 0 → g.2 = 0)
    (hst : ∀ a b, ε a = ε b → ∀ g ∈ G, (D a b g.1, D' a b g.2) ∈ G) :
    ∃ T : V →ₗ[ℂ] V', (∀ g ∈ G, T g.1 = g.2) ∧ KMap ε D D' T := by
  let A : G →ₗ[ℂ] V := (LinearMap.fst ℂ V V').comp G.subtype
  have hA : Function.Injective A := by
    rw [injective_iff_map_eq_zero]
    intro g hg
    have h1 : g.1.1 = 0 := hg
    exact Subtype.ext (Prod.ext h1 (hG _ g.2 h1))
  let U : Submodule ℂ V := LinearMap.range A
  let e : G ≃ₗ[ℂ] U := LinearEquiv.ofInjective A hA
  let T : V →ₗ[ℂ] V' := ((LinearMap.snd ℂ V V').comp G.subtype).comp
    (e.symm.toLinearMap.comp (U.orthogonalProjectionOnto : V →ₗ[ℂ] U))
  have key : ∀ g ∈ G, ∀ z ∈ Uᗮ, T (g.1 + z) = g.2 := by
    intro g hg z hz
    have h1 : U.orthogonalProjectionOnto (g.1 + z) = e ⟨g, hg⟩ := by
      rw [map_add, Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hz, add_zero]
      exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (e ⟨g, hg⟩)
    show ((e.symm (U.orthogonalProjectionOnto (g.1 + z)) : G) : V × V').2 = g.2
    rw [h1, e.symm_apply_apply]
  refine ⟨T, fun g hg => by simpa using key g hg 0 (zero_mem _), ?_⟩
  intro a b hab w
  obtain ⟨u, hu, z, hz, rfl⟩ := U.exists_add_mem_mem_orthogonal w
  obtain ⟨g, rfl⟩ := hu
  have hz' : D a b z ∈ Uᗮ := by
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨g', rfl⟩
    rw [← h b a hab.symm]
    exact (Submodule.mem_orthogonal _ _).1 hz _ ⟨⟨_, hst b a hab.symm _ g'.2⟩, rfl⟩
  have h1 := key _ (hst a b hab _ g.2) _ hz'
  have h2 := key _ g.2 _ hz
  have h3 : A g = g.1.1 := rfl
  rw [h3, h2, map_add]
  exact h1

theorem hwmap : ∀ (n : ℕ) (ε : Fin n → Bool) (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (D : Fin n → Fin n → Module.End ℂ V) (D' : Fin n → Fin n → Module.End ℂ V') (μ : Fin n → ℝ) (v : V) (v' : V'), KRel ε D → KRel ε D' → KAdj ε D → KAdj ε D' → Formalism.REAL.KHighest ε D μ v → Formalism.REAL.KHighest ε D' μ v' → v ≠ 0 → ∃ T : V →ₗ[ℂ] V', T v = v' ∧ KMap ε D D' T := by
  intro n ε V V' _ _ _ _ _ D D' μ v v' hR hR' hA hA' hv hv' hv0
  have vev := GlobalTheory.CompanionTheory.AlgRepEndIrreducible.Vev.vev_eq n ε V V' D D' μ v v' hR hR' hA hA' hv hv'
  let S : Set (V × V') := {g | ∃ l : List (Fin n × Fin n), (∀ x ∈ l, ε x.1 = ε x.2) ∧
    g = ((l.map fun x => D x.1 x.2).prod v, (l.map fun x => D' x.1 x.2).prod v')}
  have hin : ∀ g ∈ Submodule.span ℂ S, ∀ g' ∈ Submodule.span ℂ S,
      ⟪g.1, g'.1⟫_ℂ * ⟪v', v'⟫_ℂ = ⟪g.2, g'.2⟫_ℂ * ⟪v, v⟫_ℂ := by
    intro g hg g' hg'
    induction hg using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => simp only [Prod.fst_add, Prod.snd_add, inner_add_left, add_mul, hx, hy]
    | smul c x _ hx => simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_left, mul_assoc, hx]
    | mem x hx =>
      induction hg' using Submodule.span_induction with
      | zero => simp
      | add x y _ _ hx hy =>
        simp only [Prod.fst_add, Prod.snd_add, inner_add_right, add_mul, hx, hy]
      | smul c x _ hx => simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_right, mul_assoc, hx]
      | mem y hy =>
        obtain ⟨l, hl, rfl⟩ := hx
        obtain ⟨l', hl', rfl⟩ := hy
        have := vev ((l.map Prod.swap).reverse ++ l') (by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hx)
            exact (hl y hy).symm
          · exact hl' x hx)
        simp only [List.map_append, List.prod_append, Module.End.mul_apply] at this
        dsimp only
        rw [word_adj hA l hl, word_adj hA' l hl, this]
  obtain ⟨T, hT, hK⟩ := graph_extend (D' := D') hA (Submodule.span ℂ S) (by
    intro g hg h0
    have := hin g hg g hg
    rw [h0, inner_zero_left, zero_mul] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact inner_self_eq_zero.1 h
    · exact absurd (inner_self_eq_zero.1 h) hv0) (by
    intro a b hab g hg
    induction hg using Submodule.span_induction with
    | zero =>
      simp only [Prod.fst_zero, Prod.snd_zero, map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      refine Submodule.subset_span ⟨(a, b) :: l, ?_, by simp⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hab
      · exact hl x hx)
  exact ⟨T, hT (v, v') (Submodule.subset_span ⟨[], by simp, by simp⟩), hK⟩

end GlobalTheory.CompanionTheory.AlgRepEndIrreducible.HwMap
end
