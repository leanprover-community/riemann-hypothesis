import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulTopIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsDualBound
import Lemmata.GeneralBFactLeftRest.Imports
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMulEqUnifPow
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulSpanIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RelIndexEqMapMulKer

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace RedC

theorem index_eq_card {G T : Type*} [Group G] (N : Subgroup G) (f : G → T) (hs : Function.Surjective f)
    (hf : ∀ a b, f a = f b ↔ a⁻¹ * b ∈ N) : N.index = Nat.card T := by
  first | exact Bl.general_b_fact_left_rest.goal1 .. | (apply Bl.general_b_fact_left_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_rest.goal1 <;> assumption)

def redEnd (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : V ≃ₗ[K] V) (hX : X ∈ glSub A) :
    Module.End (𝓞 K) (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)) :=
  Submodule.mapQ _ _ (((X : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict fun _ hx => apply_mem hX hx)
    (fun x hx => by
      rw [Submodule.mem_comap, Submodule.mem_smul_top_iff]
      rw [Submodule.mem_smul_top_iff] at hx
      exact apply_mem_smul hX _ hx)

theorem redEnd_mk (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : V ≃ₗ[K] V) (hX : X ∈ glSub A)
    (x : ↥A) : redEnd A 𝔭 k X hX (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨X x, apply_mem hX x.2⟩ := rfl

theorem mk_eq_redEnd_iff {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {k : ℕ} {X : V ≃ₗ[K] V}
    (hX : X ∈ glSub A) (x x' : ↥A) :
    Submodule.Quotient.mk x' = redEnd A 𝔭 k X hX (Submodule.Quotient.mk x) ↔
      (x' : V) - X x ∈ extP K 𝔭 ^ k • A := by
  rw [redEnd_mk, Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
  rfl

theorem redEnd_eq_iff {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a b : V ≃ₗ[K] V}
    (ha : a ∈ glSub A) (hb : b ∈ glSub A) :
    redEnd A 𝔭 k a ha = redEnd A 𝔭 k b hb ↔ a⁻¹ * b ∈ nSub A 𝔭 k := by
  have e : ∀ z : V, a⁻¹ (a z) = z := fun z => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  have e' : ∀ z : V, a (a⁻¹ z) = z := fun z => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  constructor
  · intro hab
    refine ⟨mul_mem (inv_mem ha) hb, fun x hx => ?_⟩
    have h1 : Submodule.Quotient.mk (⟨b x, apply_mem hb hx⟩ : ↥A) =
        redEnd A 𝔭 k a ha (Submodule.Quotient.mk ⟨x, hx⟩) := by
      rw [hab, redEnd_mk]
    have h2 := apply_mem_smul (inv_mem ha) _ ((mk_eq_redEnd_iff ha _ _).1 h1)
    simpa [e] using h2
  · rintro ⟨-, hab⟩
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    symm
    rw [redEnd_mk, mk_eq_redEnd_iff]
    have h2 := apply_mem_smul ha _ (hab x x.2)
    simpa [e'] using h2

theorem redEnd_cond (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {A₀ : Submodule (𝓞 K) V}
    (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {X : V ≃ₗ[K] V}
    (hX : X ∈ sSub h (locF 𝔭 A₀) 𝔭 k) (x y x' y' : ↥(locF 𝔭 A₀))
    (hx : Submodule.Quotient.mk x' = redEnd (locF 𝔭 A₀) 𝔭 k X hX.1 (Submodule.Quotient.mk x))
    (hy : Submodule.Quotient.mk y' = redEnd (locF 𝔭 A₀) 𝔭 k X hX.1 (Submodule.Quotient.mk y)) :
    CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V)) := by
  rw [congrP_algebraMap_iff_sub_mem h𝔭]
  rw [mk_eq_redEnd_iff] at hx hy
  have z : ∀ w ∈ locF 𝔭 A₀, w ∈ extP K 𝔭 ^ 0 • locF 𝔭 A₀ := fun w hw => by rwa [pow_zero_smul]
  have h1 := hX.2 x x.2 y y.2
  have h2 := form_mem_pK hF hA₀i h𝔭 hx (z _ y'.2)
  have h3 := form_mem_pK hF hA₀i h𝔭 (z _ (apply_mem hX.1 x.2)) hy
  rw [add_zero] at h2
  rw [zero_add] at h3
  have h4 := add_mem (add_mem h1 h2) h3
  have e : h (x' : V) (y' : V) - h (x : V) (y : V) =
      h (X x) (X y) - h (x : V) (y : V) + h ((x' : V) - X x) (y' : V) + h (X x) ((y' : V) - X y) := by
    simp only [map_sub, LinearMap.sub_apply]
    abel
  rw [e]
  exact h4

theorem mem_smul_of_smul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A : Submodule (𝓞 K) V) (k : ℕ)
    {t : 𝓞 F} (ht : t ∉ 𝔭) {v : V} (hv : v ∈ A)
    (h : algebraMap (𝓞 F) (𝓞 K) t • v ∈ extP K 𝔭 ^ k • A) : v ∈ extP K 𝔭 ^ k • A := by
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht k
  have : v = algebraMap (𝓞 F) (𝓞 K) u • (algebraMap (𝓞 F) (𝓞 K) t • v) -
      algebraMap (𝓞 F) (𝓞 K) (u * t - 1) • v := by
    rw [map_sub, map_mul, map_one, sub_smul, mul_smul, one_smul]; abel
  rw [this]
  exact sub_mem (Submodule.smul_mem _ _ h) (Submodule.smul_mem_smul (localizedQuotients.ι_mem_pow hu) hv)

theorem mem_locF_of_smul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A₀ : Submodule (𝓞 K) V)
    {t : 𝓞 F} (ht : t ∉ 𝔭) {v : V} (h : algebraMap (𝓞 F) (𝓞 K) t • v ∈ locF 𝔭 A₀) : v ∈ locF 𝔭 A₀ := by
  have := h𝔭.isPrime
  obtain ⟨s, hs, h1⟩ := (LocalSpans.mem_locF 𝔭 A₀ _).1 h
  refine (LocalSpans.mem_locF 𝔭 A₀ _).2 ⟨s * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hs ht, ?_⟩
  rwa [map_mul, mul_smul]

theorem exists_lift {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (Y : Module.End (𝓞 K) (↥(locF 𝔭 A₀) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 A₀)))) :
    ∃ D : V →ₗ[K] V, ∀ x : ↥(locF 𝔭 A₀), ∃ hD : D x ∈ locF 𝔭 A₀,
      Submodule.Quotient.mk (⟨D x, hD⟩ : ↥(locF 𝔭 A₀)) = Y (Submodule.Quotient.mk x) := by
  have := h𝔭.isPrime
  obtain ⟨b, -, hb⟩ := LocalSpans.exists_basis_locF hA₀ h𝔭
  have hsp : Submodule.span (𝓞 K) (Set.range b) ≤ locF 𝔭 A₀ := hb ▸ localizedQuotients.le_locF 𝔭 _
  have hbA : ∀ i, b i ∈ locF 𝔭 A₀ := fun i => hsp (Submodule.subset_span ⟨i, rfl⟩)
  choose c hc using fun i => Submodule.Quotient.mk_surjective _ (Y (Submodule.Quotient.mk ⟨b i, hbA i⟩))
  let D : V →ₗ[K] V := b.constr K fun i => (c i : V)
  have hDb : ∀ i, D (b i) = c i := fun i => b.constr_basis K _ i
  have key : ∀ y ∈ Submodule.span (𝓞 K) (Set.range b), ∃ (hy : y ∈ locF 𝔭 A₀) (hD : D y ∈ locF 𝔭 A₀),
      Submodule.Quotient.mk (⟨D y, hD⟩ : ↥(locF 𝔭 A₀)) = Y (Submodule.Quotient.mk ⟨y, hy⟩) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      refine ⟨hbA i, by rw [hDb]; exact (c i).2, ?_⟩
      rw [← hc i]
      congr 1
      exact Subtype.ext (hDb i)
    | zero =>
      refine ⟨zero_mem _, by rw [map_zero]; exact zero_mem _, ?_⟩
      have e1 : (⟨D 0, by rw [map_zero]; exact zero_mem _⟩ : ↥(locF 𝔭 A₀)) = 0 := Subtype.ext (map_zero D)
      have e2 : (⟨0, zero_mem _⟩ : ↥(locF 𝔭 A₀)) = 0 := rfl
      rw [e1, e2, Submodule.Quotient.mk_zero, map_zero]
    | add y z _ _ h1 h2 =>
      obtain ⟨hy, hDy, e1⟩ := h1
      obtain ⟨hz, hDz, e2⟩ := h2
      refine ⟨add_mem hy hz, by rw [map_add]; exact add_mem hDy hDz, ?_⟩
      have e3 : (⟨D (y + z), by rw [map_add]; exact add_mem hDy hDz⟩ : ↥(locF 𝔭 A₀)) =
          ⟨D y, hDy⟩ + ⟨D z, hDz⟩ := Subtype.ext (map_add D y z)
      have e4 : (⟨y + z, add_mem hy hz⟩ : ↥(locF 𝔭 A₀)) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [e3, e4, Submodule.Quotient.mk_add, Submodule.Quotient.mk_add, map_add, e1, e2]
    | smul a y _ h1 =>
      obtain ⟨hy, hDy, e1⟩ := h1
      have hs : D (a • y) = a • D y := LinearMap.map_smul_of_tower D a y
      refine ⟨Submodule.smul_mem _ a hy, by rw [hs]; exact Submodule.smul_mem _ a hDy, ?_⟩
      have e3 : (⟨D (a • y), by rw [hs]; exact Submodule.smul_mem _ a hDy⟩ : ↥(locF 𝔭 A₀)) =
          a • ⟨D y, hDy⟩ := Subtype.ext hs
      have e4 : (⟨a • y, Submodule.smul_mem _ a hy⟩ : ↥(locF 𝔭 A₀)) = a • ⟨y, hy⟩ := rfl
      rw [e3, e4, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, map_smul, e1]
  refine ⟨D, fun x => ?_⟩
  have hx : (x : V) ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by rw [hb]; exact x.2
  obtain ⟨t, ht, hxt⟩ := (LocalSpans.mem_locF 𝔭 _ _).1 hx
  obtain ⟨hy, hDy, e1⟩ := key _ hxt
  have hs : D (algebraMap (𝓞 F) (𝓞 K) t • (x : V)) = algebraMap (𝓞 F) (𝓞 K) t • D x :=
    LinearMap.map_smul_of_tower D _ _
  have hDx : D x ∈ locF 𝔭 A₀ := mem_locF_of_smul_mem h𝔭 A₀ ht (hs ▸ hDy)
  refine ⟨hDx, ?_⟩
  obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (Y (Submodule.Quotient.mk x))
  rw [← hw, Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
  have e4 : (⟨algebraMap (𝓞 F) (𝓞 K) t • (x : V), hy⟩ : ↥(locF 𝔭 A₀)) = algebraMap (𝓞 F) (𝓞 K) t • x := rfl
  rw [e4, Submodule.Quotient.mk_smul, Y.map_smul, ← hw, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
    Submodule.mem_smul_top_iff] at e1
  refine mem_smul_of_smul_mem h𝔭 _ k ht (sub_mem hDx w.2) ?_
  have e5 : algebraMap (𝓞 F) (𝓞 K) t • (D x - (w : V)) =
      D (algebraMap (𝓞 F) (𝓞 K) t • (x : V)) - algebraMap (𝓞 F) (𝓞 K) t • (w : V) := by
    rw [hs, smul_sub]
  show algebraMap (𝓞 F) (𝓞 K) t • (D x - (w : V)) ∈ _
  rw [e5]
  exact e1

theorem exists_redEnd_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ k)
    (Y : Module.End (𝓞 K) (↥(locF 𝔭 A₀) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 A₀))))
    (hY : ∀ x y x' y' : ↥(locF 𝔭 A₀), Submodule.Quotient.mk x' = Y (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = Y (Submodule.Quotient.mk y) →
      CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) :
    ∃ (X : V ≃ₗ[K] V) (hX : X ∈ sSub h (locF 𝔭 A₀) 𝔭 k), redEnd (locF 𝔭 A₀) 𝔭 k X hX.1 = Y := by
  obtain ⟨g, hg, hgY⟩ := exists_isom_lift hK hF hs hd hA₀ hA₀i h𝔭 hk Y hY
  have hgA : g ∈ glSub (locF 𝔭 A₀) := hg.2
  obtain ⟨D, hD⟩ := exists_lift hA₀ h𝔭 k Y
  have hle : extP K 𝔭 ^ (k - eA h (locF 𝔭 A₀) 𝔭) • locF 𝔭 A₀ ≤ extP K 𝔭 • locF 𝔭 A₀ :=
    Submodule.smul_mono_left (Ideal.pow_le_self (by omega))
  let E : V →ₗ[K] V := (g⁻¹ : V ≃ₗ[K] V).toLinearMap ∘ₗ D - LinearMap.id
  have hE : E ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀) := by
    intro x hx
    obtain ⟨hDx, h1⟩ := hD ⟨x, hx⟩
    have h2 := apply_mem_smul (inv_mem hgA) _ (hle (hgY ⟨x, hx⟩ ⟨D x, hDx⟩ h1))
    have h3 := neg_mem h2
    have e3 : E x = -(g⁻¹ (g x - D x)) := by
      simp [E]
    rw [e3]
    exact h3
  obtain ⟨Z, hZ, hZA⟩ := exists_equiv_of_mem_endL hA₀ h𝔭 hE
  have hXD : ∀ x, (g * Z) x = D x := fun x => by
    rw [LinearEquiv.mul_apply, hZ]
    simp [E]
  have hXA : g * Z ∈ glSub (locF 𝔭 A₀) := mul_mem hgA hZA
  have hmk : ∀ x : ↥(locF 𝔭 A₀), Submodule.Quotient.mk (⟨(g * Z) x, apply_mem hXA x.2⟩ : ↥(locF 𝔭 A₀)) =
      Y (Submodule.Quotient.mk x) := fun x => by
    obtain ⟨hDx, h1⟩ := hD x
    rw [← h1]
    congr 1
    exact Subtype.ext (hXD x)
  refine ⟨g * Z, ⟨hXA, fun x hx y hy => ?_⟩, ?_⟩
  · exact (congrP_algebraMap_iff_sub_mem h𝔭).1 (hY ⟨x, hx⟩ ⟨y, hy⟩ _ _ (hmk ⟨x, hx⟩) (hmk ⟨y, hy⟩))
  · refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    rw [redEnd_mk]
    exact hmk x

end RedC

theorem alphaL_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, alphaL h (locF 𝔭 A₀) 𝔭 =
      (akCount h (locF 𝔭 A₀) 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2) := by
  refine ⟨2 * vd h A₀ 𝔭 + 1, fun k hk => ?_⟩
  have h1 : alphaL h (locF 𝔭 A₀) 𝔭 = alphaL h A₀ 𝔭 := by
    unfold alphaL
    simp_rw [akCount_locF hF h A₀ 𝔭 h𝔭]
  rw [h1, akCount_locF hF h A₀ 𝔭 h𝔭]
  exact firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hA₀ hA₀i h𝔭 hk

theorem akCount_eq_relIndex (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, akCount h (locF 𝔭 A₀) 𝔭 k =
      (nSub (locF 𝔭 A₀) 𝔭 k).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k) := by
  refine ⟨eA h (locF 𝔭 A₀) 𝔭 + 1, fun k hk => ?_⟩
  symm
  unfold akCount Subgroup.relIndex
  refine RedC.index_eq_card _
    (fun X : ↥(sSub h (locF 𝔭 A₀) 𝔭 k) => ⟨RedC.redEnd (locF 𝔭 A₀) 𝔭 k X.1 X.2.1,
      RedC.redEnd_cond hF hA₀i h𝔭 X.2⟩) ?_ ?_
  · rintro ⟨Y, hY⟩
    obtain ⟨X, hX, e⟩ := RedC.exists_redEnd_eq hK hF hs hd hA₀ hA₀i h𝔭 hk Y hY
    exact ⟨⟨X, hX⟩, Subtype.ext e⟩
  · intro a b
    rw [Subtype.mk.injEq, RedC.redEnd_eq_iff, Subgroup.mem_subgroupOf]
    rfl

end Formalism.HermitianLattices.Ext.L3.D2
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

theorem relIndex_eq_card_image {G α : Type*} [Group G] (H S : Subgroup G) (f : G → α)
    (hf : ∀ a ∈ S, ∀ b ∈ S, f a = f b ↔ a⁻¹ * b ∈ H) :
    H.relIndex S = Nat.card {c : α // ∃ a ∈ S, f a = c} := by
  classical
  show Nat.card (S ⧸ H.subgroupOf S) = _
  apply Nat.card_congr
  refine Equiv.ofBijective (fun q => Quotient.liftOn' q
    (fun a : S => (⟨f a, a, a.2, rfl⟩ : {c : α // ∃ a ∈ S, f a = c})) ?_) ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    show f a = f b
    have hab' : a⁻¹ * b ∈ H.subgroupOf S := QuotientGroup.leftRel_apply.mp hab
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hab'
    exact (hf a a.2 b b.2).mpr hab'
  · intro q₁ q₂ e
    induction q₁ using QuotientGroup.induction_on with
    | H a =>
    induction q₂ using QuotientGroup.induction_on with
    | H b =>
    have e' : f a = f b := congrArg Subtype.val e
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (hf a a.2 b b.2).mp e'
  · rintro ⟨c, a, ha, rfl⟩
    exact ⟨QuotientGroup.mk ⟨a, ha⟩, rfl⟩

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem gmap_eq_iff (a b : V ≃ₗ[K] V) (B : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap a B = Formalism.HermitianLatticesTheory.gmap b B ↔ a⁻¹ * b ∈ glSub B := by
  rw [mem_glSub]
  constructor
  · intro e
    rw [autSub_gmap_mul, ← e, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
  · intro e
    rw [show b = a * (a⁻¹ * b) from (mul_inv_cancel_left a b).symm, autSub_gmap_mul a, e]

theorem autSub_le_sSub (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    autSub h A ≤ sSub h A 𝔭 k := fun X hX => ⟨hX.2, fun x _ y _ => by
  rw [hX.1 x y, sub_self]
  exact Submodule.zero_mem _⟩

theorem coe_mem_of_mem_smul_top (I : Ideal (𝓞 K)) (A : Submodule (𝓞 K) V) {u : ↥A}
    (hu : u ∈ (I • ⊤ : Submodule (𝓞 K) ↥A)) : (u : V) ∈ I • A := by
  have h2 := Submodule.mem_map_of_mem (f := A.subtype) hu
  rwa [Submodule.map_smul'', Submodule.map_subtype_top] at h2

theorem exists_autSub_mul_nSub (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ k) {X : V ≃ₗ[K] V}
    (hX : X ∈ sSub h (locF 𝔭 A₀) 𝔭 k) :
    ∃ g ∈ autSub h (locF 𝔭 A₀), g⁻¹ * X ∈ nSub (locF 𝔭 A₀) 𝔭 (k - eA h (locF 𝔭 A₀) 𝔭) := by
  obtain ⟨hXg, hXh⟩ := hX
  set A := locF 𝔭 A₀ with hA
  let f : ↥A →ₗ[𝓞 K] ↥A :=
    (((X : V →ₗ[K] V).restrictScalars (𝓞 K)).domRestrict A).codRestrict A
      (fun x => apply_mem hXg x.2)
  have hf : ∀ x : ↥A, ((f x : ↥A) : V) = X x := fun x => rfl
  let Xb : Module.End (𝓞 K) (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)) :=
    Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top _ f)
  have key : ∀ x x' : ↥A, Submodule.Quotient.mk x' = Xb (Submodule.Quotient.mk x) →
      (x' : V) - X x ∈ extP K 𝔭 ^ k • A := by
    intro x x' hx
    have h1 : x' - f x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) := by
      rw [← Submodule.Quotient.eq]
      exact hx
    exact coe_mem_of_mem_smul_top _ _ h1
  have h0 : ∀ {z : V}, z ∈ A → z ∈ extP K 𝔭 ^ 0 • A := fun hz => by rwa [pow_zero_smul]
  obtain ⟨g, hg, hgX⟩ := exists_isom_lift hK hF hs hd hA₀ hA₀i h𝔭 hk Xb (by
    intro x y x' y' hx hy
    rw [congrP_algebraMap_iff_sub_mem h𝔭]
    have hu := key x x' hx
    have hv := key y y' hy
    have e1 : h (x' : V) (y' : V) - h (x : V) (y : V) =
        (h (X x) (X y) - h (x : V) (y : V)) + h ((x' : V) - X x) (y' : V)
          + h (X x) ((y' : V) - X y) := by
      simp only [map_sub, LinearMap.sub_apply]
      ring
    rw [e1]
    refine add_mem (add_mem (hXh x x.2 y y.2) ?_) ?_
    · simpa using form_mem_pK hF hA₀i h𝔭 hu (h0 y'.2)
    · simpa using form_mem_pK hF hA₀i h𝔭 (h0 (apply_mem hXg x.2)) hv)
  refine ⟨g, hg, mul_mem (inv_mem hg.2) hXg, fun x hx => ?_⟩
  have h1 := hgX ⟨x, hx⟩ (f ⟨x, hx⟩) rfl
  have h2 := apply_mem_smul (inv_mem (show g ∈ glSub A from hg.2)) _ ((Submodule.neg_mem _ h1))
  have e : ∀ z : V, g⁻¹ (g z) = z := fun z => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  simpa [e, hf] using h2

theorem relIndex_inf_glSub (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k) =
      orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀) := by
  obtain ⟨k₁, hk₁⟩ := nSub_le_glSub hA₀ hB₀ h𝔭
  refine ⟨eA h (locF 𝔭 A₀) 𝔭 + 1 + k₁, fun k hk => ?_⟩
  rw [Subgroup.inf_relIndex_left,
    relIndex_eq_card_image _ _ (fun X => Formalism.HermitianLatticesTheory.gmap X (locF 𝔭 B₀))
      (fun a _ b _ => gmap_eq_iff a b _)]
  unfold orbCount
  refine Nat.card_congr (Equiv.subtypeEquivRight fun C => ⟨?_, ?_⟩)
  · rintro ⟨X, hX, rfl⟩
    obtain ⟨g, hg, hY⟩ := exists_autSub_mul_nSub hK hF hs hd hA₀ hA₀i h𝔭 (by omega) hX
    exact ⟨g, hg.1, hg.2, (gmap_eq_iff g X _).2 (hk₁ _ (by omega) hY)⟩
  · rintro ⟨g, hg, hgA, rfl⟩
    exact ⟨g, autSub_le_sSub h _ 𝔭 k ⟨hg, hgA⟩, rfl⟩

end Formalism.HermitianLattices.Ext.L3.D2
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem relIndex_eq_of_map {G M : Type*} [Group G] [AddCommGroup M] (H G' : Subgroup G)
    (N P : AddSubgroup M) (φ : G → M) (h1 : ∀ x ∈ G', φ x ∈ P) (h2 : ∀ p ∈ P, ∃ x ∈ G', φ x = p)
    (h3 : ∀ x ∈ G', ∀ y ∈ G', x⁻¹ * y ∈ H ↔ φ y - φ x ∈ N) : H.relIndex G' = N.relIndex P := by
  classical
  rw [Subgroup.relIndex, AddSubgroup.relIndex, Subgroup.index, AddSubgroup.index]

  have hrel : ∀ a b : G', (a⁻¹ * b ∈ H.subgroupOf G') ↔
      (-(⟨φ a, h1 a a.2⟩ : P) + ⟨φ b, h1 b b.2⟩ ∈ N.addSubgroupOf P) := by
    intro a b
    rw [Subgroup.mem_subgroupOf, AddSubgroup.mem_addSubgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, AddSubgroup.coe_add, AddSubgroup.coe_neg, neg_add_eq_sub]
    exact h3 a a.2 b b.2
  let f : G' ⧸ H.subgroupOf G' → P ⧸ N.addSubgroupOf P :=
    Quotient.map' (fun x : G' => (⟨φ x, h1 x x.2⟩ : P)) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab
      rw [QuotientAddGroup.leftRel_apply]
      exact (hrel a b).1 hab)
  refine Nat.card_congr (Equiv.ofBijective f ⟨fun a b hab => ?_, fun p => ?_⟩)
  · induction a using QuotientGroup.induction_on with
    | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
    have hab' : ((⟨φ a, h1 a a.2⟩ : P) : P ⧸ N.addSubgroupOf P) = ((⟨φ b, h1 b b.2⟩ : P) : _) := hab
    rw [QuotientAddGroup.eq] at hab'
    exact QuotientGroup.eq.2 ((hrel a b).2 hab')
  · induction p using QuotientAddGroup.induction_on with
    | H p =>
    obtain ⟨x, hx, hφ⟩ := h2 p p.2
    refine ⟨((⟨x, hx⟩ : G') : G' ⧸ H.subgroupOf G'), ?_⟩
    change ((⟨φ x, h1 x hx⟩ : P) : P ⧸ N.addSubgroupOf P) = (p : _)
    congr 1
    exact Subtype.ext hφ

theorem relIndex_nSub_eq {A₀ B₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ c₀ : ℕ, ∀ c ≥ c₀, ∃ k₀ : ℕ, ∀ k ≥ k₀, nSub (locF 𝔭 B₀) 𝔭 (k + c) ≤ nSub (locF 𝔭 A₀) 𝔭 k ∧
      endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) ≤ endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀) ∧
      (nSub (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (nSub (locF 𝔭 A₀) 𝔭 k) =
        (endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀)).relIndex
          (endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀)) := by
  obtain ⟨r, hr⟩ := exists_endL_le hB₀ hA₀ h𝔭
  obtain ⟨k₁, hk₁⟩ := nSub_le_glSub hA₀ hB₀ h𝔭
  refine ⟨r, fun c hc => ⟨max k₁ 1, fun k hk => ?_⟩⟩
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk

  have hle : endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) ≤
      endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀) := by
    intro D hD
    refine hr k ?_
    intro x hx
    exact smul_anti 𝔭 _ (by omega) (hD x hx)

  have hlift : ∀ D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀),
      ∃ X ∈ nSub (locF 𝔭 A₀) 𝔭 k, (X : V →ₗ[K] V) - LinearMap.id = D := by
    intro D hD
    have hD1 : D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀) := by
      intro x hx
      have := smul_anti 𝔭 (locF 𝔭 A₀) hk1 (hD x hx)
      rwa [pow_one] at this
    obtain ⟨X, hX, hXg⟩ := exists_equiv_of_mem_endL hA₀ h𝔭 hD1
    refine ⟨X, mem_nSub.2 ⟨hXg, fun x hx => ?_⟩, ?_⟩
    · rw [hX, add_sub_cancel_left]
      exact hD x hx
    · ext v
      simp [hX]
  have hnsub : nSub (locF 𝔭 B₀) 𝔭 (k + c) ≤ nSub (locF 𝔭 A₀) 𝔭 k := by
    intro X hXm
    obtain ⟨hXB, hX⟩ := mem_nSub.1 hXm
    have hD : (X : V →ₗ[K] V) - LinearMap.id ∈ endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) := by
      intro x hx
      simpa using hX x hx
    obtain ⟨X', hX'm, hX'⟩ := hlift _ (hle hD)
    have hXX : X' = X := by
      ext v
      have := LinearMap.congr_fun hX' v
      simpa using this
    rw [← hXX]
    exact hX'm
  refine ⟨hnsub, hle, ?_⟩
  refine relIndex_eq_of_map _ _ _ _ (fun X => (X : V →ₗ[K] V) - LinearMap.id) (fun X hX => ?_)
    (fun D hD => ?_) (fun x hx y hy => ?_)
  · intro v hv
    simpa using (mem_nSub.1 hX).2 v hv
  · obtain ⟨X, hXm, hX⟩ := hlift D hD
    exact ⟨X, hXm, hX⟩
  · have hxB : x ∈ glSub (locF 𝔭 B₀) := hk₁ k (le_trans (le_max_left _ _) hk) hx
    have hyB : y ∈ glSub (locF 𝔭 B₀) := hk₁ k (le_trans (le_max_left _ _) hk) hy
    have hxyB : x⁻¹ * y ∈ glSub (locF 𝔭 B₀) := mul_mem (inv_mem hxB) hyB
    have e1 : ∀ v : V, x (x⁻¹ v) = v := fun v => by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    rw [mem_nSub]
    constructor
    · rintro ⟨_, h⟩ v hv
      have h' := apply_mem_smul hxB _ (h v hv)
      have e2 : x ((x⁻¹ * y) v - v) = y v - x v := by
        rw [map_sub, LinearEquiv.mul_apply, e1]
      rw [e2] at h'
      simpa using h'
    · intro h
      refine ⟨hxyB, fun v hv => ?_⟩
      have h' := apply_mem_smul (inv_mem hxB) _ (h v hv)
      have e2 : x⁻¹ ((((y : V →ₗ[K] V) - LinearMap.id) - ((x : V →ₗ[K] V) - LinearMap.id) :
          V →ₗ[K] V) v) =
          (x⁻¹ * y) v - v := by
        simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, sub_sub_sub_cancel_right,
          map_sub, LinearEquiv.mul_apply]
        rw [← LinearEquiv.mul_apply x⁻¹ x, inv_mul_cancel]
        rfl
      rw [e2] at h'
      exact h'

theorem relIndex_endL (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {A₀ B₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k c : ℕ}
    (hle : endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) ≤
      endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀)) :
    (endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀)).relIndex
        (endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀)) =
      Ideal.absNorm 𝔭 ^ (2 * finrank K V ^ 2 * c) := by
  classical
  obtain ⟨a, b, e, c0, hc0, he, hA, hB, hbe⟩ := exists_smith hA₀ hB₀ h𝔭
  have hinj := IsFractionRing.injective (𝓞 K) K
  set eK : Fin (finrank K V) → K := fun i => algebraMap (𝓞 K) K (e i) with heKdef
  set c0K : K := algebraMap (𝓞 K) K c0 with hc0Kdef
  have heK : ∀ i, eK i ≠ 0 := fun i => (map_ne_zero_iff _ hinj).2 (he i)
  have hc0K : c0K ≠ 0 := (map_ne_zero_iff _ hinj).2 hc0
  have hbeK : ∀ i, c0K • b i = eK i • a i := fun i => by
    simp only [c0K, eK, algebraMap_smul]
    exact hbe i
  have hab : ∀ l, a l = (c0K / eK l) • b l := fun l => by
    rw [div_eq_mul_inv, mul_comm, ← smul_smul, hbeK l, smul_smul, inv_mul_cancel₀ (heK l), one_smul]
  have hba : ∀ j, b j = (eK j / c0K) • a j := fun j => by
    rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← hbeK j, smul_smul, inv_mul_cancel₀ hc0K, one_smul]

  have key : ∀ (D : V →ₗ[K] V) i j, LinearMap.toMatrix b b D i j * eK i =
      eK j * LinearMap.toMatrix a a D i j := by
    intro D i j
    have h2 : D (a j) = ∑ l, (LinearMap.toMatrix a a D l j * (c0K / eK l)) • b l := by
      conv_lhs => rw [← a.sum_repr (D (a j))]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [LinearMap.toMatrix_apply, ← smul_smul, ← hab l]
    rw [LinearMap.toMatrix_apply b b, hba j, map_smul, h2, map_smul, Finsupp.smul_apply, map_sum,
      Finsupp.finset_sum_apply]
    simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    field_simp [heK i, hc0K]
  let φA : (V →ₗ[K] V) →+ Matrix (Fin (finrank K V)) (Fin (finrank K V)) K :=
    (LinearMap.toMatrix a a).toLinearMap.toAddMonoidHom
  have hφA : Function.Surjective φA := (LinearMap.toMatrix a a).surjective
  have hEA : endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀) =
      (matL 𝔭 k (fun _ _ => (1 : K)) (fun _ _ => 1)).comap φA := by
    ext D
    rw [AddSubgroup.mem_comap, ← hA, mem_endL_iff a h𝔭]
    constructor
    · intro h i j
      exact ⟨_, h i j, by simp [φA]⟩
    · intro h i j
      obtain ⟨w, hw, hw'⟩ := h i j
      simp only [one_mul, φA] at hw'
      rw [show LinearMap.toMatrix a a D i j = w from hw']
      exact hw
  have hEB : endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) =
      (matL 𝔭 (k + c) (fun _ j => eK j) (fun i _ => eK i)).comap φA := by
    ext D
    rw [AddSubgroup.mem_comap, ← hB, mem_endL_iff b h𝔭]
    constructor
    · intro h i j
      refine ⟨_, h i j, ?_⟩
      simp only [φA, LinearEquiv.coe_toLinearMap, LinearMap.toAddMonoidHom_coe]
      rw [← key, mul_comm]
    · intro h i j
      obtain ⟨w, hw, hw'⟩ := h i j
      simp only [φA, LinearEquiv.coe_toLinearMap, LinearMap.toAddMonoidHom_coe] at hw'
      rw [← key, mul_comm] at hw'
      rw [mul_left_cancel₀ (heK i) hw']
      exact hw
  rw [hEA, hEB] at hle ⊢
  have hle' : matL 𝔭 (k + c) (fun _ j => eK j) (fun i _ => eK i) ≤
      matL 𝔭 k (fun _ _ => (1 : K)) (fun _ _ => 1) := by
    intro M hM
    obtain ⟨D, rfl⟩ := hφA M
    exact hle hM
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hφA]
  have hmat := relIndex_matL hK hF h𝔭 (fun _ j => eK j) (fun i _ => eK i)
    (fun _ j => ⟨algebraMap_mem_pK 𝔭 _, heK j⟩) (fun i _ => ⟨algebraMap_mem_pK 𝔭 _, heK i⟩) k c hle'
  rw [Finset.prod_comm] at hmat
  have hP : (∏ i : Fin (finrank K V), ∏ _j : Fin (finrank K V), nO 𝔭 (eK i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun _ _ =>
      nO_ne_zero hK hF h𝔭 (algebraMap_mem_pK 𝔭 _) (heK i)
  rw [mul_comm _ (Ideal.absNorm 𝔭 ^ _)] at hmat
  simpa [Fintype.card_fin] using Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hP) hmat

theorem relIndex_nSub (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {A₀ B₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ c₀ : ℕ, ∀ c ≥ c₀, ∃ k₀ : ℕ, ∀ k ≥ k₀, nSub (locF 𝔭 B₀) 𝔭 (k + c) ≤ nSub (locF 𝔭 A₀) 𝔭 k ∧
      (nSub (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (nSub (locF 𝔭 A₀) 𝔭 k) =
        Ideal.absNorm 𝔭 ^ (2 * finrank K V ^ 2 * c) := by
  obtain ⟨c₀, hc₀⟩ := relIndex_nSub_eq hA₀ hB₀ h𝔭
  refine ⟨c₀, fun c hc => ?_⟩
  obtain ⟨k₀, hk₀⟩ := hc₀ c hc
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hk₀ k hk
  exact ⟨h1, h3.trans (relIndex_endL hK hF hA₀ hB₀ h𝔭 h2)⟩

end Formalism.HermitianLattices.Ext.L3.D2
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2.IA

theorem relIndex_eq_of_map {G M : Type*} [Group G] [AddCommGroup M] (H T : Subgroup G)
    (N' N : AddSubgroup M) (f : G → M) (hf : ∀ X ∈ T, f X ∈ N)
    (hc : ∀ X ∈ T, ∀ Y ∈ T, X⁻¹ * Y ∈ H ↔ f X - f Y ∈ N')
    (hsurj : ∀ Z ∈ N, ∃ X ∈ T, f X - Z ∈ N') : H.relIndex T = N'.relIndex N := by
  unfold Subgroup.relIndex AddSubgroup.relIndex Subgroup.index AddSubgroup.index
  let g : (T ⧸ H.subgroupOf T) → (N ⧸ N'.addSubgroupOf N) :=
    Quotient.lift (s := QuotientGroup.leftRel (H.subgroupOf T))
      (fun X : T => ((⟨f X, hf X X.2⟩ : N) : N ⧸ N'.addSubgroupOf N)) (by
        intro X Y hXY
        have hXY := QuotientGroup.leftRel_apply.1 hXY
        have h1 : f X - f Y ∈ N' := (hc X X.2 Y Y.2).1 (by simpa [Subgroup.mem_subgroupOf] using hXY)
        rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        have := N'.neg_mem h1
        simpa [neg_add_eq_sub] using this)
  refine Nat.card_eq_of_bijective g ⟨?_, ?_⟩
  · intro a b
    induction a using QuotientGroup.induction_on with | _ X => ?_
    induction b using QuotientGroup.induction_on with | _ Y => ?_
    intro hab
    have h1 : ((⟨f X, hf X X.2⟩ : N) : N ⧸ N'.addSubgroupOf N) = ((⟨f Y, hf Y Y.2⟩ : N) : N ⧸ N'.addSubgroupOf N) := hab
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h2 : f X - f Y ∈ N' := by
      have := N'.neg_mem h1
      simpa [neg_add_eq_sub] using this
    simpa using (hc X X.2 Y Y.2).2 h2
  · intro b
    induction b using QuotientAddGroup.induction_on with | _ Z => ?_
    obtain ⟨X, hX, hXZ⟩ := hsurj Z Z.2
    refine ⟨((⟨X, hX⟩ : T) : T ⧸ H.subgroupOf T), ?_⟩
    show ((⟨f X, hf X hX⟩ : N) : N ⧸ N'.addSubgroupOf N) = (Z : N ⧸ N'.addSubgroupOf N)
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    have := N'.neg_mem hXZ
    simpa [neg_add_eq_sub] using this

variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem surjective_of_nondegenerate {h : V →ₗ⋆[K] V →ₗ[K] K} (hn : h.Nondegenerate) :
    Function.Surjective h := by
  have hinj : Function.Injective h := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact hn.1 x (fun y => by rw [hx]; rfl)
  have hbij : Function.Bijective (h.rangeRestrict) :=
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), h.surjective_rangeRestrict⟩
  let j : V ≃+ LinearMap.range h := AddEquiv.ofBijective (h.rangeRestrict).toAddMonoidHom hbij
  have hr : Module.rank K V = Module.rank K (LinearMap.range h) :=
    rank_eq_of_equiv_equiv (starRingEnd K) j star_involutive.bijective (fun r m => by
      apply Subtype.ext
      show h (r • m) = (starRingEnd K) r • h m
      rw [map_smulₛₗ])
  have hf : finrank K (LinearMap.range h) = finrank K (Dual K V) := by
    rw [Subspace.dual_finrank_eq]
    unfold finrank
    rw [hr]
  have htop := Submodule.eq_top_of_finrank_eq hf
  exact LinearMap.range_eq_top.1 htop

theorem exists_adj {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hn : h.Nondegenerate)
    (s : V →ₗ⋆[K] V →ₗ[K] K) : ∃ Y : V →ₗ[K] V, ∀ x y, h x (Y y) = s x y := by
  have hex : ∀ y, ∃ w, ∀ x, h x w = s x y := by
    intro y
    let l : V →ₗ[K] K :=
      { toFun := fun x => star (s x y)
        map_add' := fun a b => by simp
        map_smul' := fun a b => by simp [starRingEnd_apply] }
    obtain ⟨w, hw⟩ := surjective_of_nondegenerate hn l
    refine ⟨w, fun x => ?_⟩
    have h1 : h w x = star (s x y) := by rw [hw]; rfl
    have h2 := hs.eq w x
    rw [← h2, h1, starRingEnd_apply, star_star]
  choose Y hY using hex
  refine ⟨{ toFun := Y, map_add' := fun a b => ?_, map_smul' := fun a b => ?_ }, fun x y => hY y x⟩
  · rw [← sub_eq_zero]
    refine hn.2 _ (fun x => ?_)
    rw [map_sub, map_add, hY, hY, hY, map_add, sub_self]
  · rw [← sub_eq_zero]
    refine hn.2 _ (fun x => ?_)
    rw [RingHom.id_apply, map_sub, map_smul, hY, hY, map_smul, sub_self]

section Lat

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def phi (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V ≃ₗ[K] V) : V →ₗ⋆[K] V →ₗ[K] K :=
  (h.comp (X : V →ₗ[K] V)).compl₂ (X : V →ₗ[K] V) - h

theorem phi_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V ≃ₗ[K] V) (x y : V) :
    phi h X x y = h (X x) (X y) - h x y := rfl

theorem star_phi {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (X : V ≃ₗ[K] V) (x y : V) :
    star (phi h X x y) = phi h X y x := by
  have e : ∀ a b, star (h a b) = h b a := fun a b => hs.eq a b
  rw [phi_apply, phi_apply, star_sub, e, e]

theorem unif_ne_zero {𝔭 : Ideal (𝓞 F)} {π : 𝓞 F} (hπ' : π ∉ 𝔭 ^ 2) : algebraMap F K (π : F) ≠ 0 := by
  intro h0
  have h1 : (π : F) = 0 := (map_eq_zero (algebraMap F K)).1 h0
  have h2 : π = 0 := by exact_mod_cast h1
  exact hπ' (h2 ▸ zero_mem _)

theorem sesq_scale (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A₀ B₀ : Submodule (𝓞 K) V} {r : ℕ}
    (hr : extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀) (s : V →ₗ⋆[K] V →ₗ[K] K) {n m : ℕ} (hnm : n + 2 * r ≤ m)
    (hs : ∀ x ∈ locF 𝔭 B₀, ∀ y ∈ locF 𝔭 B₀, s x y ∈ pK K 𝔭 m) :
    ∀ x ∈ locF 𝔭 A₀, ∀ y ∈ locF 𝔭 A₀, s x y ∈ pK K 𝔭 n := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have h0 : algebraMap F K (π : F) ≠ 0 := unif_ne_zero hπ'
  have hst : star (algebraMap F K (π : F)) = algebraMap F K (π : F) := (hF _).2 ⟨_, rfl⟩
  intro x hx y hy
  have hx' : algebraMap F K (π : F) ^ r • x ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨x, hx, rfl⟩)
  have hy' : algebraMap F K (π : F) ^ r • y ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨y, hy, rfl⟩)
  have h1 := pK_anti (K := K) 𝔭 hnm (hs _ hx' _ hy')
  rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_pow, hst, smul_eq_mul, smul_eq_mul] at h1
  obtain ⟨b, hb, e⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 h1
  refine (mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨b, hb, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero (2 * r) h0)
  calc algebraMap F K (π : F) ^ (2 * r) * s x y
      = algebraMap F K (π : F) ^ r * (algebraMap F K (π : F) ^ r * s x y) := by ring
    _ = algebraMap F K (π : F) ^ (n + 2 * r) * b := e
    _ = _ := by ring

theorem end_scale {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A₀ B₀ : Submodule (𝓞 K) V} {r r' : ℕ}
    (hr : extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀) (hr' : extP K 𝔭 ^ r' • locF 𝔭 B₀ ≤ locF 𝔭 A₀)
    (Y : V →ₗ[K] V) {n m : ℕ} (hnm : n + r + r' ≤ m)
    (hY : ∀ x ∈ locF 𝔭 A₀, Y x ∈ extP K 𝔭 ^ m • locF 𝔭 A₀) :
    ∀ x ∈ locF 𝔭 B₀, Y x ∈ extP K 𝔭 ^ n • locF 𝔭 B₀ := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have h0 : algebraMap F K (π : F) ≠ 0 := unif_ne_zero hπ'
  intro x hx
  have hx' : algebraMap F K (π : F) ^ r' • x ∈ locF 𝔭 A₀ :=
    hr' ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨x, hx, rfl⟩)
  have h1 := smul_anti 𝔭 (locF 𝔭 A₀) hnm (hY _ hx')
  obtain ⟨a, ha, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 h1
  have ha' : algebraMap F K (π : F) ^ r • a ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨a, ha, rfl⟩)
  refine (mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨_, ha', ?_⟩
  rw [map_smul] at e
  apply smul_right_injective V (pow_ne_zero r' h0)
  show algebraMap F K (π : F) ^ r' • Y x = algebraMap F K (π : F) ^ r' • _
  rw [e, smul_smul, smul_smul]
  congr 1
  ring

end Lat

end Formalism.HermitianLattices.Ext.L3.D2.IA
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

private theorem exists_int_add_star_eq_one_of_isCMUnram (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    ∃ θ : 𝓞 K, algebraMap (𝓞 K) K θ + star (algebraMap (𝓞 K) K θ) = 1 := by
  classical
  have hstarF : ∀ f : F, star (algebraMap F K f) = algebraMap F K f := fun f => (hF _).mpr ⟨f, rfl⟩
  have hint : ∀ c : 𝓞 F, IsIntegral ℤ (algebraMap F K (algebraMap (𝓞 F) F c)) := fun c =>
    (isIntegral_algebraMap_iff (algebraMap F K).injective).mpr
      (NumberField.RingOfIntegers.isIntegral_coe c)
  have hcompat : ∀ x : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) x) =
      algebraMap F K (algebraMap (𝓞 F) F x) := fun x => rfl
  let tr : 𝓞 K → K := fun θ => algebraMap (𝓞 K) K θ + star (algebraMap (𝓞 K) K θ)
  show ∃ θ : 𝓞 K, tr θ = 1
  by_contra hne
  push_neg at hne
  let I : Ideal (𝓞 F) :=
    { carrier := {a | ∃ θ : 𝓞 K, tr θ = algebraMap F K (algebraMap (𝓞 F) F a)}
      add_mem' := by
        rintro a b ⟨θ, hθ⟩ ⟨θ', hθ'⟩
        refine ⟨θ + θ', ?_⟩
        simp only [tr, map_add, star_add] at hθ hθ' ⊢
        linear_combination hθ + hθ'
      zero_mem' := ⟨0, by simp [tr]⟩
      smul_mem' := by
        rintro c a ⟨θ, hθ⟩
        refine ⟨algebraMap (𝓞 F) (𝓞 K) c * θ, ?_⟩
        simp only [tr, smul_eq_mul, map_mul, star_mul', hcompat, hstarF] at hθ ⊢
        linear_combination (algebraMap F K (algebraMap (𝓞 F) F c)) * hθ }
  have hI : (1 : 𝓞 F) ∉ I := by
    rintro ⟨θ, hθ⟩
    exact hne θ (by simpa using hθ)
  obtain ⟨𝔮, h𝔮, hI𝔮⟩ := Ideal.exists_le_maximal I ((Ideal.ne_top_iff_one I).mpr hI)
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ 𝔮 := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have h1 : algebraMap F K (algebraMap (𝓞 F) F x) = algebraMap F K (algebraMap (𝓞 F) F 0) := by
      rw [← hcompat, hx, map_zero, map_zero, map_zero]
    have h2 := IsFractionRing.injective (𝓞 F) F ((algebraMap F K).injective h1)
    rw [h2]
    exact 𝔮.zero_mem
  obtain ⟨P, hP, hP𝔮⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) 𝔮 hker
  obtain ⟨a, t, ht, hat⟩ := hK.2.2 P hP
  have hta : star (algebraMap (𝓞 K) K t) = algebraMap (𝓞 K) K a := by rw [ht, star_star]
  have hdfix : star ((algebraMap (𝓞 K) K a - algebraMap (𝓞 K) K t) ^ 2) =
      (algebraMap (𝓞 K) K a - algebraMap (𝓞 K) K t) ^ 2 := by
    rw [star_pow, star_sub, ← ht, hta]
    ring
  obtain ⟨f, hf⟩ := (hF _).mp hdfix
  have hfi : IsIntegral ℤ f := by
    rw [← isIntegral_algebraMap_iff (A := F) (B := K) (algebraMap F K).injective, hf]
    have := NumberField.RingOfIntegers.isIntegral_coe ((a - t) ^ 2)
    simpa using this
  let fO : 𝓞 F := ⟨f, hfi⟩
  have hfI : fO ∈ I := by
    refine ⟨a * (a - t), ?_⟩
    show algebraMap (𝓞 K) K (a * (a - t)) + star (algebraMap (𝓞 K) K (a * (a - t))) =
      algebraMap F K f
    rw [hf]
    simp only [map_mul, map_sub, star_mul', star_sub, ← ht, hta]
    ring
  have hmem : algebraMap (𝓞 F) (𝓞 K) fO ∈ P := by
    rw [← Ideal.mem_comap, hP𝔮]
    exact hI𝔮 hfI
  have heq : algebraMap (𝓞 F) (𝓞 K) fO = (a - t) ^ 2 := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [hcompat]
    show algebraMap F K f = _
    rw [hf]
    simp
  rw [heq] at hmem
  exact hat (hP.isPrime.mem_of_pow_mem 2 hmem)

theorem exists_theta (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) :
    ∃ θ : K, θ ∈ pK K 𝔭 0 ∧ θ + star θ = 1 := by
  obtain ⟨θ, hθ⟩ := exists_int_add_star_eq_one_of_isCMUnram hK hF
  exact ⟨algebraMap (𝓞 K) K θ, algebraMap_mem_pK 𝔭 θ, hθ⟩

theorem mul_inv_mem_iff {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {A B : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {n : ℕ}
    {U W : V ≃ₗ[K] V} (hUA : U ∈ glSub A) (hUB : U ∈ glSub B) (hWA : W ∈ glSub A) (hWB : W ∈ glSub B) :
    U * W⁻¹ ∈ sSub h B 𝔭 n ⊓ glSub A ↔ IA.phi h U - IA.phi h W ∈ hermL B 𝔭 n := by
  have eW : ∀ z : V, W (W⁻¹ z) = z := fun z => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  have eW' : ∀ z : V, W⁻¹ (W z) = z := fun z => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  constructor
  · intro hX
    have hX' := (Subgroup.mem_inf.mp hX).1.2
    refine ⟨fun x y => ?_, fun x hx y hy => ?_⟩
    · simp only [AddSubgroupClass.coe_sub, LinearMap.sub_apply, star_sub, IA.star_phi hs]
    · have := hX' (W x) (apply_mem hWB hx) (W y) (apply_mem hWB hy)
      simp only [LinearEquiv.mul_apply, eW'] at this
      simpa only [LinearMap.sub_apply, IA.phi_apply, sub_sub_sub_cancel_right] using this
  · intro hZ
    refine Subgroup.mem_inf.mpr ⟨⟨mul_mem hUB (inv_mem hWB), fun x hx y hy => ?_⟩,
      mul_mem hUA (inv_mem hWA)⟩
    have := hZ.2 (W⁻¹ x) (apply_mem (inv_mem hWB) hx) (W⁻¹ y) (apply_mem (inv_mem hWB) hy)
    simp only [LinearMap.sub_apply, IA.phi_apply, sub_sub_sub_cancel_right, eW] at this
    simpa only [LinearEquiv.mul_apply] using this

theorem exists_newton (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {r r' e : ℕ}
    (hr : extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀) (hr' : extP K 𝔭 ^ r' • locF 𝔭 B₀ ≤ locF 𝔭 A₀)
    (he : ∀ (k : ℕ) (x : V), (∀ y ∈ locF 𝔭 A₀, h y x ∈ pK K 𝔭 (k + e)) → x ∈ extP K 𝔭 ^ k • locF 𝔭 A₀)
    {k c : ℕ} (hk : c + 2 * e + 2 * r' + r + r' + 1 ≤ k) {Z : V →ₗ⋆[K] V →ₗ[K] K}
    (hZ : Z ∈ hermL (locF 𝔭 A₀) 𝔭 k) :
    ∃ X ∈ sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀), IA.phi h X - Z ∈ hermL (locF 𝔭 B₀) 𝔭 (k + c) := by
  have hsym : ∀ a b : V, star (h a b) = h b a := by
    intro a b
    exact hs.eq a b
  obtain ⟨θ₀, hθ1⟩ := exists_int_add_star_eq_one_of_isCMUnram hK hF
  set θ : K := algebraMap (𝓞 K) K θ₀ with hθdef
  obtain ⟨Y0, hY0⟩ := IA.exists_adj hs (nondegenerate hd) Z
  set Y : V →ₗ[K] V := θ • Y0 with hYdef
  have hhY : ∀ x y, h x (Y y) = θ * Z x y := by
    intro x y
    rw [hYdef, LinearMap.smul_apply, map_smul, hY0, smul_eq_mul]
  have hYh : ∀ x y, h (Y x) y = star θ * Z x y := by
    intro x y
    rw [← hsym y (Y x), hhY, star_mul', hZ.1 y x]

  have hYA : ∀ x ∈ locF 𝔭 A₀, Y x ∈ extP K 𝔭 ^ (k - e) • locF 𝔭 A₀ := by
    intro x hx
    refine he (k - e) (Y x) fun y hy => ?_
    rw [hhY, show k - e + e = k by omega, hθdef, ← Algebra.smul_def]
    exact (pK K 𝔭 k).smul_mem θ₀ (hZ.2 y hy x hx)
  have hDA : Y ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀) := fun x hx =>
    Submodule.smul_mono_left (Ideal.pow_le_self (by omega)) (hYA x hx)
  obtain ⟨X, hXeq, hXA⟩ := exists_equiv_of_mem_endL hA₀ h𝔭 hDA
  have hYB := IA.end_scale h𝔭 hr hr' Y (n := 1) (m := k - e) (by omega) hYA
  have hDB : Y ∈ endL (locF 𝔭 B₀) (extP K 𝔭 • locF 𝔭 B₀) := fun x hx => by
    simpa only [pow_one] using hYB x hx
  obtain ⟨X', hX'eq, hX'B⟩ := exists_equiv_of_mem_endL hB₀ h𝔭 hDB
  have hXX : X = X' := LinearEquiv.ext fun x => by rw [hXeq, hX'eq]
  have hphi : ∀ x y, IA.phi h X x y - Z x y = h (Y x) (Y y) := by
    intro x y
    rw [IA.phi_apply, hXeq, hXeq]
    simp only [map_add, LinearMap.add_apply]
    rw [hhY, hYh]
    linear_combination (Z x y) * hθ1
  have hYY : ∀ x ∈ locF 𝔭 A₀, ∀ y ∈ locF 𝔭 A₀, h (Y x) (Y y) ∈ pK K 𝔭 ((k - e) + (k - e)) :=
    fun x hx y hy => form_mem_pK hF hA₀i h𝔭 (hYA x hx) (hYA y hy)
  refine ⟨X, Subgroup.mem_inf.mpr ⟨mem_sSub.mpr ⟨hXA, fun x hx y hy => ?_⟩, hXX ▸ hX'B⟩, ?_, ?_⟩
  · have e1 : h (X x) (X y) - h x y = Z x y + h (Y x) (Y y) := by
      rw [← IA.phi_apply]
      linear_combination hphi x y
    rw [e1]
    exact add_mem (hZ.2 x hx y hy) (pK_anti 𝔭 (by omega) (hYY x hx y hy))
  · intro x y
    simp only [LinearMap.sub_apply, star_sub, IA.star_phi hs, hZ.1]
  · refine IA.sesq_scale hF h𝔭 hr' (IA.phi h X - Z) (n := k + c) (m := (k - e) + (k - e))
      (by omega) ?_
    intro x hx y hy
    rw [LinearMap.sub_apply, LinearMap.sub_apply, hphi]
    exact hYY x hx y hy

theorem relIndex_sSub_inf_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsLattice K B₀) (hB₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ c₀ : ℕ, ∀ c ≥ c₀, ∃ k₀ : ℕ, ∀ k ≥ k₀,
      sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) ≤ sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) ∧
      sesqL (locF 𝔭 B₀) 𝔭 (k + c) ≤ sesqL (locF 𝔭 A₀) 𝔭 k ∧
      (sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀)).relIndex
          (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)) =
        (hermL (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (hermL (locF 𝔭 A₀) 𝔭 k) := by
  obtain ⟨r, hr⟩ := exists_smul_le hA₀ hB₀ h𝔭
  obtain ⟨r', hr'⟩ := exists_smul_le hB₀ hA₀ h𝔭
  obtain ⟨e, he⟩ := exists_dual_bound hK hF hs hd hA₀ h𝔭
  refine ⟨2 * r, fun c hc => ⟨c + 2 * e + 2 * r' + r + r' + 1, fun k hk => ?_⟩⟩

  have hGA : ∀ {X : V ≃ₗ[K] V}, X ∈ sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) →
      X ∈ glSub (locF 𝔭 A₀) ∧ X ∈ glSub (locF 𝔭 B₀) := fun hX =>
    ⟨(mem_sSub.mp (Subgroup.mem_inf.mp hX).1).1, (Subgroup.mem_inf.mp hX).2⟩
  have hphiA : ∀ {X : V ≃ₗ[K] V}, X ∈ sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) →
      IA.phi h X ∈ hermL (locF 𝔭 A₀) 𝔭 k := by
    intro X hX
    refine ⟨fun x y => IA.star_phi hs X x y, fun x hx y hy => ?_⟩
    rw [IA.phi_apply]
    exact (mem_sSub.mp (Subgroup.mem_inf.mp hX).1).2 x hx y hy
  have hsesq : sesqL (locF 𝔭 B₀) 𝔭 (k + c) ≤ sesqL (locF 𝔭 A₀) 𝔭 k := fun s hs' =>
    IA.sesq_scale hF h𝔭 hr s (n := k) (m := k + c) (by omega) hs'
  have hHG : sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) ≤
      sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) := by
    intro X hX
    obtain ⟨hXB, hXA⟩ := Subgroup.mem_inf.mp hX
    obtain ⟨hXBgl, hXBv⟩ := mem_sSub.mp hXB
    refine Subgroup.mem_inf.mpr ⟨mem_sSub.mpr ⟨hXA, fun x hx y hy => ?_⟩, hXBgl⟩
    have := IA.sesq_scale hF h𝔭 hr (IA.phi h X) (n := k) (m := k + c) (by omega)
      (fun x hx y hy => by rw [IA.phi_apply]; exact hXBv x hx y hy) x hx y hy
    rwa [IA.phi_apply] at this
  refine ⟨hHG, hsesq, ?_⟩
  set G := sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) with hGdef
  set H := sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) with hHdef
  set HA := hermL (locF 𝔭 A₀) 𝔭 k with hHAdef
  set HB := hermL (locF 𝔭 B₀) 𝔭 (k + c) with hHBdef

  have key : ∀ X Y : G, (QuotientGroup.mk X : G ⧸ H.subgroupOf G) = QuotientGroup.mk Y ↔
      IA.phi h (X : V ≃ₗ[K] V)⁻¹ - IA.phi h (Y : V ≃ₗ[K] V)⁻¹ ∈ HB := by
    intro X Y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hX := hGA (inv_mem X.2)
    have hY := hGA (inv_mem Y.2)
    have := mul_inv_mem_iff hs (𝔭 := 𝔭) (n := k + c) hX.1 hX.2 hY.1 hY.2
    rw [inv_inv] at this
    rw [← this]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    try exact Iff.rfl
  have hmk : ∀ X : G, IA.phi h (X : V ≃ₗ[K] V)⁻¹ ∈ HA := fun X => hphiA (inv_mem X.2)
  have keyA : ∀ a b : HA, (QuotientAddGroup.mk a : HA ⧸ HB.addSubgroupOf HA) = QuotientAddGroup.mk b ↔
      (a : V →ₗ⋆[K] V →ₗ[K] K) - b ∈ HB := by
    intro a b
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
      AddSubgroup.coe_neg]
    constructor
    · intro hab
      have := HB.neg_mem hab
      rwa [neg_add_eq_sub, neg_sub] at this
    · intro hab
      have := HB.neg_mem hab
      rwa [neg_sub, sub_eq_neg_add] at this
  let f : G ⧸ H.subgroupOf G → HA ⧸ HB.addSubgroupOf HA :=
    Quotient.lift (fun X : G => (QuotientAddGroup.mk ⟨_, hmk X⟩ : HA ⧸ HB.addSubgroupOf HA))
      (fun X Y hXY => (keyA _ _).mpr ((key X Y).mp (Quotient.sound hXY)))
  have hinj : Function.Injective f := by
    intro q₁ q₂
    induction q₁ using QuotientGroup.induction_on with
    | H X =>
    induction q₂ using QuotientGroup.induction_on with
    | H Y =>
    intro hXY
    exact (key X Y).mpr ((keyA _ _).mp hXY)
  have hsurj : Function.Surjective f := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H Z =>
    obtain ⟨X, hXG, hXZ⟩ := exists_newton hK hF hs hd hA₀ hA₀i hB₀ h𝔭 hr hr' he (c := c) (k := k)
      (by omega) Z.2
    refine ⟨QuotientGroup.mk ⟨X⁻¹, inv_mem hXG⟩, ?_⟩
    show (QuotientAddGroup.mk ⟨_, hmk ⟨X⁻¹, inv_mem hXG⟩⟩ : HA ⧸ HB.addSubgroupOf HA) =
      QuotientAddGroup.mk Z
    rw [keyA]
    simpa only [inv_inv] using hXZ
  show Nat.card (G ⧸ H.subgroupOf G) = Nat.card (HA ⧸ HB.addSubgroupOf HA)
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

end Formalism.HermitianLattices.Ext.L3.D2
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem relIndex_sSub_inf (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsLattice K B₀) (hB₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ c₀ : ℕ, ∀ c ≥ c₀, ∃ k₀ : ℕ, ∀ k ≥ k₀,
      sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) ≤ sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) ∧
      (sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀)).relIndex
          (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)) *
          Ideal.absNorm 𝔭 ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) =
        Ideal.absNorm 𝔭 ^ (finrank K V ^ 2 * c + finrank K V * vd h (locF 𝔭 A₀) 𝔭) := by
  obtain ⟨c₀, hc₀⟩ := relIndex_sSub_inf_eq hK hF hs hd hA₀ hA₀i hB₀ hB₀i h𝔭
  refine ⟨c₀, fun c hc => ?_⟩
  obtain ⟨k₀, hk₀⟩ := hc₀ c hc
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hk₀ k hk
  refine ⟨h1, ?_⟩
  rw [h3]
  exact relIndex_hermL hK hF hs hd hA₀ hA₀i hB₀ hB₀i h𝔭 h2

end Formalism.HermitianLattices.Ext.L3.D2

namespace Formalism.HermitianLattices.Ext.L3

open D2

theorem local_density_ratio_holds : LocalDensityRatio := by
  intro K F _ _ _ _ _ _ hK hF V _ _ _ _ _ h A₀ B₀ 𝔭 hs hd h𝔭 hA₀ hB₀ hA₀i hB₀i
  obtain ⟨c₁, hc₁⟩ := D2.relIndex_sSub_inf hK hF hs hd hA₀ hA₀i hB₀ hB₀i h𝔭
  obtain ⟨c₂, hc₂⟩ := D2.relIndex_nSub hK hF hA₀ hB₀ h𝔭
  set c := c₁ + c₂ with hc
  obtain ⟨k₁, hk₁⟩ := hc₁ c (by omega)
  obtain ⟨k₂, hk₂⟩ := hc₂ c (by omega)
  obtain ⟨k₃, hk₃⟩ := D2.akCount_eq_relIndex hK hF hs hd hA₀ hA₀i h𝔭
  obtain ⟨k₄, hk₄⟩ := D2.akCount_eq_relIndex hK hF hs hd hB₀ hB₀i h𝔭
  obtain ⟨k₅, hk₅⟩ := D2.relIndex_inf_glSub hK hF hs hd hA₀ hA₀i hB₀ h𝔭
  obtain ⟨k₆, hk₆⟩ := D2.relIndex_inf_glSub hK hF hs hd hB₀ hB₀i hA₀ h𝔭
  obtain ⟨k₇, hk₇⟩ := D2.nSub_le_glSub hB₀ hA₀ h𝔭
  obtain ⟨k₈, hk₈⟩ := D2.alphaL_eq hK hF hs hd hA₀ hA₀i h𝔭
  obtain ⟨k₉, hk₉⟩ := D2.alphaL_eq hK hF hs hd hB₀ hB₀i h𝔭
  set k := k₁ + k₂ + k₃ + k₄ + k₅ + k₆ + k₇ + k₈ + k₉ with hk
  obtain ⟨hJI, hIJ⟩ := hk₁ k (by omega)
  obtain ⟨hNN, hNNi⟩ := hk₂ k (by omega)
  have hakA := hk₃ k (by omega)
  have hakB := hk₄ (k + c) (by omega)
  have horbAB := hk₅ k (by omega)
  have horbBA := hk₆ (k + c) (by omega)
  have hNBA := hk₇ (k + c) (by omega)
  have hαA := hk₈ k (by omega)
  have hαB := hk₉ (k + c) (by omega)
  have f1 := D2.nSub_le_sSub hF hA₀i h𝔭 k
  have f2 := D2.nSub_le_sSub hF hB₀i h𝔭 (k + c)
  have hNJ : nSub (locF 𝔭 B₀) 𝔭 (k + c) ≤ sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) :=
    le_inf f2 hNBA
  have hIS : sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) ≤ sSub h (locF 𝔭 A₀) 𝔭 k := inf_le_left
  have hJS : sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) ≤ sSub h (locF 𝔭 B₀) 𝔭 (k + c) :=
    inf_le_left
  have e1 := Subgroup.relIndex_mul_relIndex (hHK := hNN) (hKL := f1)
  have e2 := Subgroup.relIndex_mul_relIndex (hHK := hNJ) (hKL := hJI)
  have e3 := Subgroup.relIndex_mul_relIndex (hHK := hNJ.trans hJI) (hKL := hIS)
  have e4 := Subgroup.relIndex_mul_relIndex (hHK := hNJ) (hKL := hJS)
  have e5 : (nSub (locF 𝔭 A₀) 𝔭 k).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k) *
      (nSub (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (nSub (locF 𝔭 A₀) 𝔭 k) =
      (nSub (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀)) *
        ((sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀)).relIndex
            (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)) *
          (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k)) := by
    rw [mul_comm, e1, ← e3, ← e2, mul_assoc]
  have E : akCount h (locF 𝔭 A₀) 𝔭 k * Ideal.absNorm 𝔭 ^ (2 * finrank K V ^ 2 * c) *
      Ideal.absNorm 𝔭 ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) * orbCount h (locF 𝔭 B₀) (locF 𝔭 A₀) =
      akCount h (locF 𝔭 B₀) 𝔭 (k + c) * orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀) *
        Ideal.absNorm 𝔭 ^ (finrank K V ^ 2 * c + finrank K V * vd h (locF 𝔭 A₀) 𝔭) := by
    rw [hakA, hakB, ← horbAB, ← horbBA, ← hNNi, ← hIJ, ← e4, e5]
    ring
  have hQ : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    have hb : 𝔭 ≠ ⊥ :=
      Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
    exact_mod_cast fun h0 => hb (Ideal.absNorm_eq_zero_iff.mp h0)
  have Er : (akCount h (locF 𝔭 A₀) 𝔭 k : ℝ) * (Ideal.absNorm 𝔭 : ℝ) ^ (2 * finrank K V ^ 2 * c) *
      (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) *
        (orbCount h (locF 𝔭 B₀) (locF 𝔭 A₀) : ℝ) =
      (akCount h (locF 𝔭 B₀) 𝔭 (k + c) : ℝ) * (orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀) : ℝ) *
        (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V ^ 2 * c + finrank K V * vd h (locF 𝔭 A₀) 𝔭) := by
    exact_mod_cast E
  rw [hαA, hαB, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_div_iff (pow_ne_zero _ hQ) (pow_ne_zero _ hQ)]
  apply mul_right_cancel₀ (pow_ne_zero (finrank K V ^ 2 * c) hQ)
  linear_combination ((Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2)) * Er

end Formalism.HermitianLattices.Ext.L3
end
end

section
open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

def extHom (S : VecSplit h h') : (V' ≃ₗ[K] V') →* (V ≃ₗ[K] V) where
  toFun := SplitBAux.extOf S
  map_one' := by
    ext v
    obtain ⟨c, a, rfl⟩ := S.cover v
    rw [SplitBAux.extOf_apply]
    rfl
  map_mul' := by
    intro a b
    ext v
    obtain ⟨c, x, rfl⟩ := S.cover v
    rw [SplitBAux.extOf_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, SplitBAux.extOf_apply,
      SplitBAux.extOf_apply]

theorem extHom_apply (S : VecSplit h h') (g' : V' ≃ₗ[K] V') : extHom S g' = SplitBAux.extOf S g' := rfl

theorem extHom_injective (S : VecSplit h h') : Function.Injective (extHom S) := by
  intro a b e
  ext x
  apply S.inj
  rw [← SplitBAux.extOf_ι, ← SplitBAux.extOf_ι S b, ← extHom_apply, e, extHom_apply]

def autExt (S : VecSplit h h') (M : Submodule (𝓞 K) V) : Subgroup (V' ≃ₗ[K] V') :=
  (autSub h M).comap (extHom S)

def oM (S : VecSplit h h') (M : Submodule (𝓞 K) V) : ℕ :=
  (autExt S M).relIndex (autSub h' (S.cut M))

def nu {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (h₀ : W →ₗ⋆[K] W →ₗ[K] K) (A : Submodule (𝓞 K) W) (𝔭 : Ideal (𝓞 F)) : ℝ :=
  alphaL h₀ A 𝔭 / (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K W * vd h₀ A 𝔭)

def kap (S : VecSplit h h') (M : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F) (J k : ℕ) : ℝ :=
  (cnt h M 𝔭 k n (tube (autSub h M) M 𝔭 J S.x₀) : ℝ) /
    ((Ideal.absNorm 𝔭 : ℝ) ^ vd h M 𝔭 * nu h M 𝔭) * (nu h' (S.cut M) 𝔭 / (oM S M : ℝ))

theorem nu_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : 0 < nu h (locF 𝔭 A₀) 𝔭 := by
  have e : alphaL h (locF 𝔭 A₀) 𝔭 = alphaL h A₀ 𝔭 := by
    unfold alphaL
    congr 1
    ext k
    rw [akCount_locF hF h A₀ 𝔭 h𝔭]
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    exact_mod_cast reductionMapsOfForms.absNorm_pos h𝔭
  unfold nu
  rw [e]
  exact div_pos (alphaL_pos hK hF hs hd hA₀ hA₀i h𝔭) (pow_pos hq _)

theorem nu_mul_relIndex (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ B₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀)
    (hB₀ : Submodule.IsLattice K B₀) (hB₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h B₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) :
    nu h (locF 𝔭 A₀) 𝔭 * ((autSub h (locF 𝔭 A₀)).relIndex (autSub h (locF 𝔭 B₀)) : ℝ) =
      nu h (locF 𝔭 B₀) 𝔭 * ((autSub h (locF 𝔭 B₀)).relIndex (autSub h (locF 𝔭 A₀)) : ℝ) := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    exact_mod_cast reductionMapsOfForms.absNorm_pos h𝔭
  have h1 := local_density_ratio_holds K F hK hF V h A₀ B₀ 𝔭 hs hd h𝔭 hA₀ hB₀ hA₀i hB₀i
  rw [orbCount_eq_relIndex, orbCount_eq_relIndex] at h1
  unfold nu
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff (pow_pos hq _).ne' (pow_pos hq _).ne']
  linear_combination h1

theorem autExt_le (S : VecSplit h h') (M : Submodule (𝓞 K) V) :
    autExt S M ≤ autSub h' (S.cut M) := by
  intro g' hg
  obtain ⟨h1, h2⟩ : SplitBAux.extOf S g' ∈ Formalism.HermitianLatticesTheory.isom h ∧
    Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') M = M := hg
  refine ⟨fun a b => ?_, ?_⟩
  · rw [← S.isom, ← S.isom, ← SplitBAux.extOf_ι, ← SplitBAux.extOf_ι, h1]
  · rw [← StabilizerLattices.cut_gmap_extOf, h2]

theorem inf_fixS_eq_map (S : VecSplit h h') (M : Submodule (𝓞 K) V) :
    autSub h M ⊓ fixS S.x₀ = (autExt S M).map (extHom S) := by
  ext g
  constructor
  · rintro ⟨hg, hx⟩
    have hx' : g S.x₀ = S.x₀ := hx
    have e : extHom S (SplitBAux.res S g hg.1 hx') = g := by
      ext v
      obtain ⟨c, a, rfl⟩ := S.cover v
      rw [extHom_apply, SplitBAux.extOf_apply, SplitBAux.res_spec, map_add, map_smul, hx']
    refine ⟨SplitBAux.res S g hg.1 hx', ?_, e⟩
    change extHom S _ ∈ autSub h M
    rw [e]
    exact hg
  · rintro ⟨g', hg', rfl⟩
    exact ⟨hg', SplitBAux.extOf_x₀ S g'⟩

theorem relIndex_fix_eq (hs : h.IsSymm) (S : VecSplit h h') (M₁ M₂ : Submodule (𝓞 K) V) :
    (autSub h M₂ ⊓ fixS S.x₀).relIndex (autSub h M₁ ⊓ fixS S.x₀) =
      (autExt S M₂).relIndex (autExt S M₁) := by
  rw [inf_fixS_eq_map, inf_fixS_eq_map, Subgroup.relIndex_map_map_of_injective _ _ (extHom_injective S)]

theorem oM_ne_zero (hs : h.IsSymm) (S : VecSplit h h') {M₁ : Submodule (𝓞 K) V}
    (hM₁ : Submodule.IsLattice K M₁) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hx : S.x₀ ∈ locF 𝔭 M₁) : oM S (locF 𝔭 M₁) ≠ 0 := by
  have hN : Submodule.IsLattice K (S.adjoin (S.cut M₁)) :=
    (S.isLattice_adjoin_iff' _).mpr (StabilizerLattices.isLattice_cut S hM₁)
  have h1 : (autExt S (locF 𝔭 M₁)).relIndex (autExt S (locF 𝔭 (S.adjoin (S.cut M₁)))) ≠ 0 :=
    Subgroup.relIndex_comap_ne_zero (extHom S) (relIndex_autSub_ne_zero h hN hM₁ h𝔭)
  have h2 : autSub h' (S.cut (locF 𝔭 M₁)) ≤ autExt S (locF 𝔭 (S.adjoin (S.cut M₁))) := by
    rintro g' ⟨hg1, hg2⟩
    refine ⟨SplitBAux.extOf_mem_isom hs S hg1, ?_⟩
    change Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') _ = _
    rw [LocalizedFibreSets.cut_locF, LocalizedFibreSets.gmap_locF] at hg2
    rw [LocalizedFibreSets.gmap_locF, SplitBAux.gmap_extOf S g' rfl]
    have mono : ∀ T T' : Submodule (𝓞 K) V', locF 𝔭 T = locF 𝔭 T' →
        locF 𝔭 (S.adjoin T) ≤ locF 𝔭 (S.adjoin T') := by
      intro T T' e
      rw [← LocalizedFibreSets.locF_idem 𝔭 (S.adjoin T')]
      apply LocF.locF_mono
      unfold VecSplit.adjoin
      refine sup_le ((le_sup_left).trans (LocalizedFibreSets.le_locF 𝔭 _)) ?_
      rw [Submodule.map_le_iff_le_comap]
      intro a ha
      have ha' : a ∈ locF 𝔭 T' := e ▸ LocalizedFibreSets.le_locF 𝔭 T ha
      obtain ⟨s, hs, hsa⟩ := ha'
      refine ⟨s, hs, ?_⟩
      apply Submodule.mem_sup_right
      refine Submodule.mem_map.mpr ⟨s • a, hsa, ?_⟩
      exact LinearMap.map_smul_of_tower _ _ _
    exact le_antisymm (mono _ _ hg2) (mono _ _ hg2.symm)
  intro h0
  exact h1 (Subgroup.relIndex_eq_zero_of_le_right h2 h0)

theorem kap_alg {E₁ E₂ Q₁ Q₂ ν₁ ν₂ μ₁ μ₂ a b c d a' b' o₁ o₂ : ℝ} (hQ₁ : Q₁ ≠ 0) (hQ₂ : Q₂ ≠ 0)
    (hν₁ : ν₁ ≠ 0) (hν₂ : ν₂ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (ha' : a' ≠ 0)
    (ho₁ : o₁ ≠ 0) (ho₂ : o₂ ≠ 0) (h1 : E₁ * Q₂ * b * a' = E₂ * Q₁ * a * b')
    (h2 : ν₁ * b = ν₂ * a) (h3 : μ₁ * d = μ₂ * c) (h4 : a' * o₁ * d = c * o₂ * b') :
    E₁ / (Q₁ * ν₁) * (μ₁ / o₁) = E₂ / (Q₂ * ν₂) * (μ₂ / o₂) := by
  rw [div_mul_div_comm, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hQ₁ hν₁) ho₁) (mul_ne_zero (mul_ne_zero hQ₂ hν₂) ho₂)]
  apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero hb ha') ha) hd)
  linear_combination (μ₁ * d * ν₂ * a * o₂) * h1 + (E₂ * Q₁ * a * b' * ν₂ * a * o₂) * h3 -
    (E₂ * Q₁ * a * b' * μ₂ * c * o₂) * h2 - (E₂ * μ₂ * Q₁ * ν₁ * b * a) * h4

theorem kap_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h')
    {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₁i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₁) (hM₂ : Submodule.IsLattice K M₂)
    (hM₂i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F}
    (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F)) (hx₁ : S.x₀ ∈ locF 𝔭 M₁)
    (hx₂ : S.x₀ ∈ locF 𝔭 M₂) :
    ∀ᶠ J in atTop, ∀ᶠ k in atTop,
      kap S (locF 𝔭 M₁) 𝔭 n J k = kap S (locF 𝔭 M₂) 𝔭 n J k := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    exact_mod_cast reductionMapsOfForms.absNorm_pos h𝔭
  have hT₁ := StabilizerLattices.isLattice_cut S hM₁
  have hT₂ := StabilizerLattices.isLattice_cut S hM₂
  have hT₁i := UnimodularLocalization.isIntegralLat_cut S hM₁i
  have hT₂i := UnimodularLocalization.isIntegralLat_cut S hM₂i

  set P := autExt S (locF 𝔭 M₁) with hP
  set W := autExt S (locF 𝔭 M₂) with hW
  set Q := autSub h' (S.cut (locF 𝔭 M₁)) with hQ
  set R := autSub h' (S.cut (locF 𝔭 M₂)) with hR
  have hPQ : P ≤ Q := autExt_le S _
  have hWR : W ≤ R := autExt_le S _
  have ho₁ : P.relIndex Q ≠ 0 := oM_ne_zero hs S hM₁ h𝔭 hx₁
  have ho₂ : W.relIndex R ≠ 0 := oM_ne_zero hs S hM₂ h𝔭 hx₂
  have hc : R.relIndex Q ≠ 0 := by
    rw [hR, hQ, LocalizedFibreSets.cut_locF, LocalizedFibreSets.cut_locF]
    exact relIndex_autSub_ne_zero h' hT₁ hT₂ h𝔭
  have hd' : Q.relIndex R ≠ 0 := by
    rw [hR, hQ, LocalizedFibreSets.cut_locF, LocalizedFibreSets.cut_locF]
    exact relIndex_autSub_ne_zero h' hT₂ hT₁ h𝔭
  have hu : W.relIndex Q ≠ 0 := Subgroup.relIndex_ne_zero_trans ho₂ hc
  have ht : Q.relIndex W ≠ 0 := fun h0 => hd' (Subgroup.relIndex_eq_zero_of_le_right hWR h0)
  have ha' : W.relIndex P ≠ 0 := fun h0 => hu (Subgroup.relIndex_eq_zero_of_le_right hPQ h0)
  have c1 := relIndex_cocycle P Q W ha' ho₁ ht
  have c2 := relIndex_cocycle Q R W hu hd' (by rw [Subgroup.relIndex_eq_one.mpr hWR]; exact one_ne_zero)
  rw [Subgroup.relIndex_eq_one.mpr hPQ, one_mul] at c1
  rw [Subgroup.relIndex_eq_one.mpr hWR, mul_one] at c2
  have h4 : W.relIndex P * P.relIndex Q * Q.relIndex R = R.relIndex Q * W.relIndex R * P.relIndex W := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ht)
    calc Q.relIndex W * (W.relIndex P * P.relIndex Q * Q.relIndex R)
        = (P.relIndex Q * Q.relIndex W * W.relIndex P) * Q.relIndex R := by ring
      _ = (Q.relIndex R * W.relIndex Q) * P.relIndex W := by rw [← c1]; ring
      _ = _ := by rw [← c2]; ring
  have h2 := nu_mul_relIndex hK hF hs hd hM₁ hM₁i hM₂ hM₂i h𝔭
  have h3 := nu_mul_relIndex hK hF (S.isSymm hs) (S.isTotPosDef hd) hT₁ hT₁i hT₂ hT₂i h𝔭
  rw [← LocalizedFibreSets.cut_locF, ← LocalizedFibreSets.cut_locF, ← hQ, ← hR] at h3
  filter_upwards [pair hK hF hs hd hM₁ hM₁i hM₂ hM₂i h𝔭 hn hx hx₁ hx₂] with J hJ
  filter_upwards [hJ] with k hk
  rw [relIndex_fix_eq hs, relIndex_fix_eq hs, ← hP, ← hW] at hk
  unfold kap oM
  rw [← hP, ← hW, ← hQ, ← hR]
  refine kap_alg (pow_pos hq _).ne' (pow_pos hq _).ne'
    (nu_pos hK hF hs hd hM₁ hM₁i h𝔭).ne' (nu_pos hK hF hs hd hM₂ hM₂i h𝔭).ne'
    (a := ((autSub h (locF 𝔭 M₂)).relIndex (autSub h (locF 𝔭 M₁)) : ℝ))
    (b := ((autSub h (locF 𝔭 M₁)).relIndex (autSub h (locF 𝔭 M₂)) : ℝ))
    (c := (R.relIndex Q : ℝ)) (d := (Q.relIndex R : ℝ)) (a' := (W.relIndex P : ℝ))
    (b' := (P.relIndex W : ℝ)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ h2 h3 ?_
  · exact_mod_cast relIndex_autSub_ne_zero h hM₁ hM₂ h𝔭
  · exact_mod_cast relIndex_autSub_ne_zero h hM₂ hM₁ h𝔭
  · exact_mod_cast hd'
  · exact_mod_cast ha'
  · exact_mod_cast ho₁
  · exact_mod_cast ho₂
  · exact_mod_cast hk
  · exact_mod_cast h4

end Formalism.HermitianLattices.Ext.L3.LIOrb
end
end
