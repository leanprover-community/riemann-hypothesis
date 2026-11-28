module

import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import TauCeti.Algebra.Module.ZMod.Extend
import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Universal
import TauCeti.RepresentationTheory.Induction.Artin.Spanning
public import Lib.ClassField.GaloisCohomology.ContinuousCocycles

/-!
# Higman's criterion, dévissage and multiplicative functions on finite modules (Cartan map)

Tools that reduce a statement about finite `l`-power-torsion discrete `G`-modules to simple cases;
they serve the inequality of local duality (`Lib.ClassField.LocalDuality.DualityInequality`) and the
cocycle counts of `Lib.ClassField.GreenbergWiles.CocycleCounts`.

* `New.DiscreteModule.IsHigmanProjective`: Higman's criterion, some additive `τ` has `∑ g τ g⁻¹ = 1`
  over `G ⧸ Q`.
* `New.DiscreteModule.FiniteKilledFixedInj`: the module is finite, killed by `n` and fixed by `Q`,
  and `ρ z - m` is injective on it.
* `New.DiscreteModule.diagonalPermModule`: the functions `Y → A` with the diagonal action of `G`.
* `New.DiscreteModule.devissage_induction`: dévissage to modules killed by `l` and fixed by a normal
  subgroup `P`.
* `New.DiscreteModule.exists_open_sylow`: an open `P ≥ U` of index prime to `l` whose elements have
  an `l`-power power in `U`.
* `New.DiscreteModule.IsMultiplicative.eq_one_of_eq_one_on_isHigmanProjective`: on the finite
  modules killed by `l` and fixed by `U` with `ρ z - 1` injective, `z` central modulo `U`, a
  function with values in `ℚ≥0` that is multiplicative in short exact sequences is `1` as soon as it
  is `1` on the modules with Higman's property.

Notions from other files:
* `New.DiscreteModule R G`: an `R`-module with the discrete topology and a continuous `R`-linear
  action `ρ` of the topological group `G`.

## Relation to the literature

Known result: The Cartan map has finite cokernel. It is stated for multiplicative functions with
nonnegative rational values on finite modules killed by a prime on which one element, central modulo
the level, fixes no nonzero vector, with projectivity read as Higman's property. The reduction
uses modular Artin induction on a finite quotient.
Source: J.-P. Serre, Linear Representations of Finite Groups (1977), Thm 35; for the route by
induction from cyclic subgroups in the local Euler characteristic formula, Milne, Arithmetic Duality
Theorems, I 2.10-2.12.
-/

@[expose] public section

namespace New.DiscreteModule

open MulAction Equiv QuotientGroup Finset Finite Submonoid Function commutatorElement Subgroup
  Module.End Fintype

attribute [local instance low] Fintype.ofFinite

variable {R G : Type} [CommRing R] [Group G] [TopologicalSpace G]

/-! ### Finite modules, Higman's criterion and function modules -/

/-- Higman's criterion for the discrete `G`-module `A` relative to a subgroup `Q` of finite index:
some additive `τ : A → A` has `∑ g τ g⁻¹ = 1`, summed over the chosen representatives `g.out` of the
cosets in `G ⧸ Q`. The map `τ` is not asked to commute with `Q`. If `Q` acts trivially on `A`, the
choice of representatives does not matter. -/
def IsHigmanProjective (Q : Subgroup G) [Finite (G ⧸ Q)] (A : DiscreteModule R G) : Prop :=
  ∃ τ : A →+ A, ∀ a : A.V, ∑ g : G ⧸ Q, A.ρ g.out (τ (A.ρ g.out⁻¹ a)) = a

/-- The subgroup `Q` of `G` acts trivially on the discrete `G`-module `A`. -/
abbrev TrivialOn (Q : Subgroup G) (A : DiscreteModule R G) : Prop := ∀ g ∈ Q, ∀ m : A.V, A.ρ g m = m

/-- For a discrete `G`-module `A` and a finite set `Y` with an action of a discrete group `Δ`, the
`G × Δ`-module of functions `f : Y → A`, with `((g, δ) f) x = g (f (δ⁻¹ x))`. -/
abbrev permModule (A : DiscreteModule R G) {Δ : Type} [Group Δ] [TopologicalSpace Δ]
    [DiscreteTopology Δ] (Y : Type) [Finite Y] [MulAction Δ Y] : DiscreteModule R (G × Δ) :=
  of (V := Y → A)
    { toFun g := LinearMap.pi fun x : Y ↦ A.ρ g.1 ∘ₗ LinearMap.proj (g.2⁻¹ • x)
      map_one' := by aesop
      map_mul' := by aesop (add simp mul_smul) }

/-- The discrete `G`-module `A` is finite and killed by `n`, the subgroup `Q` acts trivially on it,
and `ρ z - m` is injective on it. -/
structure FiniteKilledFixedInj (n : ℕ) (Q : Subgroup G) (z : G) (m : ℕ) (A : DiscreteModule R G) :
    Prop where
  /-- The module is finite. -/
  finite : Finite A
  /-- The module is killed by `n`. -/
  nsmul_eq_zero : ∀ a : A, n • a = 0
  /-- The subgroup `Q` acts trivially. -/
  trivialOn : A.TrivialOn Q
  /-- The endomorphism `ρ z - m` is injective. -/
  injective : Injective ⇑(A.ρ z - m)

section FiniteKilledFixedInj
variable {n : ℕ} {Q : Subgroup G} {z : G} {m : ℕ}

private lemma FiniteKilledFixedInj.of_injective {A B : DiscreteModule R G} (ι : A.Hom B)
    (hι : Injective ι) (hB : B.FiniteKilledFixedInj n Q z m) : A.FiniteKilledFixedInj n Q z m := by
  obtain ⟨h_fin, h_killed, h_triv, h_inj⟩ := hB
  refine ⟨Finite.of_injective ι hι, fun a ↦ hι ?_, fun g hg a ↦ hι ?_, fun a b hab ↦ ?_⟩
  · simp [h_killed]
  · simp [ι.isIntertwining, h_triv g hg]
  · refine hι (h_inj (?_ : (B.ρ z - m) (ι a) = (B.ρ z - m) (ι b)))
    simpa [ι.isIntertwining] using congrArg ι hab

/-- Being finite, killed by `n`, fixed by `Q` and with `ρ z - m` injective passes from the middle
term `B` of a short exact sequence `0 → A → B → M → 0` to `A`. -/
lemma FiniteKilledFixedInj.left_of_isShortExact {A B M : DiscreteModule R G} {ι : A.Hom B}
    {π : B.Hom M} (h_exact : IsShortExact ι π) (hB : B.FiniteKilledFixedInj n Q z m) :
    A.FiniteKilledFixedInj n Q z m :=
  hB.of_injective ι h_exact.1

/-- Being finite, killed by `n`, fixed by `Q` and with `ρ z - m` injective passes from the middle
term `B` of a short exact sequence `0 → A → B → M → 0` to `M`. -/
lemma FiniteKilledFixedInj.right_of_isShortExact {A B M : DiscreteModule R G} {ι : A.Hom B}
    {π : B.Hom M} (h_exact : IsShortExact ι π) (hB : B.FiniteKilledFixedInj n Q z m) :
    M.FiniteKilledFixedInj n Q z m := by
  -- test the properties of `M` on the image of the surjective `π`
  obtain ⟨h_fin, h_killed, h_triv, h_inj⟩ := hB
  obtain ⟨-, -, π_surj⟩ := h_exact
  have hM : Finite M := of_surjective π π_surj
  refine ⟨hM, π_surj.forall.2 fun b ↦ ?_, fun g hg ↦ π_surj.forall.2 fun b ↦ ?_,
    injective_iff_surjective.2 (π_surj.forall.2 fun b ↦ ?_)⟩
  · rw [← map_nsmul, h_killed, map_zero]
  · rw [← π.isIntertwining, h_triv g hg]
  · -- on finite modules injective means surjective, which passes from `B` to `M`
    obtain ⟨c, rfl⟩ : ∃ c : B, (B.ρ z - m) c = b := injective_iff_surjective.1 h_inj b
    exact ⟨π c, by simp [← π.isIntertwining]⟩

end FiniteKilledFixedInj

/-- Let `Q` have finite index in `G`. If `A` is killed by an integer `n` prime to the index of `Q`,
then `A` satisfies Higman's criterion relative to `Q`. -/
lemma isHigmanProjective_of_coprime_index {n : ℕ} {Q : Subgroup G} [Finite (G ⧸ Q)]
    {A : DiscreteModule R G} (h_killed : ∀ a : A, n • a = 0) (h_coprime : n.Coprime Q.index) :
    A.IsHigmanProjective Q := by
  -- with `a * n + b * [G : Q] = 1`, take `b` times the identity; `n` kills `A`
  obtain ⟨a, b, bezout⟩ : ∃ a b : ℤ, a * n + b * Q.index = 1 := h_coprime.isCoprime
  refine ⟨b • AddMonoidHom.id A, fun x ↦ ?_⟩
  have h_smul : (a * n + b * Q.index) • x = x := by rw [bezout, one_smul]
  simpa [add_smul, mul_smul, h_killed, mul_comm b, Subgroup.index] using h_smul

/-- Let `Q` have finite index in `G`, and let `A` be finite, killed by `n` and fixed by `Q`, with
`ρ z - m` injective. If `n` is prime to the index of `Q`, then `A` satisfies Higman's criterion
relative to `Q`. -/
lemma FiniteKilledFixedInj.isHigmanProjective_of_coprime {n : ℕ} {Q : Subgroup G} [Finite (G ⧸ Q)]
    {z : G} {m : ℕ} {A : DiscreteModule R G} (hA : A.FiniteKilledFixedInj n Q z m)
    (h_coprime : n.Coprime Q.index) : A.IsHigmanProjective Q :=
  isHigmanProjective_of_coprime_index hA.nsmul_eq_zero h_coprime

/-! ### Dévissage and Sylow subgroups -/

/-- Dévissage. Let `l` be prime, `n = l ^ j`, and let `p` be a property of the modules that are
finite, killed by `n`, fixed by `Q` and on which `ρ z - m` is injective. Let `P` be a normal
subgroup each of whose elements `g` has a power `g ^ l ^ i` in `Q`. If `p` holds for the modules
that are also killed by `l` and fixed by `P`, and is stable under extensions, then it always
holds. -/
@[elab_as_elim]
lemma devissage_induction {l n : ℕ} [hl : Fact l.Prime] {z : G} {m j : ℕ} (hn : l ^ j = n)
    (P Q : Subgroup G) [P.Normal]
    {p : ∀ A : DiscreteModule R G, FiniteKilledFixedInj n Q z m A → Prop}
    (h_pow : ∀ g ∈ P, ∃ i : ℕ, g ^ l ^ i ∈ Q)
    (h_base : ∀ (A : DiscreteModule R G) (hA : FiniteKilledFixedInj n Q z m A),
      FiniteKilledFixedInj l P z m A → p A hA)
    (h_ext : ∀ {A B C : DiscreteModule R G} {ι : Hom A B} {π : Hom B C}
      (h_exact : IsShortExact ι π) (hB : FiniteKilledFixedInj n Q z m B),
      p A (hB.left_of_isShortExact h_exact) → p C (hB.right_of_isShortExact h_exact) → p B hB) :
    ∀ (B : DiscreteModule R G) (hB : FiniteKilledFixedInj n Q z m B), p B hB := by
  -- Induction on the length of `B`. If `B ≠ 0`, the submodule `W` of the vectors fixed by `P` and
  -- killed by `l` is not zero; `W` is a base case, `B ⧸ W` is shorter, and `B` is their extension.
  subst hn
  refine (wellFounded_lt.onFun (f := fun B : DiscreteModule R G ↦ Module.length R B)).fix ?_
  intro B ih ⟨h_fin, h_killed, h_triv, h_inj⟩
  have h_group : IsPGroup l (Multiplicative B) := fun x ↦ ⟨j, h_killed x⟩
  obtain h_one | h_dvd := h_group.card_eq_or_dvd
  · -- The zero module is a base case.
    have : Subsingleton B := card_le_one_iff_subsingleton.1 h_one.le
    exact h_base B _ ⟨h_fin, fun _ ↦ Subsingleton.elim .., fun _ _ _ ↦ Subsingleton.elim .., h_inj⟩
  -- `P` acts through an `l`-group, as `Q` acts trivially. So `l` divides the number of fixed
  -- vectors, and by Cauchy's theorem one of them, `b`, has order `l`.
  have h_image : IsPGroup l (P.map B.ρ.toHomUnits) := by
    rintro ⟨_, g, hg, rfl⟩
    obtain ⟨i, hi⟩ := h_pow g hg
    exact ⟨i, by simp [Subtype.ext_iff, Units.ext_iff, LinearMap.ext_iff, ← map_pow, h_triv _ hi]⟩
  have h_fixed : l ∣ Nat.card (FixedPoints.addSubgroup (P.map B.ρ.toHomUnits) B) :=
    ((h_image.card_modEq_card_fixedPoints B).dvd_iff dvd_rfl).1 h_dvd
  obtain ⟨⟨b, hb_fixed⟩, hb_order⟩ := exists_prime_addOrderOf_dvd_card' l h_fixed
  rw [AddSubgroup.addOrderOf_mk] at hb_order
  let W : Submodule R B := (B.restrictTo P).H0 ⊓ (l • LinearMap.id : B →ₗ[R] B).ker
  have mem_W {x : B} : x ∈ W ↔ (∀ g : P, B.ρ g x = x) ∧ l • x = 0 := Iff.rfl
  -- `W` is stable under `G` because `P` is normal.
  have hW_stable (g : G) : W ≤ W.comap (B.ρ g) := fun x hx ↦
    mem_W.2 ⟨B.ρ.le_comap_invariants P g (mem_W.1 hx).1, by simp [← map_nsmul, (mem_W.1 hx).2]⟩
  have hW_base : (B.submodule W hW_stable).FiniteKilledFixedInj l P z m :=
    ⟨inferInstance, fun x ↦ Subtype.ext (mem_W.1 x.property).2,
      fun g hg x ↦ Subtype.ext ((mem_W.1 x.property).1 ⟨g, hg⟩),
      fun x y hxy ↦ Subtype.ext (h_inj (by simpa using Subtype.ext_iff.1 hxy))⟩
  have hb_mem : b ∈ W :=
    mem_W.2 ⟨fun g ↦ hb_fixed ⟨_, P.mem_map_of_mem _ g.property⟩, by simp [← hb_order]⟩
  have hb_ne : b ≠ 0 := fun hb ↦ hl.out.ne_one (by rw [← hb_order, hb, addOrderOf_zero])
  exact h_ext (B.isShortExact_submodule W hW_stable) _ (h_base _ _ hW_base)
    (ih _ (W.length_quotient_lt (W.ne_bot_iff.2 ⟨b, hb_mem, hb_ne⟩)) _)

/-- For a prime `l` and `U` open normal in a compact group there is an open subgroup `P ≥ U` of
index prime to `l` each of whose elements `g` has a power `g ^ l ^ k` in `U`. -/
lemma exists_open_sylow (l : ℕ) [hl : Fact l.Prime] (U : OpenNormalSubgroup G)
    [IsTopologicalGroup G] [CompactSpace G] :
    ∃ P : OpenSubgroup G,
      (U : Subgroup G) ≤ P ∧ l.Coprime P.toSubgroup.index ∧ ∀ g ∈ P, ∃ k : ℕ, g ^ l ^ k ∈ U := by
  -- `P` is the preimage in `G` of a Sylow `l`-subgroup `T` of the finite quotient `G ⧸ U`; the
  -- image of `g ∈ P` lies in that `l`-group, so it is killed by a power of `l`.
  obtain ⟨T⟩ : Nonempty (Sylow l (G ⧸ (U : Subgroup G))) := Sylow.nonempty
  let P : Subgroup G := T.toSubgroup.comap (mk' (U : Subgroup G))
  have hU_le : (U : Subgroup G) ≤ P := le_comap_mk' (U : Subgroup G) T.toSubgroup
  refine ⟨⟨P, isOpen_mono hU_le U.toOpenSubgroup.isOpen⟩, hU_le, ?_, fun g hg ↦ ?_⟩
  · simp [P, T.not_dvd_index, T.index_comap, hl.out.coprime_iff_not_dvd]
  · obtain ⟨k, hk⟩ := T.isPGroup ⟨g, hg⟩
    exact ⟨k, (eq_one_iff _).1 (by simpa [Subtype.ext_iff] using hk)⟩

/-! ### Function modules and multiplicative functions -/

/-- Let `U` be open normal in `G`, let `S` be normal in `G ⧸ U` and let `Y` be a finite
`(G ⧸ U) ⧸ S`-set. The `G`-module of functions `f : Y → A` with the diagonal action
`(g f) y = g (f (g⁻¹ y))`, where `g` acts on `Y` through its image in `(G ⧸ U) ⧸ S`. -/
abbrev diagonalPermModule [IsTopologicalGroup G] (A : DiscreteModule R G)
    (U : OpenNormalSubgroup G) (S : Subgroup (G ⧸ (U : Subgroup G))) [S.Normal] (Y : Type)
    [Finite Y] [MulAction ((G ⧸ (U : Subgroup G)) ⧸ S) Y] : DiscreteModule R G :=
  letI : MulAction (G ⧸ (U : Subgroup G)) Y := compHom Y (mk' S)
  (A.permModule Y).restrictAlong ⟨(MonoidHom.id G).prod (mk' (U : Subgroup G)),
    Continuous.prodMk continuous_id continuous_mk⟩

/-- Let `l` be prime, `U` open normal in the compact group `G`, and suppose every commutator
`⁅z, g⁆` lies in `U`. Then `G ⧸ U` has a normal subgroup of order prime to `l` that contains the
image of some power `z ^ l ^ j`. -/
lemma exists_normal_pow_mem_not_dvd_card (l : ℕ) [hl : Fact l.Prime] (U : OpenNormalSubgroup G)
    {z : G} [IsTopologicalGroup G] [CompactSpace G] (hz_central : ∀ g : G, ⁅z, g⁆ ∈ U) :
    ∃ (S : Subgroup (G ⧸ (U : Subgroup G))) (j : ℕ),
      S.Normal ∧ (z : G ⧸ (U : Subgroup G)) ^ l ^ j ∈ S ∧ ¬l ∣ Nat.card S := by
  -- The image of `z` in `G ⧸ U` has order `l ^ j * n` with `n` prime to `l`. Its power `z ^ l ^ j`
  -- generates a central subgroup `S` of order `n`.
  obtain ⟨j, n, hn, h_order⟩ :
      ∃ j n : ℕ, ¬l ∣ n ∧ orderOf (z : G ⧸ (U : Subgroup G)) = l ^ j * n :=
    WfDvdMonoid.max_power_factor (orderOf_pos _).ne' hl.out
  let S : Subgroup (G ⧸ (U : Subgroup G)) := zpowers (z ^ l ^ j)
  have hS_card : Nat.card S = n := by
    simp [S, Fintype.card_zpowers, orderOf_pow, h_order, hl.out.pos]
  have central (g : G) : Commute (z : G ⧸ (U : Subgroup G)) g :=
    commutatorElement_eq_one_iff_commute.1 ((eq_one_iff _).2 (hz_central g))
  refine ⟨S, j, ⟨?_⟩, mem_zpowers _, by rwa [hS_card]⟩
  rintro _ ⟨i, rfl⟩ ⟨g⟩
  exact ⟨i, eq_mul_inv_of_mul_eq (((central g).pow_left _).zpow_left i)⟩

/-- Let `l` be prime and let `A` be finite, killed by `l` and fixed by `U`, with `ρ z - 1`
injective. If `S` contains the image of a power `z ^ l ^ j`, the functions `Y → A` on a finite
`(G ⧸ U) ⧸ S`-set `Y`, with the diagonal action of `G`, have the same properties. -/
lemma FiniteKilledFixedInj.diagonalPermModule [IsTopologicalGroup G] {l : ℕ} [hl : Fact l.Prime]
    {U : OpenNormalSubgroup G} {z : G} {A : DiscreteModule R G}
    (hA : A.FiniteKilledFixedInj l U z 1) {S : Subgroup (G ⧸ (U : Subgroup G))} [S.Normal] {j : ℕ}
    (hz_mem : (z : G ⧸ (U : Subgroup G)) ^ l ^ j ∈ S) (Y : Type) [Finite Y]
    [MulAction ((G ⧸ (U : Subgroup G)) ⧸ S) Y] :
    (A.diagonalPermModule U S Y).FiniteKilledFixedInj l U z 1 := by
  obtain ⟨h_fin, h_killed, h_triv, h_inj⟩ := hA
  let B : DiscreteModule R G := A.diagonalPermModule U S Y
  refine ⟨Pi.finite, fun f ↦ funext fun y ↦ h_killed (f y), fun g hg f ↦ funext fun y ↦ ?_,
    (injective_iff_map_eq_zero _).2 fun f hf ↦ funext fun y ↦ ?_⟩
  · simpa [(eq_one_iff g).2 hg] using h_triv g hg (f y)
  · -- A function fixed by `z` is fixed by `z ^ l ^ j`, which acts trivially on `Y`.
    have hf_fixed : B.ρ z f = f := by simpa [B, sub_eq_zero] using hf
    have h_fixed : B.ρ (z ^ l ^ j) f = f := by simp [pow_apply_eq_iterate, iterate_fixed hf_fixed]
    have h_value : (A.ρ z ^ l ^ j) (f y) = f y := by
      simpa [B, (eq_one_iff _).2 hz_mem, compHom_smul_def] using congrFun h_fixed y
    -- As `l` kills `A`, `z ^ l ^ j - 1` acts as `(z - 1) ^ l ^ j`, which is injective.
    have frobenius (x : A) : (A.ρ z ^ l ^ j) x = ((A.ρ z - 1) ^ l ^ j) x + x := by
      simpa [h_killed] using LinearMap.congr_fun
        ((Commute.one_right (A.ρ z - 1)).add_pow_prime_pow_eq hl.out j) x
    exact iterate_injective h_inj (l ^ j) (a₂ := 0) (by simpa [frobenius] using h_value)

open scoped Classical in
/-- Let the prime `l` kill `A` and not divide the order of `S`. The functions `Y → A` on a finite
`(G ⧸ U) ⧸ S`-set `Y`, with the diagonal action of `G`, satisfy Higman's criterion relative to `U`
if some `a : Y → ZMod l` has `∑ g, a (g⁻¹ • y) = 1` for every `y`, the sum running over
`(G ⧸ U) ⧸ S`. -/
lemma isHigmanProjective_diagonalPermModule [IsTopologicalGroup G] [CompactSpace G] {l : ℕ}
    [Fact l.Prime] {U : OpenNormalSubgroup G} {A : DiscreteModule R G}
    (h_killed : ∀ x : A, l • x = 0) {S : Subgroup (G ⧸ (U : Subgroup G))} [S.Normal]
    (hS_card : ¬l ∣ Nat.card S) {Y : Type} [Finite Y] [MulAction ((G ⧸ (U : Subgroup G)) ⧸ S) Y]
    (a : Y → ZMod l) (h_sum : ∀ y : Y, ∑ g : (G ⧸ (U : Subgroup G)) ⧸ S, a (g⁻¹ • y) = 1) :
    (A.diagonalPermModule U S Y).IsHigmanProjective U := by
  -- Higman's map multiplies the value at `y` by `a y / #S`. In the sum of its conjugates over
  -- `G ⧸ U` each coset of `S` occurs `#S` times, so the sum is the trace of `a`, which is `1`.
  let : Module (ZMod l) A := AddCommGroup.zmodModule h_killed
  let : MulAction (G ⧸ (U : Subgroup G)) Y := compHom Y (mk' S)
  refine ⟨.pi fun y ↦ (a y / Nat.card S) • Pi.evalAddMonoidHom (fun _ ↦ A) y,
    fun f ↦ funext fun y ↦ ?_⟩
  have h_trace : ∑ g : G ⧸ (U : Subgroup G), a (g⁻¹ • y) = Nat.card S :=
    calc _ = ∑ p : ((G ⧸ (U : Subgroup G)) ⧸ S) × S, a (p.1⁻¹ • y) :=
          S.groupEquivQuotientProdSubgroup.sum_comp fun p ↦ a (p.1⁻¹ • y)
      _ = Nat.card S := by simp [sum_prod_type_right, h_sum y]
  have h_card_ne : (Nat.card S : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  simp [-Nat.card_eq_fintype_card, ZMod.map_smul, ← sum_smul, ← sum_div, h_trace, h_card_ne]

/-- If `z` is central modulo `U`, a module satisfying `FiniteKilledFixedInj l U z 1` embeds by
constants in another such module satisfying Higman's criterion. The inclusion and quotient form
a short exact sequence. -/
lemma FiniteKilledFixedInj.exists_shortExact_higmanProjective [IsTopologicalGroup G]
    [CompactSpace G] {l : ℕ} [Fact l.Prime] {U : OpenNormalSubgroup G}
    {z : G} {A : DiscreteModule R G}
    (hA : A.FiniteKilledFixedInj l U z 1) (hz_central : ∀ g : G, ⁅z, g⁆ ∈ U) :
    ∃ (B C : DiscreteModule R G) (ι : A.Hom B) (π : B.Hom C),
      IsShortExact ι π ∧ B.FiniteKilledFixedInj l U z 1 ∧ B.IsHigmanProjective U := by
  classical
  obtain ⟨S, j, hS, hz, hS_card⟩ := exists_normal_pow_mem_not_dvd_card l U hz_central
  let Δ := (G ⧸ (U : Subgroup G)) ⧸ S
  let B := A.diagonalPermModule U S Δ
  let ι : A.Hom B := ⟨LinearMap.const, fun _ ↦ rfl⟩
  let W := ι.toLinearMap.range
  let C := B.quotient W ι.range.apply_mem_toSubmodule
  refine ⟨B, C, ι, ⟨W.mkQ, fun _ ↦ rfl⟩,
    ⟨const_injective, ι.toLinearMap.exact_map_mkQ_range, W.mkQ_surjective⟩,
    hA.diagonalPermModule hz Δ, ?_⟩
  exact isHigmanProjective_diagonalPermModule hA.nsmul_eq_zero hS_card (Pi.single (1 : Δ) 1)
    fun y ↦ by simp [inv_mul_eq_one, Pi.single_apply]

/-- A function `φ` of the modules that are finite, killed by `n` and fixed by `Q`, with `ρ z - m`
injective, is multiplicative: `φ B = φ A * φ D` for every short exact `0 → A → B → D → 0` with `B`
of this kind. -/
def IsMultiplicative {n : ℕ} {Q : Subgroup G} {z : G} {m : ℕ}
    (φ : ∀ A : DiscreteModule R G, A.FiniteKilledFixedInj n Q z m → ℚ≥0) : Prop :=
  ∀ {A B D : DiscreteModule R G} {ι : A.Hom B} {π : B.Hom D} (h_exact : IsShortExact ι π)
    (hB : B.FiniteKilledFixedInj n Q z m),
    φ B hB = φ A (hB.left_of_isShortExact h_exact) * φ D (hB.right_of_isShortExact h_exact)

section Multiplicative
variable {l : ℕ} {U : OpenNormalSubgroup G} {z : G} [IsTopologicalGroup G] [CompactSpace G]
  {φ : ∀ A : DiscreteModule R G, A.FiniteKilledFixedInj l U z 1 → ℚ≥0}

/-- Let `φ` be a function of the modules that are finite, killed by `l` and fixed by `U`, with
`ρ z - 1` injective. If `φ` is multiplicative in short exact sequences and `1` on the modules with
Higman's property relative to `U`, then it takes the same value on isomorphic modules. -/
lemma apply_eq_of_equiv (h_mul : IsMultiplicative φ)
    (h_higman : ∀ {B : DiscreteModule R G} (hB : B.FiniteKilledFixedInj l U z 1),
      B.IsHigmanProjective U → φ B hB = 1)
    {A B : DiscreteModule R G} {hA : A.FiniteKilledFixedInj l U z 1}
    {hB : B.FiniteKilledFixedInj l U z 1} (u : A.ρ.Equiv B.ρ) : φ A hA = φ B hB := by
  -- `0 → Z → A → B → 0` is short exact for the zero module `Z`, which has Higman's property
  let Z : DiscreteModule R G := of (V := Unit) 1
  have h_exact : IsShortExact (0 : Z.Hom A) u.toIntertwiningMap :=
    ⟨injective_of_subsingleton _, fun a ↦ by simp, u.surjective⟩
  rw [h_mul h_exact hA, h_higman (hA.left_of_isShortExact h_exact) ⟨0, fun _ ↦ rfl⟩, one_mul]

end Multiplicative

section ArtinInduction

open CategoryTheory Representation TauCeti
open scoped MonoidAlgebra

noncomputable section

section HomModules

variable [IsTopologicalGroup G]
  {l : ℕ} [Fact l.Prime] {U : OpenNormalSubgroup G} {z : G}
  {A : DiscreteModule R G} {S : Subgroup (G ⧸ (U : Subgroup G))} [S.Normal]

local notation "Δ" => (G ⧸ (U : Subgroup G)) ⧸ S

-- The maps from a representation of the finite quotient to `A` have the diagonal `G`-action.
private abbrev homModule (hA : A.TrivialOn U) (M : FDRep (ZMod l) Δ) : DiscreteModule R G :=
  let A' := QuotientGroup.lift (U : Subgroup G) A.ρ fun g hg ↦ LinearMap.ext (hA g hg)
  let ρ : Representation R (G ⧸ (U : Subgroup G)) (M →+ A) :=
    { toFun g :=
        { toFun f := (A' g).toAddMonoidHom.comp (f.comp (M.ρ (mk' S g⁻¹)).toAddMonoidHom)
          map_add' := fun f e ↦ AddMonoidHom.ext fun x ↦ by simp
          map_smul' := fun r f ↦ AddMonoidHom.ext fun x ↦ by simp }
      map_one' := by ext f x; simp
      map_mul' := fun g h ↦ by ext f x; simp [mul_inv_rev] }
  let : TopologicalSpace (M →+ A) := ⊥
  let : DiscreteTopology (M →+ A) := ⟨rfl⟩
  of (V := M →+ A) (ρ.comp (mk' (U : Subgroup G))) (by
    rw [continuous_prod_of_discrete_right]
    intro f
    exact (continuous_of_discreteTopology (f := fun g ↦ ρ g f)).comp continuous_mk)

private lemma homModule_apply (hA : A.TrivialOn U) (M : FDRep (ZMod l) Δ) (g : G)
    (f : homModule hA M) (x : M) :
    (homModule hA M).ρ g f x = A.ρ g (f (M.ρ (mk' S (g⁻¹ : G)) x)) := rfl

-- Precomposition by an equivariant linear map is equivariant for the diagonal action.
private def homModuleMap (hA : A.TrivialOn U) {M N : FDRep (ZMod l) Δ} (f : M ⟶ N) :
    (homModule hA N).Hom (homModule hA M) :=
  ⟨{ toFun x := x.comp f.hom.hom.hom.toAddMonoidHom
     map_add' := fun _ _ ↦ rfl
     map_smul' := fun _ _ ↦ rfl },
   fun g ↦ LinearMap.ext fun x ↦ AddMonoidHom.ext fun m ↦ by
     have h := congrArg (fun a : M.V ⟶ N.V ↦ a.hom.hom m) (f.comm (mk' S (g⁻¹ : G)))
     exact congrArg (fun y ↦ A.ρ g (x y)) h.symm⟩

private lemma homModule_shortExact (hA : A.TrivialOn U) {T : ShortComplex (FDRep (ZMod l) Δ)}
    (hT : T.ShortExact) : IsShortExact (homModuleMap hA T.g) (homModuleMap hA T.f) := by
  let F := Action.forget (FGModuleCat (ZMod l)) Δ ⋙ forget₂ _ (ModuleCat (ZMod l))
  have h := hT.map_of_exact F
  have hi : Injective T.f.hom.hom.hom := (ModuleCat.mono_iff_injective _).mp h.mono_f
  have hp : Surjective T.g.hom.hom.hom := (ModuleCat.epi_iff_surjective _).mp h.epi_g
  have hex : Function.Exact T.f.hom.hom.hom T.g.hom.hom.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h.exact
  have killed (N : FDRep (ZMod l) Δ) (x : N) : l • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod l), ZMod.natCast_self, zero_smul]
  refine ⟨fun f e he ↦ AddMonoidHom.ext (hp.forall.2 fun y ↦ DFunLike.congr_fun he y),
    hex.compHom' (killed T.X₃), fun x ↦ ?_⟩
  exact AddMonoidHom.exists_comp_eq_of_injective (killed T.X₂) hi x

private lemma homModule_finiteKilledFixedInj (hA : A.FiniteKilledFixedInj l U z 1) {j : ℕ}
    (hz : (z : G ⧸ (U : Subgroup G)) ^ l ^ j ∈ S) (M : FDRep (ZMod l) Δ) :
    (homModule hA.trivialOn M).FiniteKilledFixedInj l U z 1 := by
  let : Finite M := Module.finite_of_finite (ZMod l)
  let : MulAction Δ M :=
    { smul := fun g x ↦ M.ρ g x
      one_smul := fun x ↦ LinearMap.congr_fun M.ρ.map_one x
      mul_smul := fun g h x ↦ LinearMap.congr_fun (M.ρ.map_mul g h) x }
  let ev : (homModule hA.trivialOn M).Hom (A.diagonalPermModule U S M) :=
    ⟨{ toFun f := f, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }, fun _ ↦ rfl⟩
  exact (hA.diagonalPermModule hz M).of_injective ev DFunLike.coe_injective

-- An additive map out of a permutation module is determined by its values on the basis.
private def homModulePermEquiv (hA : A.FiniteKilledFixedInj l U z 1)
    (Y : Type) [Finite Y] [MulAction Δ Y] :
    (homModule hA.trivialOn (FDRep.of (ofMulAction (ZMod l) Δ Y))).ρ.Equiv
      (A.diagonalPermModule U S Y).ρ := by
  let : Module (ZMod l) A := AddCommGroup.zmodModule hA.nsmul_eq_zero
  let b := MonoidAlgebra.basis Y (ZMod l)
  let e : ((ZMod l)[Y] →+ A) →ₗ[R] (Y → A) :=
    { toFun f y := f (b y)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have he : Bijective e := by
    exact ⟨fun f g h ↦ AddMonoidHom.toZModLinearMap_injective l (b.ext fun y ↦ congrFun h y),
      fun f ↦ ⟨(b.constr (ZMod l) f).toAddMonoidHom, funext (b.constr_basis (ZMod l) f)⟩⟩
  refine .mk (LinearEquiv.ofBijective e he) fun g ↦ LinearMap.ext fun f ↦ funext fun y ↦ ?_
  change (homModule hA.trivialOn (FDRep.of (ofMulAction (ZMod l) Δ Y))).ρ g f
      (MonoidAlgebra.single y 1) = A.ρ g (f (MonoidAlgebra.single (mk' S (g⁻¹ : G) • y) 1))
  rw [homModule_apply]
  exact congrArg (fun v ↦ A.ρ g (f v)) (ofMulAction_single _ _ _)

variable [CompactSpace G]

private lemma diagonalPermModule_coprime (hA : A.FiniteKilledFixedInj l U z 1)
    (hS : ¬ l ∣ Nat.card S) (D : Subgroup Δ) (hD : ¬ l ∣ Nat.card D) :
    (A.diagonalPermModule U S (Δ ⧸ D)).IsHigmanProjective U := by
  classical
  have h_card : (Nat.card D : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  -- In the trace each coset occurs `#D` times, so normalize the indicator of the identity coset.
  let a : Δ ⧸ D → ZMod l := fun x ↦ if x = ⟦1⟧ then (Nat.card D : ZMod l)⁻¹ else 0
  refine isHigmanProjective_diagonalPermModule hA.nsmul_eq_zero hS a fun y ↦ ?_
  have h_eq (g : Δ) : g⁻¹ • y = ⟦1⟧ ↔ (g : Δ ⧸ D) = y := by
    rw [inv_smul_eq_iff]
    change y = ((g * 1 : Δ) : Δ ⧸ D) ↔ _
    rw [mul_one, eq_comm]
  simp only [a, h_eq]
  calc _ = ∑ p : (Δ ⧸ D) × D, if p.1 = y then (Nat.card D : ZMod l)⁻¹ else 0 :=
        Fintype.sum_equiv D.groupEquivQuotientProdSubgroup _ _ fun _ ↦ rfl
    _ = 1 := by simp [Fintype.sum_prod_type_right, -Nat.card_eq_fintype_card,
      ← Nat.cast_smul_eq_nsmul (ZMod l), ← Nat.card_eq_fintype_card, h_card]

end HomModules

variable (R) in
/-- Let `l` be prime, `G` a compact topological group and `U` open normal, and let every commutator
`⁅z, g⁆` lie in `U`. Consider the discrete `G`-modules over `R` that are finite, killed by `l` and
fixed by `U`, with `ρ z - 1` injective, and let `φ`, with values in `ℚ≥0`, satisfy `φ B = φ A * φ D`
for every short exact `A → B → D` with `B` of this kind. If `φ B = 1` for every such `B` satisfying
Higman's criterion relative to `U`, that is some additive `τ : B → B` has `∑ g τ g⁻¹ = 1` summed
over representatives `g` of the cosets in `G ⧸ U`, then `φ A = 1` for every such `A`. This is a form
of the known result that the Cartan map has finite cokernel (Serre, Linear Representations of Finite
Groups, §16.1, Theorem 35). -/
lemma IsMultiplicative.eq_one_of_eq_one_on_isHigmanProjective (l : ℕ) [Fact l.Prime]
    (U : OpenNormalSubgroup G) {z : G} {A : DiscreteModule R G}
    (φ : ∀ A : DiscreteModule R G, A.FiniteKilledFixedInj l U z 1 → ℚ≥0)
    [IsTopologicalGroup G] [CompactSpace G] (hz_central : ∀ g : G, ⁅z, g⁆ ∈ U)
    (h_mul : IsMultiplicative φ) (hA : A.FiniteKilledFixedInj l U z 1)
    (h_higman : ∀ {B : DiscreteModule R G} (hB : B.FiniteKilledFixedInj l U z 1),
      B.IsHigmanProjective U → φ B hB = 1) :
    φ A hA = 1 := by
  classical
  obtain ⟨S, j, hS, hz, hS_card⟩ := exists_normal_pow_mem_not_dvd_card l U hz_central
  let Γ₀ := (G ⧸ (U : Subgroup G)) ⧸ S
  -- A short exact sequence with projective middle term shows that `φ` is nonzero.
  have h_ne {B : DiscreteModule R G} (hB : B.FiniteKilledFixedInj l U z 1) : φ B hB ≠ 0 := by
    obtain ⟨_, _, _, _, h_exact, hP, h_proj⟩ := hB.exists_shortExact_higmanProjective hz_central
    intro h_zero
    have h := h_mul h_exact hP
    rw [h_higman hP h_proj, h_zero, zero_mul] at h
    exact one_ne_zero h
  -- On representations of the finite quotient use the invariant of the `A`-valued dual.
  let hM (M : FDRep (ZMod l) Γ₀) := homModule_finiteKilledFixedInj hA hz M
  let f (M : FDRep (ZMod l) Γ₀) : Additive ℚ≥0ˣ := .ofMul
    (Units.mk0 (φ (homModule hA.trivialOn M) (hM M)) (h_ne (hM M)))
  have hf : ∀ ⦃T : ShortComplex (FDRep (ZMod l) Γ₀)⦄, T.ShortExact →
      f T.X₂ = f T.X₁ + f T.X₃ := by
    intro T hT
    apply Additive.toMul.injective
    apply Units.ext
    exact (h_mul (homModule_shortExact hA.trivialOn hT) (hM T.X₂)).trans (mul_comm _ _)
  let F := liftFDRepK0 f hf
  have h_perm (Y : Type) [Finite Y] [MulAction Γ₀ Y] :
      (F (permK0 (ZMod l) Γ₀ Y)).toMul.val =
        φ (A.diagonalPermModule U S Y) (hA.diagonalPermModule hz Y) := by
    have h_eval : F (permK0 (ZMod l) Γ₀ Y) = f (FDRep.of (ofMulAction (ZMod l) Γ₀ Y)) :=
      (congrArg F (permK0_def (ZMod l) (G := Γ₀) Y)).trans
        (liftFDRepK0_of f hf (FDRep.of (ofMulAction (ZMod l) Γ₀ Y)))
    rw [h_eval]
    exact apply_eq_of_equiv h_mul h_higman (homModulePermEquiv hA Y)
  have h_van (D : Subgroup Γ₀) (hD : ¬ l ∣ Nat.card D) :
      F (permK0 (ZMod l) Γ₀ (Γ₀ ⧸ D)) = 0 := by
    apply Additive.toMul.injective
    apply Units.ext
    rw [h_perm, h_higman _ (diagonalPermModule_coprime hA hS_card D hD)]
    rfl
  -- Modular Artin induction expresses `#Γ₀` times the trivial class using coset representations
  -- of subgroups of order prime to `l`, on each of which the invariant is `1`.
  obtain ⟨a, ha⟩ := exists_linearCombination_indK0_resK0_eq_natCard_nsmul (k := ZMod l) (G := Γ₀) l
  have h_zero : Nat.card Γ₀ • F 1 = 0 := by
    rw [← map_nsmul, ← ha 1]
    simp only [Finsupp.linearCombination_apply, resK0_one, indK0_one, map_finsuppSum, map_zsmul]
    exact Finset.sum_eq_zero fun D _ ↦ by simp only [h_van D.val D.property.2, zsmul_zero]
  have h_pow : (F 1).toMul.val ^ Nat.card Γ₀ = 1 :=
    congrArg (fun x : Additive ℚ≥0ˣ ↦ x.toMul.val) h_zero
  have h_trivial : (F 1).toMul.val = 1 :=
    (pow_eq_one_iff_of_nonneg zero_le Nat.card_pos.ne').mp h_pow
  have h_line : permK0 (ZMod l) Γ₀ Unit = 1 := by
    rw [permK0_of_subsingleton, exactK0_one_eq_of_trivial]
  rw [← h_line, h_perm] at h_trivial
  have e : A.ρ.Equiv (A.diagonalPermModule U S Unit).ρ :=
    .mk (LinearEquiv.funUnique _ R A).symm fun _ ↦ rfl
  exact (apply_eq_of_equiv h_mul h_higman e).trans h_trivial

end

end ArtinInduction

end New.DiscreteModule
