module

import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.RingTheory.Etale.Weakly
import TauCeti.NumberTheory.NumberField.Countable
public import Lib.General.Combinatorics
public import Lib.Shimura.IntegralModel.UniversalFamily
import Lib.ClassField.Places.ValuationSubrings
import Lib.PadicComparison.Descent.TestCategory
import Lib.Shimura.CongruenceRelation.HeckeNeighbours
import Lib.Shimura.IntegralModel.BallImmersion

/-!
# Existence of the model: the tower of Kuga–Sato covers with its congruence relation

The end of the construction of the moduli tower. It goes from a universal family of PEL type
(`New.Variety.UniversalFamily`) to the structure `New.Variety.Model`, which is all that the point
counts use.

* `New.Variety.exists_model`: the model exists.
* `New.Variety.UniversalFamily.GraphClosure.congruenceRelation`,
  `New.Variety.UniversalFamily.GraphClosure.isTangentPoly_localTerm_of_translate`: the congruence
  relation and the tangent map at a fixed point, for the legs of a cover.

Notions from other files:
* `New.Variety.UniversalFamily`: a universal family of PEL type over `R`: a base scheme with an
  abelian scheme over it and its standing hypotheses. `New.Variety.UniversalFamily.GraphClosure` is
  the reduced closure of the graph of finitely many translations `a ↦ a·(g_j, 1)` of complex points;
  `C.proj j` projects it to the factor `j`, sending `C.point a` to `U.datumPoint 𝔪 (a.act g)`, the
  complex point of level `𝔪`, when `γ j = (𝔪, g)`.
* `New.Variety.Model`: the tower of Kuga–Sato varieties over `R`, given by a list of properties.
* `New.Variety.Cancels`: The integers `m i` add up to zero on every fibre of `v`, that is,
  `∑ m i • [v i] = 0` in the free abelian group on `V`.
* `New.Variety.IsSafe`: Safe places w of E: the place u of ℚ(√−d₀) below w satisfies
  `New.GaloisRep.IsSplitPrimeToDisc`, and 𝔑 lies neither in w nor in any place above ū.
* `New.Variety.IsNeat`: The level 𝔑 is neat: 𝔑 ≠ 0 and, whenever `x` is a signed frame with `ℓ` for
  some form (`New.Variety.IsSignedFrame`), every y in GL_n(E) with x⁻¹yx in `levelGU n 𝔑` (the
  subgroup of level 𝔑 of GL_n(𝔸f E), inside `GUPlus E n`, whose elements translate moduli points by
  `a.act`) that fixes ℓ under `New.Variety.ratConj` equals 1.

## Relation to the literature

Known result: Integral Kuga–Sato models for GU(1,n−1) with level covers and the congruence relation.
Here the smooth proper base is a closure of theta values with no moduli property. The covers are
reduced projective closures of tuples of isogenous points. The model asks for smoothness of the base
only, and of the covers that they are Galois on points in characteristic zero. The congruence
relation at good split places is part of the statement.
Source: Harris, Taylor, The geometry and cohomology of some simple Shimura varieties, 2001, III.4;
Kottwitz, Points on some Shimura varieties over finite fields, JAMS 5 (1992), §5.
-/

@[expose] public section

open NumberField CategoryTheory AlgebraicGeometry IsLocalRing CommRingCat New.Variety Spec
  ULift QuotientGroup Category Function ReducedClosure Finset IncidenceAlgebra Filter Algebra
  RingHom Over Finsupp ModuliPoint UniversalFamily

/-- The Möbius coefficients `(-1) ^ r * q ^ (r.choose 2)`, with `r = Module.finrank (ResField w) A`
the dimension of `A`, of the subspaces `A` of `k ^ n`, `k` the residue field of `w`, cancel along
every map that depends only on `A ⊔ W` for some `W ≠ ⊥`. -/
lemma New.Variety.cancels_moebius_of_factorsThrough_sup {E n : Type} {X : Type*} [Field E]
    [NumberField E] [Fintype n] {w : FinPlace E} {W : Submodule (ResField w) (n → ResField w)}
    (hW : W ≠ ⊥) {v : Submodule (ResField w) (n → ResField w) → X} (hv : v.FactorsThrough (· ⊔ W)) :
    Cancels
      (fun A : Submodule (ResField w) (n → ResField w) ↦
        (-1) ^ Module.finrank (ResField w) A * w.q ^ (Module.finrank (ResField w) A).choose 2)
      v := by
  classical
  let μ (A : Submodule (ResField w) (n → ResField w)) : ℤ :=
    (-1) ^ Module.finrank (ResField w) A * w.q ^ (Module.finrank (ResField w) A).choose 2
  let F (B : Submodule (ResField w) (n → ResField w)) : ℤ := ∑ A with A ⊔ W = B, μ A
  -- Summing `F` below `B` sums `μ` over the `A` with `A ⊔ W ≤ B`. This is empty unless `W ≤ B`;
  -- then it is the product in `q_binomial_submodule` at `X = 1`, whose first factor `1 - q ^ 0` is
  -- zero.
  let : LocallyFiniteOrder (Submodule (ResField w) (n → ResField w)) := Fintype.toLocallyFiniteOrder
  have sum_F (B : Submodule (ResField w) (n → ResField w)) : 0 = ∑ B' ∈ Finset.Iic B, F B' := by
    refine .trans ?_ (sum_fiberwise_eq_sum_filter ..).symm
    by_cases h : W ≤ B
    · have hfilt : (Finset.univ.filter fun A : Submodule (ResField w) (n → ResField w) ↦
          A ⊔ W ∈ Finset.Iic B) = Finset.univ.filter (· ≤ B) := by
        ext A
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic, sup_le_iff, h,
          and_true]
      rw [hfilt, ← Int.cast_inj (α := ℂ), Int.cast_zero, Int.cast_sum]
      have hcast : (∑ A ∈ Finset.univ.filter (· ≤ B), (μ A : ℂ)) =
          ∑ A ∈ Finset.univ.filter (· ≤ B), heckePolyCoeff 1 A :=
        Finset.sum_congr rfl fun A _ ↦ by
          simp only [μ, heckePolyCoeff, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
            Int.cast_natCast, card_ResField]
      rw [hcast, q_binomial_submodule, SiegelWeil.qPochhammer]
      have hpos : 0 < Module.finrank (ResField w) B :=
        pos_iff_ne_zero.mpr (mt Submodule.finrank_eq_zero.mp (ne_bot_of_le_ne_bot hW h))
      exact (Finset.prod_eq_zero (i := 0) (Finset.mem_range.mpr hpos)
        (by simp only [pow_zero, mul_one, sub_self])).symm
    · have hfilt : (Finset.univ.filter fun A : Submodule (ResField w) (n → ResField w) ↦
          A ⊔ W ∈ Finset.Iic B) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro A _ hle
        exact h (le_sup_right.trans (Finset.mem_Iic.mp hle))
      rw [hfilt, Finset.sum_empty]
  have F_eq_zero (B : Submodule (ResField w) (n → ResField w)) : F B = 0 := by
    simpa only [Pi.zero_apply, mul_zero, sum_const_zero] using moebius_inversion_bot F 0 sum_F B
  -- `F B` is the coefficient of `B` in the formal sum of the `μ A • [A ⊔ W]`
  refine .mono ((FreeAddCommGroup.equivFinsupp _).injective (ext fun B ↦ ?_)) hv
  rw [map_sum, map_zero, Finset.sum_apply', Finsupp.zero_apply]
  have hterm (A : Submodule (ResField w) (n → ResField w)) :
      FreeAddCommGroup.equivFinsupp _ (μ A • FreeAddCommGroup.of (A ⊔ W)) B =
        if A ⊔ W = B then μ A else 0 := by
    rw [map_zsmul, Finsupp.smul_apply]
    have hof : FreeAddCommGroup.equivFinsupp _ (FreeAddCommGroup.of (A ⊔ W)) =
        single (A ⊔ W) 1 := by simp
    rw [hof, single_apply, smul_ite, zsmul_eq_mul, mul_one, Int.cast_id, smul_zero]
  rw [Finset.sum_congr rfl fun A _ ↦ hterm A, ← Finset.sum_filter]
  exact F_eq_zero B

/-- Suppose `D.β` is the image of (1 + √−d₀)/2, and `c` sends the complex point of each `a` in the
closure `C` to `U.datumPoint 1 a`. Let `w` be a split finite place that is safe for `D.level` and at
which `D` is good, with residue field `k` of order `q = l ^ f`, and let `𝔭 ⊆ R` contain the image of
`w`. Let `u A`, for each subspace `A` of `k ^ n`, be maps from `C` to the base that translate the
complex points by the Hecke element `invHeckeIsogeny w A`. Then `u` satisfies the congruence
relation modulo `𝔭` (`New.Variety.CongruenceRelation`) with coefficients
`(-1) ^ r * q ^ (r.choose 2)` and `l`-power Frobenius exponents `(n - r) * f`, where `r` is the
dimension of `A`. -/
lemma New.Variety.UniversalFamily.GraphClosure.congruenceRelation {E : Type} [Field E] [CMBase E]
    {d₀ : ℕ} [HasQuadSubfield d₀ E] {R : Subalgebra (𝓞 E) E} {D : PEL E}
    {U : UniversalFamily D R} (hβ : D.β = algebraMap (𝓞 (QuadField d₀)) (𝓞 E) (QuadField.betaK d₀))
    {ν : ℕ} [NeZero ν] {J : Type} [Finite J] {γ : J → nonZeroDivisors (𝓞 E) × GUPlus E D.Index}
    (C : U.GraphClosure γ ν)
    {c : C.scheme ⟶ (Over.map U.base.hom).obj
      (ThetaFamily.fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin ν))}
    (hc : ∀ a : ModuliPoint E D.Index ν, C.point a ≫ c = U.datumPoint 1 a) {w : SplitFinPlace E}
    (hw : IsSafe D.level w.val) (hD : D.IsGoodAt w.val.asIdeal) {𝔭 : Set R}
    (h𝔭 : ∀ a ∈ w.val.asIdeal, algebraMap (𝓞 E) R a ∈ 𝔭)
    {u : Submodule (ResField (E := E) w) (D.Index → ResField (E := E) w) →
      (C.scheme ⟶ (Over.map U.base.hom).obj
        (ThetaFamily.fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin ν)))}
    (hu : ∀ (A : Submodule (ResField (E := E) w) (D.Index → ResField (E := E) w))
        (a : ModuliPoint E D.Index ν),
      C.point a ≫ u A = U.datumPoint 1 (a.act
        ⟨invHeckeIsogeny w A, invHeckeIsogeny_mem_GUPlus w A⟩))
    {l f : ℕ} [Fact l.Prime] (hq : w.val.q = l ^ f) :
    let r (A : Submodule (ResField w.val) (D.Index → ResField w.val)) : ℕ :=
      Module.finrank (ResField w.val) A
    CongruenceRelation (fun A ↦ (-1) ^ r A * w.val.q ^ (r A).choose 2) 𝔭 l
      (fun A ↦ (Fintype.card D.Index - r A) * f) u := by
  intro r k h_field h_charP x hx
  -- `x` comes from the residue field of a point `z`, and `z` is the centre of an arc `α` over a
  -- valuation ring `V` of `ℂ`. By `along`, a map that sends the complex point of `b` to that of
  -- `a` sends `α` to the `V`-point of `a`.
  obtain ⟨z, ρ, rfl, -⟩ := exists_countable_residue_point C.scheme.hom x
  obtain ⟨V, α, b, ρ', centre, along⟩ := C.exists_arc z
  have hz_charP : CharP (C.scheme.left.residueField z) l := ρ.charP ρ.injective l
  have hV_charP : CharP (ResidueField V) l := charP_of_injective_ringHom ρ'.injective l
  -- the Frobenius twists of the reduced Hecke neighbours depend only on `A ⊔ W`, for some `W ≠ ⊥`
  let twist (A : Submodule (ResField w.val) (D.Index → ResField w.val)) :=
    specMap ((iterateFrobenius (ResidueField V) l ((Fintype.card D.Index - r A) * f)).comp
      (residue V)) ≫ α ≫ (u A).left
  obtain ⟨W, hW, reduction⟩ : ∃ W ≠ ⊥, FactorsThrough twist (· ⊔ W) := by
    -- the Frobenius exponents: `l ^ ((n - r A) * f) = q ^ (n - r A)`
    refine U.exists_ne_bot_factorsThrough_sup hβ (along (hc b)) residue_surjective rfl ?_ hD hw
      (fun A ↦ by dsimp only [r]; rw [pow_mul', ← hq, Fintype.card_fin]) fun A ↦ along (hu A b)
    -- the centre of the arc lies above `w`
    refine w.val.isMaximal.eq_of_le (ker_ne_top _) fun a ha ↦ ?_
    have hcw : c.left ≫ (U.family.fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin ν)).hom ≫
        U.base.hom = C.scheme.hom := c.w
    have hmap : (specMap (residue V) ≫ (α ≫ c.left) ≫
        (U.family.fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin ν)).hom) ≫
        U.base.hom ≫ specMap (algebraMap (𝓞 E) R) =
        (specMap ρ' ≫ C.scheme.left.fromSpecResidueField z ≫ C.scheme.hom) ≫
        specMap (algebraMap (𝓞 E) R) := by
      rw [assoc, assoc, assoc, ← assoc (specMap (residue V)), ← centre, assoc, assoc,
        ← assoc (U.family.fibrePower _).hom, ← assoc c.left, hcw, assoc]
    rw [RingHom.mem_ker, ThetaObject.baseHom, hmap, preimage_comp, preimage_comp]
    have h0 := hx _ (h𝔭 a ha)
    rw [assoc, preimage_comp] at h0
    simp only [specMap, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      Spec.preimage_map, CommRingCat.hom_ofHom, map_eq_zero] at h0 ⊢
    exact h0
  refine (cancels_moebius_of_factorsThrough_sup hW reduction).mono fun A B hAB ↦ ?_
  -- Frobenius commutes with `ρ` and `ρ'`, and `Spec` of a field embedding is an epimorphism: the
  -- equation descends from the residue field of `V` to that of `z` and goes up to `k`.
  simp only [twist, specMap, ofHom_comp, Spec.map_comp, assoc] at hAB ⊢
  simp only [← reassoc_of% centre] at hAB
  simp only [← Spec.map_comp_assoc, ← ofHom_comp, ← iterateFrobenius_comm] at hAB ⊢
  simp only [ofHom_comp, Spec.map_comp, assoc] at hAB ⊢
  exact congrArg (Spec.map (ofHom ρ) ≫ ·) ((cancel_epi (Spec.map (ofHom ρ'))).mp hAB)


/-- The tangent map at a fixed point. Let `c` send the complex point of `a` in the closure `C` to
that of `a` in the base (`U.datumPoint 1 a`), and let `v` send it to that of the translate
`a.act g α`. Suppose `z` in GL_n(E) relates this translate to `a` at level `D.level` (`IsLevelIso`),
the characteristic polynomial of `z` is separable, and `a.reflection` is the marked reflection
`markedReflection z μ` for the index `μ`. Then `localTerm α z.val.charpoly μ` is
`det (1 - X (dc)⁻¹ dv)` on the tangent space at the point of `a`, which has dimension
`card D.Index - 1 + ν * abelianDim E D.Index`, up to a constant factor
(`New.Variety.IsTangentPoly`). -/
lemma New.Variety.UniversalFamily.GraphClosure.isTangentPoly_localTerm_of_translate
    {E : Type} [Field E] [CMBase E] {R : Subalgebra (𝓞 E) E}
    {D : PEL E} {U : UniversalFamily D R} {ν : ℕ} [NeZero ν] {J : Type} [Finite J]
    {γ : J → nonZeroDivisors (𝓞 E) × GUPlus E D.Index} (C : U.GraphClosure γ ν)
    {c v : C.scheme ⟶ (Over.map U.base.hom).obj
      (ThetaFamily.fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin ν))}
    (hc : ∀ a : ModuliPoint E D.Index ν, C.point a ≫ c = U.datumPoint 1 a) {g : GUPlus E D.Index}
    {α : Fin ν → 𝓞 E} (hv : ∀ a : ModuliPoint E D.Index ν,
      C.point a ≫ v = U.datumPoint 1 (a.act g α))
    {a : ModuliPoint E D.Index ν} {z : GL D.Index E} {μ : D.Index}
    (hz : z.val.charpoly.Separable) (h_reflection : a.reflection = markedReflection z μ)
    (hrel : (a.act g α).IsLevelIso (levelGU D.Index D.level) z a) :
    IsTangentPoly (Fintype.card D.Index - 1 + ν * abelianDim E D.Index)
      ((algPoints (ℂ) (of R)).map c) ((algPoints (ℂ) (of R)).map v) ⟨C.point a⟩
      (localTerm α z.val.charpoly μ) := by
  -- An analytic family `q ↦ f.ballPoint a.markedPoint q` passes through `a` at `q = 0`, and `z`
  -- acts on it near `0` by a linear map `K`. The tangent space is the parameter space, by the
  -- universal jet `σ`.
  obtain ⟨f, hf⟩ := exists_isBallFamily a
  obtain ⟨K, hK, hdet⟩ := hf.exists_linear_isLevelIso hz h_reflection hrel
  obtain ⟨σ, hσ⟩ := (C.holomorphicAt_point a.markedPoint 0 hf.zero_mem).exists_isJet .id
  -- `τ x` is the jet `σ` in the direction `x`
  let τ (x : BallBase D.Index × (Fin ν → BallFibre E D.Index)) :
      Spec (of (TrivSqZeroExt ℂ ℂ)) ⟶ C.scheme.left :=
    specMap (TrivSqZeroExt.map (.applyₗ x)).toRingHom ≫ σ
  have jet (x : BallBase D.Index × (Fin ν → BallFibre E D.Index)) :
      IsJet (fun q ↦ (C.point (f.ballPoint a.markedPoint q)).left) 0 (LinearMap.applyₗ x) (τ x) :=
    fun V s hV ↦ by
      obtain ⟨hland, hval⟩ := hσ V s hV
      refine ⟨hland.comp _, ?_⟩
      dsimp only [τ]
      rw [PointFn.isRegularOn_ofSection s _ _ hland, hval]
      change (TrivSqZeroExt.map (.applyₗ x)) (_ + _) = _
      simp only [map_add, TrivSqZeroExt.map_inl, TrivSqZeroExt.map_inr, LinearMap.id_apply,
        LinearMap.applyₗ_apply_apply]
  -- followed by `c`, it is the jet of the family in the base (`hc`)
  have jet_c (x : BallBase D.Index × (Fin ν → BallFibre E D.Index)) :
      IsJet (fun q ↦ (U.datumPoint 1 (f.ballPoint a.markedPoint q)).left) 0 (LinearMap.applyₗ x)
        (τ x ≫ c.left) :=
    ((jet x).comp_hom c.left).congr
      (.of_forall fun q ↦ congrArg Hom.left (hc (f.ballPoint a.markedPoint q)))
  -- followed by `v`, it is the jet of the family moved by `K` (`hv`, and `z` near `0` by `hK`)
  have jet_v (x : BallBase D.Index × (Fin ν → BallFibre E D.Index)) :
      IsJet (fun q ↦ (U.datumPoint 1 (f.ballPoint a.markedPoint (K q))).left) 0 (LinearMap.applyₗ x)
        (τ x ≫ v.left) :=
    ((jet x).comp_hom v.left).congr <| hK.mono fun q hq ↦ by
      have h_pt : C.point (f.ballPoint a.markedPoint q) ≫ v = U.datumPoint 1
        (f.ballPoint a.markedPoint (K q)) :=
        (hv _).trans (datumPoint_eq_iff.mpr ⟨z, by simpa using hq⟩)
      exact congrArg Hom.left h_pt
  -- the tangent space at the point of `a` is the parameter space of the family, embedded by `σ`;
  -- it remains to check its dimension and its base point, that `dc` is injective, and `dv = dc K`
  refine ⟨.of ℂ _, ⟨homMk σ ((hσ.comp_base_eq fun _ ↦ w _).trans (map_comp ..).symm)⟩, K, ?_, ?_,
    fun x y hxy ↦ ?_, fun x ↦ up_inj.mpr (OverMorphism.ext ?_), hdet⟩
  · simp [finrank_eq_abelianDim (f.torus 0).realEquiv, Module.finrank_pi_fintype]
  · -- the jet `σ` lies over the point of `f.ballPoint a.markedPoint 0 = a`
    refine congrArg ULift.up (OverMorphism.ext (hσ.fst_comp.trans ?_))
    rw [hf.ballPoint_zero]
  · -- Equal jets give equal derivatives, so the family is constant to first order in the
    -- direction `x - y`; it is immersed in the base.
    have same : τ x ≫ c.left = τ y ≫ c.left := congr($hxy.1.left)
    have imm : IsHolomorphicImmersionAt (fun q ↦
      (U.datumPoint 1 (f.ballPoint a.markedPoint q)).left) 0 :=
      U.isHolomorphicImmersionAt_datumPoint 0 hf.zero_mem
    refine sub_eq_zero.mp (imm.2 _ (isFirstOrderConst_iff.mpr fun V s hV ↦ ?_))
    have value_x := (jet_c x V s hV).2
    rw [same, (jet_c y V s hV).2] at value_x
    have hsnd := congrArg TrivSqZeroExt.snd value_x.symm
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
      LinearMap.applyₗ_apply_apply] at hsnd
    rw [map_sub, sub_eq_zero]
    exact hsnd
  · -- By the chain rule, both sides are the jet of `q ↦ f.ballPoint a.markedPoint (K q)` in the
    -- direction `x`.
    let K' := ContinuousLinearMap.mk K
    have h0 : K' 0 = 0 := map_zero K'
    have chain : IsJet (fun q ↦ (U.datumPoint 1 (f.ballPoint a.markedPoint (K q))).left) 0
        (LinearMap.applyₗ x) (τ (K x) ≫ c.left) :=
      (isJet_comp_iff K'.hasFDerivAt
        (U.isHolomorphicImmersionAt_datumPoint _ (by rw [h0]; exact hf.zero_mem)).1).mpr
        (by rw [h0]; exact jet_c (K x))
    exact (jet_v x).unique chain

/-- Two moduli points `a` and `b` with the same complex point in the base (`hab`) have the same
complex point in the closure `C` after `a` is translated by `κ⁻¹` for some `κ` in
`levelGU D.Index D.level`. -/
lemma New.Variety.UniversalFamily.GraphClosure.exists_point_act_eq {E : Type} [Field E] [CMBase E]
    {R : Subalgebra (𝓞 E) E} {D : PEL E} {U : UniversalFamily D R} {ν : ℕ}
    {J : Type} [Finite J] {γ : J → nonZeroDivisors (𝓞 E) × GUPlus E D.Index}
    (C : U.GraphClosure γ ν) {a b : ModuliPoint E D.Index ν}
    (hab : U.datumPoint 1 a = U.datumPoint 1 b) :
    ∃ κ : levelGU D.Index D.level,
      C.point (a.act ⟨↑κ⁻¹, mem_GUPlus_of_mem_levelGU κ⁻¹.property⟩) = C.point b := by
  -- `z` is an isomorphism of level `D.level` from `a` to `b`. Its level condition gives `κ`; after
  -- translating `a` by `κ⁻¹`, `z` is an isomorphism of every level, in particular of the level
  -- `𝔫` at which the points of `C` are determined.
  obtain ⟨z, hz⟩ := datumPoint_eq_iff.mp hab
  obtain ⟨𝔫, h_point_eq⟩ := C.exists_level_point_eq
  exact ⟨⟨_, hz.mem_level.1⟩, h_point_eq
    { mem_level := by
        simp only [act, Subgroup.coe_inv, ← mul_assoc, mul_inv_cancel, one_mem]
      reflection_eq := hz.reflection_eq
      sub_mem_lattice := fun i ↦ by
        simp only [act, Pi.one_apply, map_one, one_smul]
        exact hz.sub_mem_lattice i }⟩

/-- A map `f` from the closure `C` to the base that translates the complex points by `g` is
determined by the coset of `g` modulo `levelGU D.Index D.level`: there is one map `u` on all cosets
with `f = u ⟦g⟧` for every such `f`. The map `c` witnesses that maps to the base exist. -/
lemma New.Variety.UniversalFamily.GraphClosure.exists_forall_eq_apply_mk_of_translate {E : Type}
    [Field E] [CMBase E] {R : Subalgebra (𝓞 E) E} {D : PEL E} {U : UniversalFamily D R} {ν : ℕ}
    {J : Type} [Finite J] {γ : J → nonZeroDivisors (𝓞 E) × GUPlus E D.Index}
    (C : U.GraphClosure γ ν)
    (c : C.scheme ⟶ (Over.map U.base.hom).obj
      (ThetaFamily.fibrePower (X := U.family) (NonzeroTorsion (E := E) 1 D.Index ⊕ Fin ν))) :
    ∃ u : (GL D.Index (𝔸f E) ⧸ levelGU D.Index D.level) →
        (C.scheme ⟶ (Over.map U.base.hom).obj
          (ThetaFamily.fibrePower (X := U.family) (NonzeroTorsion (E := E) 1 D.Index ⊕ Fin ν))),
      ∀ {g : GL D.Index (𝔸f E)}
        {f : C.scheme ⟶ (Over.map U.base.hom).obj
          (ThetaFamily.fibrePower (X := U.family) (NonzeroTorsion (E := E) 1 D.Index ⊕ Fin ν))}
        (hg : g ∈ GUPlus E D.Index),
      (∀ a : ModuliPoint E D.Index ν, C.point a ≫ f = U.datumPoint 1 (a.act ⟨g, hg⟩)) →
      f = u ⟦g⟧ := by
  -- the legs: maps `f` that translate complex points by some `g`
  let Leg := Σ' (g : GUPlus E D.Index)
    (f : C.scheme ⟶ (Over.map U.base.hom).obj
      (ThetaFamily.fibrePower (X := U.family) (NonzeroTorsion (E := E) 1 D.Index ⊕ Fin ν))),
    ∀ a : ModuliPoint E D.Index ν, C.point a ≫ f = U.datumPoint 1 (a.act g)
  -- two legs whose `g` have the same coset agree on all complex points, hence are equal
  have factors :
      FactorsThrough (fun p : Leg ↦ p.snd.fst) fun p : Leg ↦
        (p.fst.val : GL D.Index (𝔸f E) ⧸ levelGU D.Index D.level) := by
    rintro ⟨⟨g, hg⟩, f, hf⟩ ⟨⟨g', hg'⟩, f', hf'⟩ hpq
    refine C.isSeparatingFamily.hom_ext fun a ↦ ?_
    -- the isomorphism is `1`; its level condition is the equality of cosets `hpq`
    have hpt : U.datumPoint 1 (a.act ⟨g, hg⟩) = U.datumPoint 1 (a.act ⟨g', hg'⟩) := by
      refine datumPoint_eq_iff.mpr ⟨1, ?_, by simp only [act, ratConj, map_one, one_smul],
        fun i ↦ by
          rw [act, act, realVecAction, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
            Matrix.mulVecLin_apply, Matrix.one_mulVec, sub_self]
          exact zero_mem _⟩
      have hmem : g'⁻¹ * g ∈ levelGU D.Index D.level := QuotientGroup.eq.mp hpq.symm
      have h1 : (a.frame * g')⁻¹ * toFinGL (1 : GL D.Index E) * (a.frame * g) = g'⁻¹ * g := by
        simp only [map_one, mul_one, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      change (a.frame * g')⁻¹ * toFinGL (1 : GL D.Index E) * (a.frame * g) ∈
        levelGU D.Index D.level ⊓ levelGU D.Index 1
      rw [levelGU_inf_one, h1]
      exact hmem
    exact (hf a).trans (hpt.trans (hf' a).symm)
  have h_nonempty : Nonempty (C.scheme ⟶ (Over.map U.base.hom).obj
      (ThetaFamily.fibrePower (X := U.family) (NonzeroTorsion (E := E) 1 D.Index ⊕ Fin ν))) := ⟨c⟩
  obtain ⟨u, hu⟩ := (factorsThrough_iff _).mp factors
  exact ⟨u, fun hg h ↦ congrFun hu ⟨⟨_, hg⟩, _, h⟩⟩

/-- Maps from a subring `R` of a number field that contains the integers to fields of
characteristic zero are injective, as `R` is algebraic over `ℤ`. -/
lemma New.Variety.injective_of_subalgebra_of_charZero {E : Type*} [Field E] [NumberField E]
    (R : Subalgebra (𝓞 E) E) (k : Type*) [Field k] [CharZero k] (f : R →+* k) :
    Function.Injective f := by
  -- `E` is algebraic over `ℤ` through `𝓞 E`, hence so is its subring `R`; a map from an algebraic
  -- `ℤ`-algebra to a field of characteristic zero is injective
  let algebra_R_k : Algebra R k := f.toAlgebra
  have h_alg_E : Algebra.IsAlgebraic ℤ E := IsAlgebraic.trans ℤ (𝓞 E) E
  have h_alg_R : Algebra.IsAlgebraic ℤ R := h_alg_E.tower_bot_of_injective Subtype.val_injective
  exact h_alg_R.injective_tower_top R Int.cast_injective

namespace New.Variety

section TowerHelpers

variable {E : Type} [Field E] [CMBase E] {R : Subalgebra (𝓞 E) E}
  {D : PEL E} {U : UniversalFamily D R} {ν : ℕ}

private lemma ModuliPoint.act_eq_self {n : Type} [Fintype n] [DecidableEq n]
    (a : ModuliPoint E n ν) {g : GUPlus E n} (hg : g.val = 1) : a.act g = a := by
  cases a
  simp only [act, hg, mul_one, Pi.one_apply, map_one, one_smul]

private lemma ModuliPoint.act_mul {n : Type} [Fintype n] [DecidableEq n]
    (a : ModuliPoint E n ν) (g h : GUPlus E n) : (a.act g).act h = a.act (g * h) := by
  simp only [act, Submonoid.coe_mul, mul_assoc, Pi.one_apply, map_one, one_smul]

/-- The finite quotient of `levelGU D.Index D.level` by the normal core of its subgroup of level
`M`: the deck group of a cover of the tower in `New.Variety.exists_model`. -/
private abbrev TowerQuot (D : PEL E) (M : nonZeroDivisors (𝓞 E)) : Type :=
  levelGU D.Index D.level ⧸ ((levelGU D.Index (M : 𝓞 E)).subgroupOf
    (levelGU D.Index D.level)).normalCore

open scoped Classical in
/-- The pairs `(𝔪, κ * g)` that define the cover of level `i` in `New.Variety.exists_model`: `κ`
runs over `New.Variety.TowerQuot D M` (through the chosen representative `out`) and `(𝔪, g)` over
`i`, `(1, 1)` and `(M, 1)`. -/
private noncomputable abbrev towerPairs (D : PEL E) (M : nonZeroDivisors (𝓞 E))
    (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E D.Index))
    (j : TowerQuot D M × ↥(insert (M, 1) (insert 1 i))) :
    nonZeroDivisors (𝓞 E) × GUPlus E D.Index :=
  (j.2.val.1, ⟨_, mem_GUPlus_of_mem_levelGU j.1.out.property⟩ * j.2.val.2)

open scoped Classical in
/-- On the cover `C` of level `i` with pairs `New.Variety.towerPairs D M i`, the factor `(⟦κ⟧, x)`
of the point of `a` may be computed with the representative `κ` instead of the chosen one: the two
differ by an element of level `M`, which `hM` conjugates into the level of every pair. -/
private lemma UniversalFamily.GraphClosure.point_comp_proj_towerPairs
    {M : nonZeroDivisors (𝓞 E)} {i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E D.Index)}
    (hM : ∀ x ∈ insert (M, 1) (insert 1 i), ∀ k ∈ levelGU D.Index (M : 𝓞 E),
      (x.2 : GL D.Index (𝔸f E))⁻¹ * k * x.2 ∈ levelGU D.Index D.level ⊓ levelGU D.Index x.1)
    (C : U.GraphClosure (towerPairs D M i) ν) {a : ModuliPoint E D.Index ν}
    (x : ↥(insert (M, 1) (insert 1 i))) (κ : levelGU D.Index D.level) :
    C.point a ≫ C.proj (⟦κ⟧, x) =
      U.datumPoint x.val.1 (a.act (⟨κ, mem_GUPlus_of_mem_levelGU κ.property⟩ * x.val.2)) := by
  -- `κ⁻¹` times the chosen representative of `⟦κ⟧` has level `M`
  have h_deep : (κ.val⁻¹ * (κ : TowerQuot D M).out) ∈ levelGU D.Index (M : 𝓞 E) := by
    have h := Subgroup.normalCore_le _ (QuotientGroup.eq.1 (κ : TowerQuot D M).out_eq.symm)
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h
  rw [point_comp_proj]
  refine datumPoint_eq_iff.2 ⟨1, ?_, by simp only [act, ratConj, map_one, one_smul],
    fun k ↦ by
      rw [act, act, realVecAction, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.mulVecLin_apply, Matrix.one_mulVec, sub_self]
      exact zero_mem _⟩
  have hframe :
      (a.act (⟨κ, mem_GUPlus_of_mem_levelGU κ.2⟩ * x.1.2)).frame⁻¹ * toFinGL (1 : GL D.Index E) *
        (a.act (towerPairs D M i (⟦κ⟧, x)).2).frame =
      (x.val.2 : GL D.Index (𝔸f E))⁻¹ * (κ.val⁻¹ * (κ : TowerQuot D M).out.val) * x.val.2 := by
    simp only [act, Submonoid.coe_mul, map_one, mul_one, mul_inv_rev, mul_assoc,
      inv_mul_cancel_left]
  rw [hframe]
  exact hM _ x.property _ h_deep

open scoped Classical in
/-- The element `κ` of `levelGU D.Index D.level` acts on the cover `C` of level `i` by a map `p`
that permutes the factors, `(q, x) ↦ (κ⁻¹ q, x)`, and translates complex points by `κ⁻¹`. -/
private lemma UniversalFamily.GraphClosure.exists_deck_towerPairs
    {M : nonZeroDivisors (𝓞 E)} {i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E D.Index)}
    (hM : ∀ x ∈ insert (M, 1) (insert 1 i), ∀ k ∈ levelGU D.Index (M : 𝓞 E),
      (x.2 : GL D.Index (𝔸f E))⁻¹ * k * x.2 ∈ levelGU D.Index D.level ⊓ levelGU D.Index x.1)
    (C : U.GraphClosure (towerPairs D M i) ν) (κ : levelGU D.Index D.level) :
    ∃ p : C.scheme ⟶ C.scheme,
      (∀ j : TowerQuot D M × ↥(insert (M, 1) (insert 1 i)),
        p ≫ C.proj j = C.proj (κ⁻¹ * j.1, j.2)) ∧
        ∀ a : ModuliPoint E D.Index ν,
          C.point a ≫ p = C.point (a.act ⟨↑κ⁻¹, mem_GUPlus_of_mem_levelGU κ⁻¹.property⟩) :=
  C.exists_lift _ _ fun a j ↦ by
    rw [← j.1.out_eq, ← QuotientGroup.mk_mul, C.point_comp_proj_towerPairs hM]
    refine congrArg (U.datumPoint j.2.val.1) ?_
    rw [act_mul, ← mul_assoc]
    rfl

open scoped Classical in
/-- The deck maps `p κ` act freely on complex points: if `p κ` and `p κ'` agree at the point of `x`,
then `κ` and `κ'` have the same class in `New.Variety.TowerQuot D M`. Compare the factors
`(⟦κ * q⁻¹⟧, (M, 1))`: the isomorphism between the two translates is an automorphism of level
`D.level`, hence trivial as the level is neat. -/
private lemma UniversalFamily.GraphClosure.eq_of_point_comp_deck_eq
    (hN : IsNeat D.Index D.level) {M : nonZeroDivisors (𝓞 E)}
    {i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E D.Index)}
    (hM : ∀ x ∈ insert (M, 1) (insert 1 i), ∀ k ∈ levelGU D.Index (M : 𝓞 E),
      (x.2 : GL D.Index (𝔸f E))⁻¹ * k * x.2 ∈ levelGU D.Index D.level ⊓ levelGU D.Index x.1)
    (C : U.GraphClosure (towerPairs D M i) ν) {p : levelGU D.Index D.level → (C.scheme ⟶ C.scheme)}
    (hp : ∀ (κ : levelGU D.Index D.level) (a : ModuliPoint E D.Index ν),
      C.point a ≫ p κ = C.point (a.act ⟨↑κ⁻¹, mem_GUPlus_of_mem_levelGU κ⁻¹.property⟩))
    {x : ModuliPoint E D.Index ν} {κ κ' : levelGU D.Index D.level}
    (h_eq : C.point x ≫ p κ = C.point x ≫ p κ') :
    (κ : TowerQuot D M) = κ' := by
  refine QuotientGroup.eq.2 fun q ↦ ?_
  rw [hp, hp] at h_eq
  obtain ⟨z, hz⟩ := datumPoint_eq_iff.1
    (by simpa only [C.point_comp_proj_towerPairs hM] using
      h_eq =≫ C.proj ⟨⟦κ * q⁻¹⟧, _, mem_insert_self ..⟩)
  obtain ⟨h_level_𝔑, h_level_M⟩ := Subgroup.mem_inf.mp hz.mem_level
  simp only [act, mul_one, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc,
    inv_mul_cancel_left] at h_level_𝔑 h_level_M
  have h_aut : x.frame⁻¹ * toFinGL z * x.frame ∈ levelGU D.Index D.level := by
    have h1 : q.val * (κ.val⁻¹ * (κ'.val * (x.frame⁻¹ * (toFinGL z * x.frame)))) ∈
        levelGU D.Index D.level := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using mul_mem h_level_𝔑 q.property
    have h2 := (mul_mem_cancel_left q.property).mp h1
    have h3 := (mul_mem_cancel_left (inv_mem κ.property)).mp h2
    have h4 := (mul_mem_cancel_left κ'.property).mp h3
    rwa [mul_assoc]
  obtain rfl : z = 1 := hN.eq_one_of_mem_levelGU x.isSignedFrame h_aut hz.reflection_eq
  simp only [map_one, one_mul, inv_mul_cancel_left] at h_level_M
  rw [Subgroup.mem_subgroupOf]
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using h_level_M

end TowerHelpers

end New.Variety

/-- Let `U` be a universal family over `R` for the PEL data `D` (`New.Variety.UniversalFamily`),
where `E` contains ℚ(√−d₀) with d₀ ≡ 3 mod 4. Suppose that `D.level` is neat and that `D.β` is the
image of (1 + √−d₀)/2. Suppose also that `D` is good (`New.PEL.IsGoodAt`) at every finite place `w`
that is safe for `D.level`, meaning that the place of ℚ(√−d₀) below `w` is split and prime to the
discriminant, and that `D.level` lies neither in `w` nor in any place above its conjugate. Then for
every ν ≠ 0 there is a model `New.Variety.Model D.Index d₀ D.level ν R`, that is, a tower of
Kuga–Sato varieties over `R` with base `base`, schemes `cover i` and legs `leg` to the base, finite
deck groups `deckGroup i`, maps `mulMap` and complex points, satisfying the listed properties. -/
lemma New.Variety.exists_model {E : Type} [Field E] [CMBase E]
    {d₀ : ℕ} [HasQuadSubfield d₀ E] {R : Subalgebra (𝓞 E) E} {D : PEL E} (U : UniversalFamily D R)
    (hN : IsNeat D.Index D.level) (hβ : D.β = algebraMap (𝓞 (QuadField d₀)) (𝓞 E)
      (QuadField.betaK d₀))
    (hG : ∀ w : FinPlace E, IsSafe D.level w → D.IsGoodAt w.asIdeal) (ν : ℕ) [NeZero ν] :
    Nonempty (Model D.Index d₀ D.level ν R) := by
  classical
  -- The cover of level `i` is the closure `C i` of the tuples of complex points translated by
  -- `κ * g`, with `κ` in the finite quotient `New.Variety.TowerQuot D (M i)` of
  -- `levelGU D.Index D.level` and `(𝔪, g)` in `i` or equal to `(1, 1)` or `(M i, 1)`
  -- (`New.Variety.towerPairs`). All maps between covers are lifts of translations of points, and
  -- are determined by them. `M i` is chosen so that `g⁻¹ K(M i) g ⊆ K(𝔑) ∩ K(𝔪)` for all these
  -- `(𝔪, g)`.
  choose M hM using exists_level_conj_mem (n := D.Index) hN.ne_zero
  -- The base is the fibre power at level `1`: smooth, with dense complex points, and `m α`
  -- multiplies the marked points by `α`.
  obtain ⟨smooth, dense, m, hm⟩ := U.smooth_and_isDenseFamily_and_exists_comp_eq_act ν
  obtain ⟨C⟩ : Nonempty (∀ i, U.GraphClosure (towerPairs D (M i) i) ν) := inferInstance
  -- `κ` acts on `C i` by permuting the factors: this is the deck transformation `p κ`
  choose p p_proj pt_p using fun {i} ↦ (C i).exists_deck_towerPairs (hM i)
  -- the legs `u i`, and the set `s i` of the `g` for which `u i ⟦g⟧` translates points by `g`
  have pt_base (i) (a : ModuliPoint E D.Index ν) :
      (C i).point a ≫ (C i).proj ⟨⟦1⟧, 1, by simp⟩ = U.datumPoint 1 a := by
    rw [(C i).point_comp_proj_towerPairs (hM i)]
    exact congrArg (U.datumPoint 1) (act_eq_self a (by simp only [Subgroup.coe_one, Prod.snd_one,
      mul_one]))
  choose u eq_u using fun i ↦
    (C i).exists_forall_eq_apply_mk_of_translate ((C i).proj ⟨⟦1⟧, 1, by simp⟩)
  let s i := {g | ∃ hg, ∀ a, (C i).point a ≫ u i ⟦g⟧ = U.datumPoint 1 (a.act ⟨g, hg⟩)}
  have mem_s {i g f} (hg : g ∈ GUPlus E D.Index)
      (h : ∀ a, (C i).point a ≫ f = U.datumPoint 1 (a.act ⟨g, hg⟩)) : g ∈ s i :=
    ⟨hg, by rwa [← eq_u i hg h]⟩
  have one_mem_s i : 1 ∈ s i :=
    mem_s (one_mem _) fun a ↦
      (pt_base i a).trans (congrArg (U.datumPoint 1) (act_eq_self a rfl).symm)
  have pt_u_one {i} a : (C i).point a ≫ u i ⟦1⟧ = U.datumPoint 1 a :=
    ((one_mem_s i).2 a).trans (congrArg (U.datumPoint 1) (act_eq_self a rfl))
  have comp_u {g hg i j f} (h : ∀ a, (C i).point a ≫ f = (C j).point (a.act ⟨g, hg⟩)) q
      (hq : q ∈ s j) : f ≫ u j ⟦q⟧ = u i ⟦g * q⟧ :=
    eq_u i (mul_mem hg hq.1) fun a ↦ by
      rw [← assoc, h, hq.2, act_mul]
      rfl
  -- `p` is a homomorphism, trivial on the normal core, so the finite group `TowerQuot D (M i)` acts
  let deck i : TowerQuot D (M i) →* End (C i).scheme := QuotientGroup.lift _
    ⟨⟨fun κ ↦ .of (p κ), End.ext <| (C i).isSeparatingFamily.hom_ext fun a ↦ by
        change (C i).point a ≫ p 1 = (C i).point a ≫ 𝟙 _
        rw [Category.comp_id, pt_p]
        exact congrArg (C i).point (act_eq_self a (by simp only [inv_one, Subgroup.coe_one]))⟩,
      fun κ₁ κ₂ ↦
        have hg : (⟨↑(κ₁ * κ₂)⁻¹, mem_GUPlus_of_mem_levelGU (κ₁ * κ₂)⁻¹.2⟩ : GUPlus E D.Index) =
            ⟨↑κ₂⁻¹, mem_GUPlus_of_mem_levelGU κ₂⁻¹.property⟩ *
              ⟨↑κ₁⁻¹, mem_GUPlus_of_mem_levelGU κ₁⁻¹.property⟩ :=
          Subtype.ext (by simp only [Submonoid.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul,
            mul_inv_rev])
        End.ext <| (C i).isSeparatingFamily.hom_ext fun a ↦ by
          change (C i).point a ≫ p (κ₁ * κ₂) = (C i).point a ≫ (p κ₂ ≫ p κ₁)
          rw [pt_p, ← assoc, pt_p, pt_p, act_mul, hg]⟩
    fun κ hκ ↦ End.ext <| (C i).hom_ext fun j ↦ by
      change p κ ≫ (C i).proj j = 𝟙 _ ≫ (C i).proj j
      rw [p_proj, Category.id_comp, (QuotientGroup.eq_one_iff κ⁻¹).2 (inv_mem hκ), one_mul]
  exact ⟨{ base := _
           cover i := (C i).scheme
           legIndices := s
           leg := u
           one_mem := one_mem_s
           eventually_translate {g} j hg := by
             -- translation by `g` lifts once `i` contains the `g`-translates of all pairs
             refine (eventually_all.2 fun x ↦ eventually_finset_mem_atTop
                 ((towerPairs D (M j) j x).1, (⟨g, hg⟩ * (towerPairs D (M j) j x).2 :))).mono
               fun i hi ↦ ?_
             obtain ⟨f, -, hf⟩ :=
               (C j).exists_lift (C' := C i) (·.act ⟨g, hg⟩)
                 (fun x ↦ (C i).proj ⟨⟦1⟧, _, mem_insert_of_mem (mem_insert_of_mem (hi x))⟩)
                 fun a x ↦ by
                   rw [(C i).point_comp_proj_towerPairs (hM i), act_mul]
                   exact congrArg (U.datumPoint _) (congrArg a.act (one_mul _))
             exact ⟨mem_s (f := f ≫ u j ⟦1⟧) hg fun a ↦ by rw [← assoc, hf, pt_u_one], f,
               comp_u hf⟩
           deckGroup i := .of (TowerQuot D (M i))
           deck := deck
           deck_comp_leg i := Quot.ind fun κ ↦ ⟨κ⁻¹, comp_u (pt_p κ)⟩
           mulMap := m
           point i := (C i).point
           point_surjective i := (C i).point_surjective pt_u_one
           point_eq_iff i a b := by
             rw [pt_u_one, pt_u_one, datumPoint_eq_iff, OneMemClass.coe_one, levelGU_inf_one]
           point_leg g α a h := by rw [← assoc, h.2, hm, pt_u_one]
           dimension := _
           smooth := smooth
           covering i := by
             refine isGaloisCovering_of_complex_points (injective_of_subalgebra_of_charZero R)
               (Quot.ind fun κ ↦ ?_) ?_ ?_
             · -- `u i ⟦1⟧` is invariant under the deck group
               exact (comp_u (pt_p κ) 1 (one_mem_s i)).trans (congrArg (u i) (QuotientGroup.eq.mpr
                 (by rw [mul_one, mul_one, Subgroup.coe_inv, inv_inv]; exact κ.property)))
             · -- its image is closed and contains the dense points `U.datumPoint 1 a`
               exact dense.surjective _ _ fun a ↦ congr($(pt_u_one a).1)
             · -- simply transitive on fibres; every complex point is some `(C i).point x`
               refine ((C i).point_surjective pt_u_one).forall₂.2 fun x y h ↦ ?_
               rw [pt_u_one, pt_u_one] at h
               obtain ⟨κ, hκ⟩ := (C i).exists_point_act_eq h
               rw [← pt_p] at hκ
               exact ⟨⟦κ⟧, hκ, Quot.ind fun κ' hκ' ↦
                 (C i).eq_of_point_comp_deck_eq hN (hM i) (fun κ a ↦ pt_p κ a) (hκ'.trans hκ.symm)⟩
           tangent i g α a z μ h :=
             (C i).isTangentPoly_localTerm_of_translate pt_u_one fun a ↦ by
               rw [← assoc, h.2, hm]
           congruence w hw i 𝔭 h𝔭 hs l f _ hq :=
             (C i).congruenceRelation hβ pt_u_one hw (hG _ hw) h𝔭 (fun A ↦ (hs A).2) hq }⟩
