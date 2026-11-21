import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeutralGroupModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOneOfPowOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianReductionAlongIsogenyStrictHenselian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSmConnOfIsProperStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosedStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusAbelianQuotientPDivisibleSmoothGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimLeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionMulCardToricTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismOpenAffineLineAbelianSchemeConst
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.InfiniteTorsionOrCocharacterOfArcAtInfinity
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfPowerSeriesArcsOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharPSpecialisationSmoothCommGroupCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsProjectiveOverRingByChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperSmoothConnGroupSchemeDvrOfProperFibres

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relDim_le_of_smooth_of_isClosedImmersion : ∀ (k : Type) [Field k] (N G : Over (Sp k)) (ν : N ⟶ G), IsClosedImmersion ν.left → Nonempty N.left → ∀ g g' : ℕ, SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension g' N.hom → g' ≤ g := by
  first | exact @GlobalTheory.relDim_le_of_isClosedImmersion | exact GlobalTheory.relDim_le_of_isClosedImmersion | (intros; apply GlobalTheory.relDim_le_of_isClosedImmersion <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusExtTorsion

theorem card_le : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsCommMonObj G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), GlobalTheory.SS.IsQuot i q → IsAbelianScheme B → ∀ a : ℕ, SmoothOfRelativeDimension a B.hom → ∀ m : ℕ, (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → s.card ≤ m ^ (Module.finrank ℤ X + 2 * a) := by
  classical
  intro k _ _ G _ hGc X _ _ _ B _ i q hQ hB a ha m hm s hs
  obtain ⟨hi, hq, -, -, -, hk, -⟩ := hQ
  haveI := hGc
  let P := 𝟙_ (Over (Sp k))
  let I := IsMonHom.monoidHom i P
  let Q := IsMonHom.monoidHom q P
  have hIinj : Function.Injective I := fun a b h => hk.hom_ext h (toUnit_unique _ _)
  have hm0 : m ≠ 0 := by rintro rfl; exact hm Nat.cast_zero

  obtain ⟨e⟩ := GlobalTheory.SemiAbTorsionCount.nonempty_torus_points_mulEquiv k X
  obtain ⟨-, hTcard⟩ := GlobalTheory.SemiAbTorsionCount.divisible_and_card e m hm
  haveI hTfin : Finite {t : P ⟶ splitTorus (Sp k) X // t ^ m = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hTcard]; exact pow_ne_zero _ hm0)
  letI : Fintype {t : P ⟶ splitTorus (Sp k) X // t ^ m = 1} := Fintype.ofFinite _

  have hBcard := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional k B a m hB ha hm
  haveI hBfin : Finite {b : P ⟶ B // b ^ m = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hBcard]; exact pow_ne_zero _ hm0)

  have himg : (s.image Q).card ≤ m ^ (2 * a) := by
    rw [← hBcard, ← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective (fun y => ⟨y.1, ?_⟩) (fun y z h => Subtype.ext (congrArg Subtype.val h :))
    obtain ⟨x, hx, hy⟩ := Finset.mem_image.1 y.2
    rw [← hy, ← map_pow, hs x hx, map_one]

  have hfib : ∀ b ∈ s.image Q, (s.filter (fun x => Q x = b)).card ≤ m ^ Module.finrank ℤ X := by
    intro b hb
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hb
    have hsub : s.filter (fun x => Q x = Q x₀) ⊆
        Finset.univ.image (fun t : {t : P ⟶ splitTorus (Sp k) X // t ^ m = 1} => x₀ * I t.1) := by
      intro x hx
      obtain ⟨hxs, hxq⟩ := Finset.mem_filter.1 hx
      have hy : (x₀⁻¹ * x) ≫ q = 1 := by
        change Q (x₀⁻¹ * x) = 1
        rw [map_mul, map_inv, hxq, inv_mul_cancel]
      let t := hk.lift (x₀⁻¹ * x) (toUnit _) (by rw [hy, Hom.one_def])
      have ht : I t = x₀⁻¹ * x := hk.lift_fst _ _ _
      have htm : t ^ m = 1 := by
        apply hIinj
        rw [map_pow, ht, map_one, mul_pow, inv_pow, hs x hxs, hs x₀ hx₀, inv_one, _root_.one_mul]
      refine Finset.mem_image.2 ⟨⟨t, htm⟩, Finset.mem_univ _, ?_⟩
      change x₀ * I t = x
      rw [ht, mul_inv_cancel_left]
    calc (s.filter (fun x => Q x = Q x₀)).card ≤ _ := Finset.card_le_card hsub
      _ ≤ Finset.univ.card := Finset.card_image_le
      _ = m ^ Module.finrank ℤ X := by rw [Finset.card_univ, Fintype.card_eq_nat_card, hTcard]
  calc s.card ≤ m ^ Module.finrank ℤ X * (s.image Q).card := Finset.card_le_mul_card_image s _ hfib
    _ ≤ m ^ Module.finrank ℤ X * m ^ (2 * a) := Nat.mul_le_mul_left _ himg
    _ = m ^ (Module.finrank ℤ X + 2 * a) := (pow_add _ _ _).symm

end GlobalTheory.TorusExtTorsion
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_torsion_torusExtension_abelianVariety_le : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsCommMonObj G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), GlobalTheory.SS.IsQuot i q → IsAbelianScheme B → ∀ a : ℕ, SmoothOfRelativeDimension a B.hom → ∀ m : ℕ, (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → s.card ≤ m ^ (Module.finrank ℤ X + 2 * a) := by
  atlas_forward_decl GlobalTheory.TorusExtTorsion.card_le
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SS

theorem isProper_of_isQuot_of_finrank_eq_zero : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), GlobalTheory.SS.IsQuot i q → IsAbelianScheme B → Module.finrank ℤ X = 0 → IsProper G.hom := by
  intro k _ _ G _ X _ _ _ B _ i q hQ hB hX
  obtain ⟨hi, hq, hf, hsu, ha, hp, -⟩ := hQ
  have hsub : Subsingleton X := Module.finrank_zero_iff.1 hX
  have : Mono q := ⟨fun {Y} x y hxy => by
    have h1 : (x * y⁻¹) ≫ q = toUnit _ ≫ η[B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
      rfl
    have h2 : hp.lift _ _ h1 = 1 := by
      apply (GlobalTheory.splitTorusPointsEquiv (Sp k) X Y).injective
      refine MonoidHom.ext fun a => ?_
      have ha1 : a = 1 := by
        show a = Multiplicative.ofAdd 0
        rw [← ofAdd_toAdd a, Subsingleton.elim (Multiplicative.toAdd a) 0]
      rw [ha1, map_one, map_one]
    have h3 := hp.lift_fst _ _ h1
    rw [h2, MonObj.one_comp] at h3
    exact mul_inv_eq_one.1 h3.symm⟩
  have : Mono q.left := inferInstanceAs (Mono ((Over.forget _).map q))
  have := hB.proper
  have : Flat q.left := hf
  have : Surjective q.left := hsu
  have : IsAffineHom q.left := ha
  have : IsIso q.left := Flat.isIso_of_surjective_of_mono q.left
  rw [← Over.w q]
  infer_instance

end GlobalTheory.SS
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_isQuot_abelian_of_finrank_eq_zero : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), GlobalTheory.SS.IsQuot i q → IsAbelianScheme B → Module.finrank ℤ X = 0 → IsProper G.hom := by
  atlas_forward_decl GlobalTheory.SS.isProper_of_isQuot_of_finrank_eq_zero
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SerreTateProperness

theorem main : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → m ^ (2 * g) < m * s.card → IsProper G.hom := by
  intro k _ _ p _ _ G _ hG g hg m hm s hs hcard
  classical
  obtain ⟨N, _, ν, hN, hνmon, hνci, hpdiv, hlift, -, hdim⟩ :=
    GlobalTheory.DivisiblePart.exists_divisiblePart k p G hG
  obtain ⟨g', hg', hiso⟩ := hdim g hg
  obtain ⟨X, _, _, _, B, _, i, q, hq, hB, hdimB⟩ :=
    GlobalTheory.SS.DivSemi.exists_torus_abelian_quotient k p N hN hpdiv
  obtain ⟨a, ha, hga⟩ := hdimB g' hg'

  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have hcop : m.Coprime p := by
    have hnd : ¬ p ∣ m := fun h => hm ((CharP.cast_eq_zero_iff k p m).mpr h)
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr hnd)

  have hmono : Mono ν.left := inferInstance
  have hinj : ∀ y y' : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = y' ≫ ν → y = y' := by
    intro y y' h
    ext1
    exact (cancel_mono ν.left).mp (by simpa using congrArg CommaMorphism.left h)

  have hlift' : ∀ x ∈ s, ∃ y : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = x ∧ y ^ m = 1 := by
    intro x hx
    obtain ⟨y, hy⟩ := hlift x m hcop hm0 (hs x hx)
    refine ⟨y, hy, hinj _ _ ?_⟩
    rw [MonObj.pow_comp, hy, hs x hx, MonObj.one_comp]
  choose! f hf1 hf2 using hlift'
  have hfinj : Set.InjOn f s := by
    intro x hx x' hx' h
    rw [← hf1 x hx, ← hf1 x' hx', h]
  have hcardN : (s.image f).card ≤ m ^ (Module.finrank ℤ X + 2 * a) := by
    refine GlobalTheory.T.card_torsion_torusExtension_abelianVariety_le k N hN.1 X B i q hq hB a ha m hm (s.image f) ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hf2 x hx
  rw [Finset.card_image_of_injOn hfinj] at hcardN

  have hpt : Nonempty (𝟙_ (Over (Sp k))).left := by
    change Nonempty (Sp k)
    first
    | infer_instance
    | exact ⟨IsLocalRing.closedPoint k⟩
  have hne : Nonempty N.left := ⟨(1 : 𝟙_ (Over (Sp k)) ⟶ N).left hpt.some⟩
  have hgle : g' ≤ g := GlobalTheory.T.relDim_le_of_smooth_of_isClosedImmersion k N G ν hνci hne g g' hg hg'

  have hm1 : 1 < m := by
    rcases Nat.lt_or_ge 1 m with h | h
    · exact h
    · exfalso
      have : m = 1 := by omega
      subst this
      simp at hcard hcardN
      omega
  have hlt : m ^ (2 * g) < m ^ (Module.finrank ℤ X + 2 * a + 1) := by
    calc m ^ (2 * g) < m * s.card := hcard
      _ ≤ m * m ^ (Module.finrank ℤ X + 2 * a) := Nat.mul_le_mul_left m hcardN
      _ = m ^ (Module.finrank ℤ X + 2 * a + 1) := by ring
  have hexp := (Nat.pow_lt_pow_iff_right (by omega)).mp hlt
  have ht : Module.finrank ℤ X = 0 := by omega
  have hgg : g ≤ g' := by omega
  haveI hP : IsProper N.hom := GlobalTheory.T.isProper_of_isQuot_abelian_of_finrank_eq_zero k N X B i q hq hB ht
  haveI : IsIso ν.left := by
    haveI := hiso hgg
    exact Functor.map_isIso (Over.forget (Sp k)) ν
  have hw : G.hom = inv ν.left ≫ N.hom := by
    rw [← Over.w ν]
    simp
  rw [hw]
  infer_instance

end GlobalTheory.SerreTateProperness
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_smoothConnGroup_of_many_torsion_charP : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → m ^ (2 * g) < m * s.card → IsProper G.hom := by
  atlas_forward_decl GlobalTheory.SerreTateProperness.main
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SS.ArcInf
variable {k : Type} [Field k] [IsAlgClosed k]

theorem exists_eval_ne_zero_of_ne_zero {p : Polynomial k} (hp : p ≠ 0) : ∃ t, p.eval t ≠ 0 := by
  by_contra h
  push_neg at h
  exact hp (Polynomial.funext fun t => by rw [h t, Polynomial.eval_zero])

theorem comp_linear_ne_zero {p : Polynomial k} (hp : p ≠ 0) {c e : k} (hc : c ≠ 0) :
    p.comp (Polynomial.C c * Polynomial.X + Polynomial.C e) ≠ 0 := by
  intro h
  rw [Polynomial.comp_eq_zero_iff] at h
  rcases h with h | ⟨-, h⟩
  · exact hp h
  · have := congrArg (Polynomial.coeff · 1) h
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_one, Polynomial.coeff_C,
      one_ne_zero, if_false, mul_one, add_zero] at this
    exact hc (by simpa using this)

theorem exists_rational_family {G : Over (Sp k)} [GrpObj G] (hG : SmConn G)
    (a : algOver k (FractionRing (PowerSeries k)) ⟶ G)
    (hna : ¬ ∃ b : algOver k (PowerSeries k) ⟶ G, algOverHom (toK k) ≫ b = a) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ)
      (f : Fin r → A) (Pd : Polynomial k) (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k)) (t₁ t₂ : k),
      IsChart G j ε f ∧ Pd ≠ 0 ∧ (∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) ∧
      Pd.eval t₁ ≠ 0 ∧ Pd.eval t₂ ≠ 0 ∧ ψ t₁ ≠ ψ t₂ := by
  obtain ⟨A, _, _, j, ε, r, f, hc⟩ := GlobalTheory.T.exists_affineUnitChart_smoothGroupScheme k G hG
  obtain ⟨h, d, hd1, hh1, ht⟩ := GlobalTheory.T.exists_arcQuotient_twoVariable_coords k G A j ε r f hc a
  have hsep := hG.2.2.1
  have hXd := mt ((GlobalTheory.T.subst_two_variables_identities_alt k).1 d).1.1 hd1
  have hXh := fun i => ((GlobalTheory.T.subst_two_variables_identities_alt k).1 (h i)).1.2 (hh1 i)
  have hd' : (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) d) ≠ 0 := fun e => hXd (e ▸ dvd_zero _)
  have hd : d ≠ 0 := by
    rintro rfl
    apply hd1
    rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
      fun i => by fin_cases i <;> exact PowerSeries.constantCoeff_X), map_zero]
  by_cases hQ : ∀ i, MvPowerSeries.weightedOrder (![1, 1] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) d) < MvPowerSeries.weightedOrder (![1, 1] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) (h i))
  · exfalso
    obtain ⟨Pd, P, ψ, hPd, hP, hg⟩ := ht.shear hc hd' le_rfl le_rfl (fun i => (hQ i).le)
    obtain ⟨ch1, ch2⟩ := GlobalTheory.T.relation_of_gen_of_order_eq k (fun z w => Rel a z w 1)
      (fun m n => ∀ z : PowerSeries k, z.order = (m : ℕ∞) →
        ∃ S : Set k, S.Finite ∧ ∀ t, t ∉ S → Rel a z (PowerSeries.C t * PowerSeries.X ^ n) 1)
      (fun z w h => by simpa using h.symm) (fun x y z h h' => by simpa using h.trans h') (fun _ _ h => h)
    have g11 := ch1 1 1 (fun z hz => by
      have hz0 := coeff_ne_of_order hz
      refine ⟨insert 0 ((fun t => (t + 1) * PowerSeries.coeff 1 z) '' {t | Pd.IsRoot t}),
        ((Polynomial.finite_setOfPred_isRoot hPd).image _).insert _, fun t hS => ?_⟩
      have e : t / PowerSeries.coeff 1 z * PowerSeries.coeff 1 z = t := div_mul_cancel₀ _ hz0
      have ht0 : t ≠ 0 := fun e => hS (Or.inl e)
      have hp : Pd.eval (t / PowerSeries.coeff 1 z - 1) ≠ 0 := fun e' =>
        hS (Or.inr ⟨_, e', by simp only [sub_add_cancel, e]⟩)
      obtain ⟨h1, h2⟩ := mul_step le_rfl hg z hz _ (div_ne_zero ht0 hz0) hp
      have : ψ (t / PowerSeries.coeff 1 z - 1) = ε := hc.hom_ext fun i => by
        have := h1 i
        rw [(hP i).2 (hQ i), Polynomial.eval_zero, mul_eq_zero] at this
        rw [hc.2.2.2, this.resolve_right hp]
      rwa [this, hc.2.1, e] at h2)
    obtain ⟨-, s2, s3, s4⟩ := GlobalTheory.T.weightedOrder_slope_comparison_alt k r h d hd _ (fun _ _ => Iff.rfl)
    obtain ⟨m₀, hm₀⟩ := s2 (ht.lt_of_rel hc hd le_rfl le_rfl g11)
    have all := ch2 (m₀ + 1) fun m hm =>
      ht.gen_of_lt hc hd (m := m) (n := m + 1) (by omega) (by omega) (hm₀ m (by omega))
    refine hna (GlobalTheory.T.arc_extends_of_regular_second_axis k G A j ε r f hc a h d hd ht (s4 fun n hn => ?_))
    refine (s3 1 n (m₀ + 1) (by omega)).1 (ht.lt_of_rel hc hd (by omega) (Nat.mul_pos (by omega) hn) ?_)
    intro z w hz hw
    exact all _ _ z w (by omega) (Nat.le_mul_of_pos_right _ hn) hz hw
  · obtain ⟨m, n, hm, hmn, hle, i, hi⟩ := (GlobalTheory.T.weightedOrder_slope_comparison_alt k r (fun i => (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) (h i))) _ hd' _
      (fun _ _ => Iff.rfl)).1 hXh hXd ⟨1, 1, le_rfl, le_rfl, hQ⟩
    obtain ⟨Pd, P, ψ, hPd, hP, hg⟩ := ht.shear hc hd' hm (hm.trans hmn) hle
    have hPi : P i ≠ 0 := fun e => ((hP i).1 e).ne hi
    have triv : ∀ t, Pd.eval t ≠ 0 → (∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) →
        algOverHom (ψ t) ≫ j = 1 → (P i).eval t = 0 := fun t ht h1 h => by
      have e : ψ t = ε := eq_of_comp_eq hc.1 (h.trans hc.2.1.symm)
      rw [← h1 i, e, hc.2.2.2 i, zero_mul]
    rcases hmn.lt_or_eq with hlt | rfl
    · have hψ : ∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t :=
        fun t ht => (add_step hlt hg 0 t ht).1
      have hmul : ∀ t t', Pd.eval t ≠ 0 → Pd.eval t' ≠ 0 → Pd.eval (t + t') ≠ 0 →
          (algOverHom (ψ t) ≫ j) * (algOverHom (ψ t') ≫ j) = algOverHom (ψ (t + t')) ≫ j := by
        intro t t' h1 h2 h3
        have e1 := (add_step hlt hg 0 t' h2).2
        have e2 := (add_step hlt hg (t' + 0) t h1).2
        have e3 := (add_step hlt hg 0 (t + t') h3).2
        rw [_root_.add_assoc] at e3
        exact Red.unique hsep (e1.trans e2) e3
      obtain ⟨t', ht'⟩ := exists_eval_ne_zero_of_ne_zero hPd
      obtain ⟨t, ht⟩ := exists_eval_ne_zero_of_ne_zero (mul_ne_zero (mul_ne_zero hPd hPi)
        (comp_linear_ne_zero hPd (one_ne_zero (α := k)) (e := t')))
      simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_X, _root_.one_mul, ne_eq, mul_eq_zero, not_or] at ht
      obtain ⟨⟨hpt, hpi⟩, hpt2⟩ := ht
      refine ⟨A, _, _, j, ε, r, f, Pd, P, ψ, t + t', t', hc, hPd, hψ, hpt2, ht', fun e => hpi ?_⟩
      have h := hmul t t' hpt ht' hpt2
      rw [e] at h
      exact triv t hpt (hψ t hpt) (mul_eq_right.1 h)
    · have ev : ∀ (q : Polynomial k) (t : k), (q.comp (Polynomial.X - Polynomial.C 1)).eval t = q.eval (t - 1) :=
        fun q t => by simp
      have hψ : ∀ t, t ≠ 0 → Pd.eval (t - 1) ≠ 0 → ∀ i, ψ (t - 1) (f i) * Pd.eval (t - 1) = (P i).eval (t - 1) :=
        fun t h0 h1 => (mul_step hm hg _ (order_mon one_ne_zero m) t h0 h1).1
      have hmul : ∀ t t', t ≠ 0 → t' ≠ 0 → Pd.eval (t - 1) ≠ 0 → Pd.eval (t' - 1) ≠ 0 → Pd.eval (t * t' - 1) ≠ 0 →
          (algOverHom (ψ (t - 1)) ≫ j) * (algOverHom (ψ (t' - 1)) ≫ j) = algOverHom (ψ (t * t' - 1)) ≫ j := by
        intro t t' h0 h0' h1 h2 h3
        have e1 := (mul_step hm hg _ (order_mon one_ne_zero m) t' h0' h2).2
        have e3 := (mul_step hm hg _ (order_mon one_ne_zero m) _ (mul_ne_zero h0 h0') h3).2
        rw [coeff_mon, _root_.mul_one] at e1 e3
        have e2 := (mul_step hm hg _ (order_mon h0' m) t h0 h1).2
        rw [coeff_mon] at e2
        exact Red.unique hsep (e1.trans e2) e3
      have hQ1 : Pd.comp (Polynomial.C 1 * Polynomial.X + Polynomial.C (-1)) ≠ 0 :=
        comp_linear_ne_zero hPd one_ne_zero
      have hQ2 : (P i).comp (Polynomial.C 1 * Polynomial.X + Polynomial.C (-1)) ≠ 0 :=
        comp_linear_ne_zero hPi one_ne_zero
      obtain ⟨t', ht'⟩ := exists_eval_ne_zero_of_ne_zero (mul_ne_zero Polynomial.X_ne_zero hQ1)
      simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_X, _root_.one_mul, ne_eq, mul_eq_zero, not_or, ← sub_eq_add_neg] at ht'
      obtain ⟨h0', hpt'⟩ := ht'
      obtain ⟨t, ht⟩ := exists_eval_ne_zero_of_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        Polynomial.X_ne_zero hQ1) hQ2) (comp_linear_ne_zero hPd h0' (e := -1)))
      simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_X, _root_.one_mul, ne_eq, mul_eq_zero, not_or, ← sub_eq_add_neg] at ht
      obtain ⟨⟨⟨h0, hpt⟩, hpi⟩, hpt2⟩ := ht
      rw [mul_comm t' t] at hpt2
      refine ⟨A, _, _, j, ε, r, f, Polynomial.X * Pd.comp (Polynomial.X - Polynomial.C 1),
        fun i => Polynomial.X * (P i).comp (Polynomial.X - Polynomial.C 1), fun t => ψ (t - 1), t * t', t', hc,
        mul_ne_zero Polynomial.X_ne_zero (mt comp_sub_one_eq_zero.1 hPd), fun s hs i => ?_, ?_, ?_, fun e => hpi ?_⟩
      · rw [Polynomial.eval_mul, Polynomial.eval_X, ev] at hs
        rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_X, ev, ev,
          ← hψ s (left_ne_zero_of_mul hs) (right_ne_zero_of_mul hs) i]
        ring
      · rw [Polynomial.eval_mul, Polynomial.eval_X, ev]
        exact mul_ne_zero (mul_ne_zero h0 h0') hpt2
      · rw [Polynomial.eval_mul, Polynomial.eval_X, ev]
        exact mul_ne_zero h0' hpt'
      · have h := hmul t t' h0 h0' hpt hpt' hpt2
        have e' : ψ (t * t' - 1) = ψ (t' - 1) := e
        rw [e'] at h
        exact triv (t - 1) hpt (hψ t h0 hpt) (mul_eq_right.1 h)

end GlobalTheory.SS.ArcInf

noncomputable section
namespace GlobalTheory.RatCurve
open GlobalTheory.SS GlobalTheory.SS.ArcInf

section Curve
variable {k : Type} [Field k]

def evAway (Pd : Polynomial k) (t : k) (ht : Pd.eval t ≠ 0) : Localization.Away Pd →ₐ[k] k :=
  { IsLocalization.Away.lift Pd (g := Polynomial.evalRingHom t) (IsUnit.mk0 _ ht) with
    commutes' := fun c => by
      show IsLocalization.Away.lift Pd _ (algebraMap k (Localization.Away Pd) c) = c
      rw [IsScalarTower.algebraMap_apply k (Polynomial k) (Localization.Away Pd)]
      simp [IsLocalization.Away.lift] }

theorem evAway_alg (Pd : Polynomial k) (t : k) (ht : Pd.eval t ≠ 0) (q : Polynomial k) :
    evAway Pd t ht (algebraMap _ _ q) = q.eval t := by
  simp [evAway, IsLocalization.Away.lift]

theorem evAway_invSelf (Pd : Polynomial k) (t : k) (ht : Pd.eval t ≠ 0) :
    evAway Pd t ht (IsLocalization.Away.invSelf Pd) = (Pd.eval t)⁻¹ := by
  have h := congrArg (evAway Pd t ht) (IsLocalization.Away.mul_invSelf (S := Localization.Away Pd) Pd)
  rw [map_mul, evAway_alg, map_one] at h
  exact eq_inv_of_mul_eq_one_right h

theorem eq_zero_of_evAway [Infinite k] {Pd : Polynomial k} (hPd : Pd ≠ 0) (x : Localization.Away Pd)
    (hx : ∀ t (ht : Pd.eval t ≠ 0), evAway Pd t ht x = 0) : x = 0 := by
  obtain ⟨⟨Q, ⟨_, n, rfl⟩⟩, hQ⟩ := IsLocalization.surj (Submonoid.powers Pd) x
  have hQ0 : Q * Pd = 0 := by
    refine Polynomial.funext fun t => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_zero]
    by_cases ht : Pd.eval t = 0
    · rw [ht, mul_zero]
    · have := congrArg (evAway Pd t ht) hQ
      simp only [map_mul, evAway_alg, hx t ht, zero_mul] at this
      rw [← this, zero_mul]
  have hQ' : Q = 0 := (mul_eq_zero.1 hQ0).resolve_right hPd
  simp only [hQ', map_zero] at hQ
  exact (IsLocalization.map_units (Localization.Away Pd) (⟨Pd ^ n, n, rfl⟩ : Submonoid.powers Pd)).mul_left_eq_zero.1 hQ

variable [Infinite k] {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A]
  {j : algOver k A ⟶ G} {ε : A →ₐ[k] k} {r : ℕ} {f : Fin r → A}

theorem exists_algHom_of_family (hc : IsChart G j ε f) {Pd : Polynomial k} (hPd : Pd ≠ 0)
    (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k))
    (hψ : ∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) :
    ∃ Ψ : A →ₐ[k] Localization.Away Pd, ∀ t (ht : Pd.eval t ≠ 0), (evAway Pd t ht).comp Ψ = ψ t := by
  let g : Fin r → Localization.Away Pd := fun i =>
    algebraMap (Polynomial k) _ (P i) * IsLocalization.Away.invSelf Pd
  have hg : ∀ t (ht : Pd.eval t ≠ 0) i, evAway Pd t ht (g i) = ψ t (f i) := fun t ht i => by
    simp only [g, map_mul, evAway_alg, evAway_invSelf]
    rw [← hψ t ht i, mul_inv_cancel_right₀ ht]
  let φ : MvPolynomial (Fin r) k →ₐ[k] A := MvPolynomial.aeval f
  have hsurj : Function.Surjective φ := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
    exact hc.2.2.1
  let Φ : MvPolynomial (Fin r) k →ₐ[k] Localization.Away Pd := MvPolynomial.aeval g
  have hev : ∀ t (ht : Pd.eval t ≠ 0), (evAway Pd t ht).comp Φ = (ψ t).comp φ := fun t ht => by
    rw [MvPolynomial.comp_aeval, MvPolynomial.comp_aeval]
    exact congrArg _ (funext (hg t ht))
  have hker : RingHom.ker φ ≤ RingHom.ker Φ := fun p hp => by
    rw [RingHom.mem_ker] at hp ⊢
    refine eq_zero_of_evAway hPd _ fun t ht => ?_
    have := AlgHom.congr_fun (hev t ht) p
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at this
    rw [this, show φ p = 0 from hp, map_zero]
  let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let Ψ : A →ₐ[k] Localization.Away Pd :=
    (Ideal.Quotient.liftₐ (RingHom.ker φ) Φ fun p hp => hker hp).comp e.symm.toAlgHom
  have hΨ : Ψ.comp φ = Φ := by
    ext p
    simp only [Ψ, AlgHom.comp_apply]
    have : e.symm (φ (MvPolynomial.X p)) = Ideal.Quotient.mk _ (MvPolynomial.X p) := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    change (Ideal.Quotient.liftₐ (RingHom.ker φ) Φ _) (e.symm (φ (MvPolynomial.X p))) = _
    rw [this]
    rfl
  refine ⟨Ψ, fun t ht => ?_⟩
  refine AlgHom.ext fun x => ?_
  obtain ⟨p, rfl⟩ := hsurj x
  have := AlgHom.congr_fun (hev t ht) p
  rw [← hΨ] at this
  simpa only [AlgHom.comp_apply] using this

theorem curve_of_family (hc : IsChart G j ε f) {Pd : Polynomial k} (hPd : Pd ≠ 0)
    (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k))
    (hψ : ∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) {t₁ t₂ : k}
    (h₁ : Pd.eval t₁ ≠ 0) (h₂ : Pd.eval t₂ ≠ 0) (hne : ψ t₁ ≠ ψ t₂) :
    ∃ (P : Polynomial k) (_ : P ≠ 0) (u : Sp (Localization.Away P) ⟶ G.left)
      (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) ∧
      spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u := by
  obtain ⟨Ψ, hΨ⟩ := exists_algHom_of_family hc hPd P ψ hψ
  refine ⟨Pd, hPd, (algOverHom Ψ ≫ j).left, evAway Pd t₁ h₁, evAway Pd t₂ h₂, Over.w _, fun e => hne ?_⟩
  have key : ∀ t (ht : Pd.eval t ≠ 0), spMap (evAway Pd t ht).toRingHom ≫ (algOverHom Ψ ≫ j).left =
      (algOverHom (ψ t) ≫ j).left := fun t ht => by
    rw [← hΨ t ht, algOverHom_comp, Over.comp_left, Over.comp_left, Over.comp_left, algOverHom_left]
    rfl
  rw [key, key] at e
  exact eq_of_comp_eq hc.1 (Over.OverMorphism.ext e)

end Curve
end GlobalTheory.RatCurve

namespace GlobalTheory.RatCurve
open GlobalTheory.SS GlobalTheory.SS.ArcInf

theorem exists_rational_curve : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G],
    GlobalTheory.SS.SmConn G → ¬ IsProper G.hom → ∃ (P : Polynomial k) (_ : P ≠ 0) (u : Sp (Localization.Away P) ⟶ G.left)
      (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) ∧
      spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u := by
  intro k _ _ G _ hG hnp
  have : Smooth G.hom := hG.2.1
  have : GeometricallyConnected G.hom := hG.2.2.2.2
  have : IsIntegral G.left := GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected G.hom
  have harc : ∃ a : Sp (FractionRing (PowerSeries k)) ⟶ G.left,
      a ≫ G.hom = spMap (algebraMap k (FractionRing (PowerSeries k))) ∧
      ¬ ∃ b : Sp (PowerSeries k) ⟶ G.left, spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a := by
    by_contra hno
    refine hnp (GlobalTheory.ArcProper.isProper_of_arcs k G hG.2.2.1 inferInstance hG.2.2.2.1 fun a ha => ?_)
    by_contra hb
    exact hno ⟨a, ha, hb⟩
  obtain ⟨a, ha, hna⟩ := harc
  obtain ⟨A, _, _, j, ε, r, f, Pd, P, ψ, t₁, t₂, hc, hPd, hψ, h₁, h₂, hne⟩ :=
    exists_rational_family hG (Over.homMk a ha) (by
      rintro ⟨b, hb⟩
      exact hna ⟨b.left, congrArg (fun x => x.left) hb⟩)
  exact curve_of_family hc hPd P ψ hψ h₁ h₂ hne

end GlobalTheory.RatCurve
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonconstant_rational_curve_nonproper_group : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ¬ IsProper G.hom → ∃ (P : Polynomial k) (_ : P ≠ 0) (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) ∧ spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u := by
  atlas_forward_decl GlobalTheory.RatCurve.exists_rational_curve
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ManyTorsionProper

theorem isProper_of_many_torsion_charZero : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → m ^ (2 * g) < m * s.card → IsProper G.hom := by
  intro k _ _ _ G _ hG g hg m s hs hcard
  by_contra hnp
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp at hcard
    · exact h
  obtain ⟨P, hP, u, a, b, hu, hab⟩ := GlobalTheory.T.exists_nonconstant_rational_curve_nonproper_group k G hG hnp
  obtain ⟨k', _, _, p, _, _, G', _, hG', hg', hm', ⟨s', hs', hc'⟩, P', hP', u', a', b', hu', hab'⟩ :=
    GlobalTheory.T.exists_charP_specialization_smooth_commGroup_curve k G hG g hg m hm s hs P hP u a b hu hab
  have hpr : IsProper G'.hom :=
    GlobalTheory.T.isProper_smoothConnGroup_of_many_torsion_charP k' p G' hG' g hg' m hm' s' hs' (by rw [hc']; exact hcard)
  exact hab' (GlobalTheory.T.morphism_open_affine_line_abelianScheme_const k' G' (GlobalTheory.T.isAbelianScheme_of_smConn_of_isProper' _ G' hG' hpr) P' hP' u' a' b' hu')

end GlobalTheory.ManyTorsionProper
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_many_torsion_points_charZero : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → m ^ (2 * g) < m * s.card → IsProper G.hom := by
  atlas_forward_decl GlobalTheory.ManyTorsionProper.isProper_of_many_torsion_charZero
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.properOfInfinitelyManyLargeTorsionCounts :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G →
      ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ C : ℕ,
      {m : ℕ | (m : k) ≠ 0 ∧ ∃ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) ∧
        m ^ (2 * g) ≤ C * s.card}.Infinite → IsProper G.hom := by
  intro k _ _ G _ hG g hsm C hinf
  obtain ⟨m, ⟨hm0, s, hs, hle⟩, hCm⟩ := hinf.exists_gt C
  have hm1 : 1 ≤ m := by omega
  have hcard : 0 < s.card := by
    rcases Nat.eq_zero_or_pos s.card with h | h
    · rw [h, Nat.mul_zero] at hle
      have : 0 < m ^ (2 * g) := Nat.pow_pos hm1
      omega
    · exact h
  have hlt : m ^ (2 * g) < m * s.card :=
    lt_of_le_of_lt hle (Nat.mul_lt_mul_of_pos_right hCm hcard)
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hpp | hp0
  · haveI : Fact p.Prime := ⟨hpp⟩
    exact GlobalTheory.T.isProper_smoothConnGroup_of_many_torsion_charP k p G hG g hsm m hm0 s hs hlt
  · subst hp0
    haveI : CharZero k := CharP.charP_to_charZero k
    exact GlobalTheory.T.isProper_of_many_torsion_points_charZero k G hG g hsm m s hs hlt
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_infinitely_many_large_torsion : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ C : ℕ, {m : ℕ | (m : k) ≠ 0 ∧ ∃ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) ∧ m ^ (2 * g) ≤ C * s.card}.Infinite → IsProper G.hom := by
  atlas_forward_decl GlobalTheory.properOfInfinitelyManyLargeTorsionCounts
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_smoothConnGroupScheme_dvr_of_proper_fibres : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], GlobalTheory.SS.SmConn G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → IsProper (GlobalTheory.SS.spFibre G).hom → IsProper G.hom := by
  first | exact @GlobalTheory.GoodRedProper.isProper_of_proper_fibres | exact GlobalTheory.GoodRedProper.isProper_of_proper_fibres | (intros; apply GlobalTheory.GoodRedProper.isProper_of_proper_fibres <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GoodRedTorsion

def secHom {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] :
    (𝟙_ (Over S) ⟶ G) →* (𝟙_ (Over T) ⟶ (Over.pullback f).obj G) :=
  (GlobalTheory.RedPts.precomp _ (Functor.LaxMonoidal.ε (Over.pullback f))).comp (Over.pullback f).homMonoidHom

theorem secHom_apply {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] (s : 𝟙_ (Over S) ⟶ G) :
    secHom f G s = GlobalTheory.IsogRed.sec f s := rfl

theorem card_le_of_fibres {M N : Type} [CommGroup M] [DecidableEq N] (TF : Finset M) (m c B : ℕ)
    (hT : ∀ a ∈ TF, a ^ m = 1) (F : M → N)
    (hF : ∀ a ∈ TF, ∀ b ∈ TF, F a = F b → a ^ c = b ^ c)
    (hfin : {x : M | x ^ Nat.gcd m c = 1}.Finite) (hB : {x : M | x ^ Nat.gcd m c = 1}.ncard ≤ B) :
    TF.card ≤ B * (TF.image F).card := by
  classical
  refine Finset.card_le_mul_card_image TF B fun y hy => ?_
  obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.1 hy
  calc (TF.filter fun x => F x = F a0).card ≤ hfin.toFinset.card := by
        refine Finset.card_le_card_of_injOn (fun a => a * a0⁻¹) ?_ ?_
        · intro a ha
          have ha' : a ∈ TF.filter fun x => F x = F a0 := by simpa using ha
          obtain ⟨haT, haF⟩ := Finset.mem_filter.1 ha'
          have h1 : (a * a0⁻¹) ^ m = 1 := by rw [mul_pow, inv_pow, hT a haT, hT a0 ha0]; simp
          have h2 : (a * a0⁻¹) ^ c = 1 := by rw [mul_pow, inv_pow, hF a haT a0 ha0 haF, mul_inv_cancel]
          simpa using pow_gcd_eq_one.2 ⟨h1, h2⟩
        · intro a _ b _ h
          simpa using h
    _ = {x : M | x ^ Nat.gcd m c = 1}.ncard := (Set.ncard_eq_toFinset_card _ hfin).symm
    _ ≤ B := hB

theorem torsion_finite_ncard_le (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (g : ℕ) (hg : SmoothOfRelativeDimension g A.hom) (d : ℕ) (hd : (d : K) ≠ 0) :
    {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ d = 1}.Finite ∧
      {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ d = 1}.ncard ≤ d ^ (2 * g) := by
  have hc := GlobalTheory.T.card_abelianVariety_torsion_sepClosed K (AlgebraicClosure K) A hA g hg d hd
  let u : ptOver K (AlgebraicClosure K) ⟶ 𝟙_ (Over (Sp K)) := toUnit _
  have hu : u.left = spMap (algebraMap K (AlgebraicClosure K)) := by simpa using Over.w u
  have hdom : IsDominant (spMap (algebraMap K (AlgebraicClosure K))) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap K (AlgebraicClosure K)) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap K (AlgebraicClosure K)).injective]; exact bot_le)⟩
  have : IsProper A.hom := hA.proper
  have hinj : Function.Injective (fun x : 𝟙_ (Over (Sp K)) ⟶ A => u ≫ x) := by
    intro x y h
    have h' : spMap (algebraMap K (AlgebraicClosure K)) ≫ x.left = spMap (algebraMap K (AlgebraicClosure K)) ≫ y.left := by
      rw [← hu]; exact congrArg Over.Hom.left h
    exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp K) A.hom
      ((Over.w x).trans (Over.w y).symm) (spMap (algebraMap K (AlgebraicClosure K))) h')
  have hd0 : d ≠ 0 := by rintro rfl; exact hd Nat.cast_zero
  have hfinB : Finite {x : ptOver K (AlgebraicClosure K) ⟶ A // x ^ d = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hd0)
  let φ : {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ d = 1} → {x : ptOver K (AlgebraicClosure K) ⟶ A // x ^ d = 1} :=
    fun x => ⟨u ≫ x.1, by rw [← MonObj.comp_pow, x.2, MonObj.comp_one]⟩
  have hφ : Function.Injective φ := fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))
  have : Finite {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ d = 1} := Finite.of_injective φ hφ
  refine ⟨Set.toFinite _, ?_⟩
  rw [← Nat.card_coe_set_eq, ← hc]
  exact Nat.card_le_card_of_injective φ hφ

end GlobalTheory.GoodRedTorsion

namespace GlobalTheory.GoodRedTorsion

theorem hasGoodReduction_of_torsion : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], GlobalTheory.SS.SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → {m : ℕ | (m : ResidueField R) ≠ 0 ∧ Nat.card {x : 𝟙_ (Over (Sp K)) ⟶ A // x ^ m = 1} = m ^ (2 * g)}.Infinite → HasGoodReduction R K A := by
  intro R K _ _ _ _ _ hS A _ _ hA g hg hinf
  obtain ⟨G, inst, hG, he, c, hc, hs⟩ :=
    GlobalTheory.SS.exists_neutral_group_model R K hS A hA (GlobalTheory.T.abelianVariety_isProjectiveOverRingByCharts K A hA)
  obtain ⟨hDVR, hHen, hAC, hFR⟩ := hS
  have := hG.1
  have := hG.2.1
  have := hG.2.2.1
  have := GlobalTheory.schemeTheoreticallyDominant_fractionField R K
  have heL : IsIso G.e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map G.e.hom))
  have hgenP : IsProper ((Over.pullback (spMap (algebraMap R K))).obj G.Y).hom := by
    rw [← Over.w G.e.hom]; have := hA.proper; infer_instance
  have hGg : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K))).obj G.Y).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_horiz_isIso (g := 𝟙 _) ⟨(Over.w G.e.hom).trans (Category.comp_id _).symm⟩) hg
  let ψ : (𝟙_ (Over (Sp R)) ⟶ G.Y) →* (𝟙_ (Over (Sp K)) ⟶ A) :=
    { toFun := fun t => secHom (spMap (algebraMap R K)) G.Y t ≫ G.e.hom
      map_one' := by rw [map_one]; exact MonObj.one_comp _
      map_mul' := fun t t' => by rw [map_mul]; exact MonObj.mul_comp _ _ _ }
  have hψinj : Function.Injective ψ := fun t t' h =>
    GlobalTheory.IsogRed.sec_injective (spMap (algebraMap R K)) ((cancel_mono G.e.hom).1 h)
  have hψ : ∀ a : 𝟙_ (Over (Sp K)) ⟶ A, ∃ t, ψ t = a ^ c := fun a => by
    obtain ⟨s, hs'⟩ := hs a
    refine ⟨s, ?_⟩
    change GlobalTheory.IsogRed.sec _ s ≫ G.e.hom = _
    rw [GlobalTheory.IsogRed.sec_eq_comp _ G.e s (a ^ c) hs', Category.assoc, Iso.inv_hom_id, Category.comp_id]
  choose sA hsA using hψ
  have hred : ∀ t : 𝟙_ (Over (Sp R)) ⟶ G.Y, ∀ n : ℕ, IsUnit (n : R) → t ^ n = 1 →
      secHom (spMap (residue R)) G.Y t = 1 → t = 1 := by
    intro t n hn htn ht
    refine GlobalTheory.RedPts.eq_one_of_pow_of_closedPoint G.Y (𝟙 (Sp R)) hn t htn (Z := Over.mk (spMap (residue R)))
      (Over.homMk (spMap (residue R)) (Category.comp_id _))
      ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue R)⟩ ?_
    rw [← MonObj.comp_one (Over.homMk (spMap (residue R)) (Category.comp_id _) :
      Over.mk (spMap (residue R)) ⟶ Over.mk (𝟙 (Sp R)))]
    apply Over.OverMorphism.ext
    have e1 := GlobalTheory.IsogRed.sec_left (spMap (residue R)) t
    have e2 := GlobalTheory.IsogRed.sec_left (spMap (residue R)) (1 : 𝟙_ (Over (Sp R)) ⟶ G.Y)
    have e3 : GlobalTheory.IsogRed.sec (spMap (residue R)) t = GlobalTheory.IsogRed.sec (spMap (residue R)) 1 := by
      rw [← secHom_apply, ← secHom_apply, map_one]; exact ht
    change spMap (residue R) ≫ t.left = spMap (residue R) ≫ (1 : 𝟙_ (Over (Sp R)) ⟶ G.Y).left
    rw [← e1, ← e2, e3]
  have hunit : ∀ m : ℕ, (m : ResidueField R) ≠ 0 → IsUnit (m : R) := fun m hm => by
    by_contra h
    exact hm (by rw [← map_natCast (residue R)]; exact (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 h))
  have hsp : IsProper (GlobalTheory.SS.spFibre G.Y).hom := by
    refine GlobalTheory.T.isProper_of_infinitely_many_large_torsion (ResidueField R) (GlobalTheory.SS.spFibre G.Y) (GlobalTheory.IsogRed.smConn_baseChange _ _ hG) g
      (GlobalTheory.IsogRed.relDim_spFibre (K := K) G.Y hG g hGg) (c ^ (2 * g)) (hinf.mono ?_)
    rintro m ⟨hm, hcard⟩
    refine ⟨hm, ?_⟩
    have hm0 : m ≠ 0 := by rintro rfl; exact hm Nat.cast_zero
    have hmK : (m : K) ≠ 0 := by
      have := ((hunit m hm).map (algebraMap R K)).ne_zero
      rwa [map_natCast] at this
    have hfinT : {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ m = 1}.Finite := by
      have : Finite {x : 𝟙_ (Over (Sp K)) ⟶ A // x ^ m = 1} :=
        Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hm0)
      exact Set.finite_coe_iff.mp this
    have hTcard : hfinT.toFinset.card = m ^ (2 * g) := by
      rw [← hcard, ← Set.ncard_eq_toFinset_card _ hfinT, ← Nat.card_coe_set_eq]; rfl
    have hT : ∀ a ∈ hfinT.toFinset, a ^ m = 1 := fun a ha => by simpa using ha
    have hsAm : ∀ a : 𝟙_ (Over (Sp K)) ⟶ A, a ^ m = 1 → sA a ^ m = 1 := fun a ha =>
      hψinj (by rw [map_pow, hsA, map_one, ← pow_mul, mul_comm, pow_mul, ha, one_pow])
    classical
    refine ⟨hfinT.toFinset.image fun a => secHom (spMap (residue R)) G.Y (sA a), ?_, ?_⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      rw [← map_pow, hsAm a (hT a ha), map_one]
    · have hd : ((Nat.gcd m c : ℕ) : K) ≠ 0 := by
        obtain ⟨k, hk⟩ := Nat.gcd_dvd_left m c
        intro h0
        apply hmK
        rw [hk, Nat.cast_mul, h0, zero_mul]
      obtain ⟨hfin, hB⟩ := torsion_finite_ncard_le K A hA g hg _ hd
      rw [← hTcard]
      refine card_le_of_fibres _ m c (c ^ (2 * g)) hT _ ?_ hfin
        (hB.trans (Nat.pow_le_pow_left (Nat.le_of_dvd hc (Nat.gcd_dvd_right m c)) _))
      intro a ha b hb hab
      have ht : (sA a * (sA b)⁻¹) ^ m = 1 := by
        rw [mul_pow, inv_pow, hsAm a (hT a ha), hsAm b (hT b hb)]; simp
      have h1 := hred _ m (hunit m hm) ht (by rw [map_mul, map_inv, hab, mul_inv_cancel])
      rw [← hsA a, ← hsA b, mul_inv_eq_one.1 h1]
  have hprop : IsProper G.Y.hom := GlobalTheory.T.isProper_smoothConnGroupScheme_dvr_of_proper_fibres R K G.Y hG hgenP hsp
  exact ⟨G.Y, inst, GlobalTheory.T.isAbelianScheme_of_smConn_of_isProper' _ G.Y hG hprop, G.e, he⟩

end GlobalTheory.GoodRedTorsion
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGoodReduction_of_many_rational_torsion_points : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], GlobalTheory.SS.SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → {m : ℕ | (m : ResidueField R) ≠ 0 ∧ Nat.card {x : 𝟙_ (Over (Sp K)) ⟶ A // x ^ m = 1} = m ^ (2 * g)}.Infinite → HasGoodReduction R K A := by
  atlas_forward_decl GlobalTheory.GoodRedTorsion.hasGoodReduction_of_torsion
end
