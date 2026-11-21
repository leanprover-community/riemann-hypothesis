import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsActionOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfAppLESectionEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientDescendGrpObj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSumSmulSeparatingInertia
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothDescentOfTameQuotient
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGeometricallyIntegralAbLocusTensorObj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfQuotientOfRigid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStructureAndSymmetricOfCubeGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LinDescent

variable {X Y Z : Scheme.{0}}

theorem sum_coeff_eq_zero_of_linearIndependent {R M ι C : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [Fintype C] [DecidableEq ι] {v : ι → M} (hv : LinearIndependent R v) (p : C → ι)
    (a : C → R) (h : ∑ c, a c • v (p c) = 0) (i : ι) : ∑ c, (if p c = i then a c else 0) = 0 := by
  have h1 := linearIndependent_iff.1 hv (∑ c, Finsupp.single (p c) (a c)) (by
    simpa only [map_sum, Finsupp.linearCombination_single] using h)
  have h2 := DFunLike.congr_fun h1 i
  simpa only [Finsupp.finset_sum_apply, Finsupp.single_apply, Finsupp.zero_apply] using h2

variable {L : LB X} {C : Type} {t : C → (X ⟶ X)} {π : X ⟶ Y}

theorem exists_inv_sec_of_tame [Group C] [Finite C] (hL : L.IsLB)
    (ht : ∀ c c', t c ≫ t c' = t (c * c'))
    (htame : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X),
      (Nat.card {c // r ≫ t c = r} : k) ≠ 0)
    {u : ∀ c, LB.Gen (twist L (t c))} (hu : ∀ c, (u c).IsGen)
    (hc : ∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c'))
      (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') (t c))))
    (hfix : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X) c, r ≫ t c = r →
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (u c) r) (LB.oneGen L))
    {W : X.Opens} (hWa : IsAffineOpen W) (hW : ∀ c, W ≤ t c ⁻¹ᵁ W) (x : X) (hx : x ∈ W) :
    ∃ s : ∀ i, Γ(X, W ⊓ L.U i), IsLocSec L W s ∧ IsInv u W s ∧
      ∃ i, x ∈ X.basicOpen (s i) := by
  classical
  cases nonempty_fintype C
  obtain ⟨m, hm, hm'⟩ := exists_locSec hL hWa x hx
  obtain ⟨k, _, _, r, hr⟩ := FinEt.exists_algClosed_point X x
  let z : Sp k := IsLocalRing.closedPoint k
  obtain rfl : r z = x := hr.le ⟨z, rfl⟩
  let ek := (stalkClosedPointIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have hF : IsField ((Sp k).presheaf.stalk z) := ek.toMulEquiv.isField (Field.toIsField k)
  have hz : ∀ c, (r ≫ t c) z ∈ W := fun c => hW c hx
  let p : C → (Γ(X, W) →* (Sp k).presheaf.stalk z) :=
    fun c => (gsHom (r ≫ t c) z W (hz c)).toMonoidHom
  have hp : ∀ c, p c = (gsHom r z W hx).toMonoidHom ↔ r ≫ t c = r := fun c =>
    ⟨fun e => hom_ext_of_gs hWa
      (fun z' => Subsingleton.elim z z' ▸ hz c) (fun z' => Subsingleton.elim z z' ▸ hx)
      fun z' f => by
        obtain rfl : z = z' := Subsingleton.elim _ _
        rw [gs_eq_gsHom _ _ _ (hz c), gs_eq_gsHom _ _ _ hx]
        exact DFunLike.congr_fun e f,
    fun e => MonoidHom.ext fun f => by
      change gsHom (r ≫ t c) z W (hz c) f = gsHom r z W hx f
      rw [← gs_eq_gsHom, ← gs_eq_gsHom, e]⟩
  choose J hJ using fun χ : Sp k ⟶ X => exists_chart hL (χ z)
  have hJ' : Good L z J := hJ
  have h1 : ∀ c, r ≫ t c = r → uv (u c) r z (J r) (J (r ≫ t c)) = 1 := fun c e => by
    have := val_corr hJ' (hfix k r c e) (𝟙 _)
    rwa [val_pull hJ', val_one, Category.id_comp, val_eq_uv] at this
  have : ∃ f : Γ(X, W), ∑ c, (uv (u c) r z (J r) (J (r ≫ t c))).val *
      gs (r ≫ t c) z _ (m (J (r ≫ t c))) * gs (r ≫ t c) z W f ≠ 0 := by
    by_contra! H
    have h2 := sum_coeff_eq_zero_of_linearIndependent
      (linearIndependent_monoidHom Γ(X, W) ((Sp k).presheaf.stalk z)) p
      (fun c => (uv (u c) r z (J r) (J (r ≫ t c))).val * gs (r ≫ t c) z _ (m (J (r ≫ t c))))
      (funext fun f => by
        rw [Finset.sum_apply]
        refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) (H f)
        rw [gs_eq_gsHom _ _ _ (hz c) f]
        rfl) (gsHom r z W hx).toMonoidHom
    have h3 : ∀ c, (if p c = (gsHom r z W hx).toMonoidHom then
        (uv (u c) r z (J r) (J (r ≫ t c))).val * gs (r ≫ t c) z _ (m (J (r ≫ t c))) else 0) =
        if r ≫ t c = r then gs r z _ (m (J r)) else 0 := fun c =>
      if_ctx_congr (hp c) (fun e => by rw [h1 c e, Units.val_one, one_mul, e]) fun _ => rfl
    rw [Finset.sum_congr rfl fun c _ => h3 c, ← Finset.sum_filter, Finset.sum_const,
      ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, nsmul_eq_mul] at h2
    have h4 : IsUnit (gs r z _ (m (J r))) :=
      (isUnit_gs_iff r z (W ⊓ L.U (J r)) ⟨hx, hJ r⟩ _).2 (hm' _ (hJ r))
    have h5 := congrArg ek (h4.mul_left_eq_zero.1 h2)
    rw [map_natCast, map_zero] at h5
    exact htame k r h5
  obtain ⟨f, hf⟩ := this
  obtain ⟨s, h1, h2, h3⟩ := exists_average hL ht hu hc hW hm f
  refine ⟨s, h1, h2, J r, (isUnit_gs_iff r z (W ⊓ L.U (J r)) ⟨hx, hJ r⟩ _).1 ?_⟩
  rw [h3 _ r z (J r) (fun c => J (r ≫ t c)) hx (hJ r) fun c => hJ _]
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel hf
  exact IsUnit.of_mul_eq_one _ hb

def FunctionsAreInvariants (t : C → (X ⟶ X)) (π : X ⟶ Y) : Prop :=
  ∀ V : Y.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V),
    (∀ c (h : π ⁻¹ᵁ V ≤ t c ⁻¹ᵁ (π ⁻¹ᵁ V)), ((t c).appLE _ _ h).hom f = f) →
      f ∈ Set.range (π.app V).hom

theorem FunctionsAreInvariants.exists_descend (h : FunctionsAreInvariants t π) (V : Y.Opens)
    (f : Γ(X, π ⁻¹ᵁ V))
    (hf : ∀ c (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z), r z ∈ π ⁻¹ᵁ V →
      gs (r ≫ t c) z _ f = gs r z _ f) :
    ∃ a : Γ(Y, V), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z), r z ∈ π ⁻¹ᵁ V →
      gs (r ≫ π) z V a = gs r z _ f := by
  obtain ⟨a, rfl⟩ := (h V).2 f fun c e => fn_ext fun x hx =>
    (gs_appLE (𝟙 X) (t c) x _ _ e hx f).trans (hf c X (𝟙 X) x hx)
  exact ⟨a, fun Z r z hz => (gs_pull r π z V hz a).symm⟩

theorem FunctionsAreInvariants.unit_ext (h : FunctionsAreInvariants t π) {V : Y.Opens}
    {a b : Γ(Y, V)ˣ} (e : ∀ x, π x ∈ V → gm (𝟙 X ≫ π) x V a = gm (𝟙 X ≫ π) x V b) : a = b := by
  refine Units.ext ((h V).1 (fn_ext fun x hx => ?_))
  rw [gs_pull (𝟙 X) π x V hx, gs_pull (𝟙 X) π x V hx, gs_unit (𝟙 X ≫ π) x V hx,
    gs_unit (𝟙 X ≫ π) x V hx, e x hx]

theorem exists_descent_of_invGen_of_invariants [Surjective π] (hL : L.IsLB)
    (hπ : ∀ c, t c ≫ π = π) (h : FunctionsAreInvariants t π) {u : ∀ c, LB.Gen (twist L (t c))}
    (V : Y → Y.Opens) (hV : ∀ y, y ∈ V y) (e : ∀ y i, Γ(X, π ⁻¹ᵁ V y ⊓ L.U i)ˣ)
    (he : ∀ y, IsInvGen u (π ⁻¹ᵁ V y) (e y)) :
    ∃ M : LB Y, M.IsLB ∧ LBIso L (M.pull π) := by
  have hmem : ∀ (U : Y.Opens) c {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z), r z ∈ π ⁻¹ᵁ U →
      (r ≫ t c) z ∈ π ⁻¹ᵁ U := fun U c Z r z hz => by
    change ((r ≫ t c) ≫ π) z ∈ U
    rw [Category.assoc, hπ]
    exact hz
  have H : ∀ y y', ∃ g : Γ(Y, V y ⊓ V y')ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i,
      r z ∈ π ⁻¹ᵁ V y → r z ∈ π ⁻¹ᵁ V y' → r z ∈ L.U i →
      gm (r ≫ π) z _ g = gm r z _ (e y' i) * (gm r z _ (e y i))⁻¹ := fun y y' => by
    let O : L.ι → X.Opens := fun i => π ⁻¹ᵁ (V y ⊓ V y') ⊓ L.U i
    have l : ∀ i, O i ≤ π ⁻¹ᵁ V y ⊓ L.U i := fun i x hx => ⟨hx.1.1, hx.2⟩
    have l' : ∀ i, O i ≤ π ⁻¹ᵁ V y' ⊓ L.U i := fun i x hx => ⟨hx.1.2, hx.2⟩
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ O i →
        gs r z (O i) (res (l' i) (e y' i) * (res (l i) (e y i))⁻¹).val =
        (gm r z _ (e y' i) * (gm r z _ (e y i))⁻¹).val := fun Z r z i hz => by
      rw [gs_unit r z _ hz, map_mul, map_inv, gm_res r z _ hz, gm_res r z _ hz]
    obtain ⟨ρ, hρ⟩ := glue_fn (π ⁻¹ᵁ (V y ⊓ V y')) O (fun _ => inf_le_left)
      (fun x hx => (exists_chart hL x).imp fun i hi => ⟨hx, hi⟩)
      (fun i => (res (l' i) (e y' i) * (res (l i) (e y i))⁻¹).val) (fun i j x hi hj => by
        rw [v _ (𝟙 X) x i hi, v _ (𝟙 X) x j hj, (he y).1 _ (𝟙 X) x i j hi.1.1 hi.2 hj.2,
          (he y').1 _ (𝟙 X) x i j hi.1.2 hi.2 hj.2, ← div_eq_mul_inv, mul_div_mul_left_eq_div,
          div_eq_mul_inv])
    have hρ' : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ π ⁻¹ᵁ (V y ⊓ V y') →
        r z ∈ L.U i → gs r z _ ρ = (gm r z _ (e y' i) * (gm r z _ (e y i))⁻¹).val :=
      fun Z r z i h1 h2 => (hρ Z r z i ⟨h1, h2⟩).trans (v Z r z i ⟨h1, h2⟩)
    obtain ⟨a, ha⟩ := h.exists_descend (V y ⊓ V y') ρ fun c Z r z hz => by
      obtain ⟨i, hi⟩ := exists_chart hL (r z)
      obtain ⟨k, hk⟩ := exists_chart hL ((r ≫ t c) z)
      rw [hρ' Z r z i hz hi, hρ' Z (r ≫ t c) z k (hmem _ c r z hz) hk,
        (he y).2 c Z r z i k hz.1 hi hk, (he y').2 c Z r z i k hz.2 hi hk,
        ← div_eq_mul_inv (_ * _), mul_div_mul_left_eq_div, div_eq_mul_inv]
    have hu : IsUnit a := isUnit_of_mem_basicOpen a fun b hb => by
      obtain ⟨x, rfl⟩ := π.surjective b
      obtain ⟨i, hi⟩ := exists_chart hL x
      refine (isUnit_gs_iff (𝟙 X ≫ π) x (V y ⊓ V y') hb a).1 ?_
      rw [ha _ (𝟙 X) x hb, hρ' _ (𝟙 X) x i hb hi]
      exact Units.isUnit _
    refine ⟨hu.unit, fun Z r z i h1 h2 hi => Units.ext ?_⟩
    exact (gs_unit (r ≫ π) z (V y ⊓ V y') ⟨h1, h2⟩ hu.unit).symm.trans
      ((ha Z r z ⟨h1, h2⟩).trans (hρ' Z r z i ⟨h1, h2⟩ hi))
  choose g hg using H
  let M : LB Y := ⟨Y, V, g⟩
  refine ⟨M, ⟨eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hV y⟩, fun y => ?_,
    fun y₁ y₂ y₃ => ?_⟩, ?_⟩
  · refine h.unit_ext fun x hx => ?_
    obtain ⟨i, hi⟩ := exists_chart hL x
    refine (gm_res (𝟙 X ≫ π) x _ hx _).trans ((hg y y _ (𝟙 X) x i hx hx hi).trans ?_)
    rw [mul_inv_cancel, map_one]
  · refine h.unit_ext fun x hx => ?_
    obtain ⟨i, hi⟩ := exists_chart hL x
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res (𝟙 X ≫ π) x _ hx _).trans (hg y₁ y₂ _ (𝟙 X) x i hx.1.1 hx.1.2 hi))
      ((gm_res (𝟙 X ≫ π) x _ hx _).trans (hg y₂ y₃ _ (𝟙 X) x i hx.1.2 hx.2 hi)))).trans
      (Eq.trans ?_ ((gm_res (𝟙 X ≫ π) x _ hx _).trans
        (hg y₁ y₃ _ (𝟙 X) x i hx.1.1 hx.2 hi)).symm)
    rw [mul_comm, mul_assoc, inv_mul_cancel_left]
  · have l : ∀ p : (PUnit → Y) × L.ι, (M.pull π).U p.1 ⊓ L.U p.2 ≤
        π ⁻¹ᵁ V (p.1 PUnit.unit) ⊓ L.U p.2 := fun p x hx => ⟨mem_pull.1 hx.1, hx.2⟩
    let w : LB.Iso L (M.pull π) := ⟨fun p => (res (l p) (e (p.1 PUnit.unit) p.2))⁻¹⟩
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (y : Y) i, π (r z) ∈ V y → r z ∈ L.U i →
        gw w r z y i = (gm r z _ (e y i))⁻¹ := fun Z r z y i h1 h2 =>
      (map_inv _ _).trans (congrArg _ (gm_res r z (l (fun _ => y, i))
        ⟨(mem_pull (L := M)).2 h1, h2⟩ _))
    refine ⟨w, (isGen_iff w).2 fun Z r z y y' i i' h1 h2 h3 h4 => ?_⟩
    rw [v Z r z y i h1 h3, v Z r z y' i' h2 h4]
    refine Eq.trans ?_ (congrArg (· * _ * _) (hg y y' Z r z i' h1 h2 h4)).symm
    rw [(he y).1 Z r z i i' h1 h3 h4]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem exists_descent_of_tame_family [Group C] [Finite C] [IsIntegralHom π] [Surjective π]
    (hL : L.IsLB) (ht : ∀ c c', t c ≫ t c' = t (c * c'))
    (hπ : ∀ c, t c ≫ π = π) (h : FunctionsAreInvariants t π)
    (horb : ∀ x x' : X, π x = π x' → ∃ c, x = t c x')
    (htame : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X),
      (Nat.card {c // r ≫ t c = r} : k) ≠ 0)
    {u : ∀ c, LB.Gen (twist L (t c))} (hu : ∀ c, (u c).IsGen)
    (hc : ∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c'))
      (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') (t c))))
    (hfix : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X) c, r ≫ t c = r →
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (u c) r) (LB.oneGen L)) :
    ∃ M : LB Y, M.IsLB ∧ LBIso L (M.pull π) := by
  have H : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ e, IsInvGen u (π ⁻¹ᵁ V) e := fun y => by
    obtain ⟨x, rfl⟩ := π.surjective y
    obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hx, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (π x)) isOpen_univ
    have hinv : ∀ (V : Y.Opens) c, π ⁻¹ᵁ V ≤ t c ⁻¹ᵁ π ⁻¹ᵁ V := fun V c => by
      rw [← Scheme.Hom.comp_preimage, hπ]
    obtain ⟨s, h1, h2, i₀, h3⟩ := exists_inv_sec_of_tame hL ht htame hu hc hfix
      (IsAffineOpen.preimage hV₀ π) (hinv V₀) x hx
    let N : X.Opens := ⨆ i, X.basicOpen (s i)
    let V : Y.Opens := ⟨(π '' (N : Set X)ᶜ)ᶜ, (π.isClosedMap _ N.isOpen.isClosed_compl).isOpen_compl⟩
    have hN : ∀ x', x' ∈ π ⁻¹ᵁ V → ∃ i, x' ∈ X.basicOpen (s i) := fun x' hx' => by
      by_contra hh
      exact hx' ⟨x', fun hh' => hh (Opens.mem_iSup.1 hh'), rfl⟩
    have hN' : ∀ x', x' ∈ π ⁻¹ᵁ V → x' ∈ π ⁻¹ᵁ V₀ := fun x' hx' => by
      obtain ⟨i, hi⟩ := hN x' hx'
      exact (X.basicOpen_le _ hi).1
    have l : ∀ i, π ⁻¹ᵁ V ⊓ L.U i ≤ π ⁻¹ᵁ V₀ ⊓ L.U i := fun i x' hx' => ⟨hN' x' hx'.1, hx'.2⟩
    have hu' : ∀ i, IsUnit (rs (l i) (s i)) := fun i => isUnit_of_mem_basicOpen _ fun x' hx' => by
      obtain ⟨j, hj⟩ := hN x' hx'.1
      have hj' := X.basicOpen_le _ hj
      refine (isUnit_gs_iff (𝟙 X) x' _ hx' _).1 ?_
      rw [gs_res (𝟙 X) x' _ hx', h1 _ (𝟙 X) x' i j hj'.1 hx'.2 hj'.2]
      exact (Units.isUnit _).mul ((isUnit_gs_iff (𝟙 X) x' _ hj' _).2 hj)
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ π ⁻¹ᵁ V → r z ∈ L.U i →
        (gm r z _ (hu' i).unit).val = gs r z _ (s i) := fun Z r z i a b =>
      (gs_unit r z (π ⁻¹ᵁ V ⊓ L.U i) ⟨a, b⟩ _).symm.trans (gs_res r z (l i) ⟨a, b⟩ _)
    refine ⟨V, ?_, fun i => (hu' i).unit, fun Z r z i j a b c => Units.ext ?_,
      fun c Z r z i k a b d => Units.ext ?_⟩
    · rintro ⟨x', hx', e⟩
      obtain ⟨c, rfl⟩ := horb _ _ e
      obtain ⟨k, hk⟩ := exists_chart hL (t c x)
      have h4 := X.basicOpen_le _ h3
      have h5 := (isUnit_gs_iff (𝟙 X) x _ h4 _).2 h3
      rw [h2 c _ (𝟙 X) x i₀ k hx h4.2 hk] at h5
      exact hx' (Opens.mem_iSup.2 ⟨k, (isUnit_gs_iff (𝟙 X ≫ t c) x (π ⁻¹ᵁ V₀ ⊓ L.U k)
        ⟨hinv V₀ c hx, hk⟩ _).1 (isUnit_of_mul_isUnit_right h5)⟩)
    · rw [Units.val_mul, v Z r z i a b, v Z r z j a c]
      exact h1 Z r z i j (hN' _ a) b c
    · rw [Units.val_mul, v Z r z i a b, v Z (r ≫ t c) z k (hinv V c a) d]
      exact h2 c Z r z i k (hN' _ a) b d
  choose V hV e he using H
  exact exists_descent_of_invGen_of_invariants hL hπ h V hV e he

end GlobalTheory.LinDescent

namespace GlobalTheory.LinDescent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

theorem exists_descent_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (Y Y' : Scheme.{0}) (τ : Γ →* Aut Y) (φ : Y ⟶ Y') (L : LB Y), (IsAffineHom φ ∧ (∀ g, (τ g).hom ≫ φ = φ) ∧ ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V), (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y), (Nat.card {g // x ≫ (τ g).hom = x} : k) ≠ 0) → L.IsLB → ∀ u : ∀ g, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 Y, (τ g).hom] ![1, -1]), (∀ g, (u g).IsGen) → (∀ g h, LB.Gen.Corr L _ _ _ _ (u (h * g)) (LB.mulGen L _ _ _ _ (u g) (LB.pullGen L _ _ (u h) (τ g).hom))) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y) g, y ≫ (τ g).hom = y → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (u g) y) (LB.oneGen L)) → ∃ L' : LB Y', L'.IsLB ∧ LBIso L (L'.pull φ) := by
  intro Γ _ _ Y Y' τ φ L hφ htame hL u hu hc hfix
  obtain ⟨_, _, horb, -, -⟩ := quotient_isIntegral_surjective_orbits Γ Y Y' τ φ hφ
  have : Finite Γᵐᵒᵖ := Finite.of_equiv Γ MulOpposite.opEquiv
  refine exists_descent_of_tame_family (C := Γᵐᵒᵖ) (t := fun c => (τ c.unop).hom) hL
    (fun c c' => ?_) (fun c => hφ.2.1 _)
    (fun V => ⟨(hφ.2.2 V).1, fun f hf => (hφ.2.2 V).2 f fun g => hf (MulOpposite.op g)⟩)
    (fun x x' e => ?_) (fun k _ _ r => ?_) (u := fun c => u c.unop) (fun c => hu _)
    (fun c c' => hc c.unop c'.unop) (fun k _ _ r c => hfix k r c.unop)
  · beta_reduce
    rw [MulOpposite.unop_mul, map_mul]
    rfl
  · obtain ⟨g, hg⟩ := horb x' x e.symm
    exact ⟨MulOpposite.op g, hg⟩
  · rw [← Nat.card_congr (MulOpposite.opEquiv.subtypeEquiv
      (p := fun g : Γ => r ≫ (τ g).hom = r) fun g => Iff.rfl)]
    exact htame k r

end GlobalTheory.LinDescent
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.DescTheta

open GlobalTheory.LB

theorem exists_trace_ne_zero {Γ B A K : Type} [Group Γ] [Fintype Γ] [CommRing B] [CommRing A]
    [Field K] [MulSemiringAction Γ B] [MulSemiringAction Γ A] (f : B →+* A)
    (hf : ∀ (g : Γ) b, f (g • b) = g • f b) (ev : A →+* K)
    (hc : (Nat.card ((RingHom.ker (ev.comp f)).inertia Γ) : K) ≠ 0) (x : A)
    (hI : ∀ g ∈ (RingHom.ker (ev.comp f)).inertia Γ, ev (g • x) = ev x) (hx : ev x ≠ 0) :
    ∃ c : B, ev (∑ g : Γ, g • (f c * x)) ≠ 0 := by
  classical
  obtain ⟨n, c, d, s, hs, h⟩ := exists_sum_smul_separating_inertia Γ B _
    (RingHom.ker_isPrime (ev.comp f))
  by_contra! H
  have h1 : ∑ j, ev (f (d j)) * ev (∑ g : Γ, g • (f (c j) * x)) = 0 := by
    simp only [H, mul_zero, Finset.sum_const_zero]
  have h2 : ∑ j, ev (f (d j)) * ev (∑ g : Γ, g • (f (c j) * x)) =
      ∑ g : Γ, ev (f (∑ j, d j * g • c j)) * ev (g • x) := by
    simp only [map_sum, Finset.mul_sum, Finset.sum_mul, smul_mul', map_mul, hf, _root_.mul_assoc]
    rw [Finset.sum_comm]
  have h3 : ∀ g : Γ, ev (f (∑ j, d j * g • c j)) * ev (g • x) =
      if g ∈ (RingHom.ker (ev.comp f)).inertia Γ then ev (f s) * ev x else 0 := by
    intro g
    split_ifs with hg
    · have := (h g).1 hg
      rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
      rw [hI g hg]
      exact congrArg (· * ev x) this
    · have : ev (f (∑ j, d j * g • c j)) = 0 := (h g).2 hg
      rw [this, zero_mul]
  rw [h2] at h1
  simp only [h3] at h1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card] at h1
  exact mul_ne_zero hc (mul_ne_zero hs hx) h1

variable {X Y : Scheme.{0}}

theorem mem_basicOpen_resG {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (x : X) :
    x ∈ X.basicOpen (resG X h a) ↔ x ∈ V ∧ x ∈ X.basicOpen a := by
  have : X.basicOpen (resG X h a) = V ⊓ X.basicOpen a := X.basicOpen_res a (homOfLE h).op
  rw [this]; rfl

theorem mem_basicOpen_appLE (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (a : Γ(X, U)) (y : Y) :
    y ∈ Y.basicOpen ((f.appLE U V h).hom a) ↔ y ∈ V ∧ f y ∈ X.basicOpen a := by
  have : Y.basicOpen ((f.appLE U V h).hom a) = V ⊓ f ⁻¹ᵁ X.basicOpen a :=
    Scheme.basicOpen_appLE f V U h a
  rw [this]; rfl

theorem mem_basicOpen_mul {U : X.Opens} (a b : Γ(X, U)) (x : X) :
    x ∈ X.basicOpen (a * b) ↔ x ∈ X.basicOpen a ∧ x ∈ X.basicOpen b := by
  rw [Scheme.basicOpen_mul]; rfl

theorem nonvanishing_iso {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen)
    {V : X.Opens} (s : Γ(toMod L, V)) (x : X) :
    (∃ p, x ∈ X.basicOpen (coord ((isoOfGen hL hM w hw).hom.app V s) p)) ↔
      ∃ q, x ∈ X.basicOpen (coord s q) := by
  have key (p : M.ι) (q : L.ι) (hp : x ∈ V ⊓ M.U p) (hq : x ∈ V ⊓ L.U q) :
      x ∈ X.basicOpen (coord ((isoOfGen hL hM w hw).hom.app V s) p) ↔
        x ∈ X.basicOpen (coord s q) := by
    have e := coord_isoOfGen_hom_app hL hM w hw s p q (W := (V ⊓ M.U p) ⊓ (V ⊓ L.U q))
      inf_le_left inf_le_right (inf_le_inf inf_le_right inf_le_right)
    have e' := congrArg (fun a => x ∈ X.basicOpen a) e
    simp only [mem_basicOpen_mul, mem_basicOpen_resG, eq_iff_iff] at e'
    have hx : x ∈ (V ⊓ M.U p) ⊓ (V ⊓ L.U q) := ⟨hp, hq⟩
    have hx' : x ∈ X.basicOpen (U := M.U p ⊓ L.U q)
        ((show Γ(X, M.U p ⊓ L.U q)ˣ from w.s (p, q)) : Γ(X, M.U p ⊓ L.U q)) :=
      (X.basicOpen_of_isUnit (U := M.U p ⊓ L.U q) (Units.isUnit _)).ge ⟨hp.2, hq.2⟩
    exact ⟨fun h => (e'.1 ⟨hx, h⟩).2.2, fun h => (e'.2 ⟨⟨hx, hx'⟩, hx, h⟩).2⟩
  constructor
  · rintro ⟨p, hp⟩
    have hp' := X.basicOpen_le _ hp
    obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ x))
    exact ⟨q, (key p q hp' ⟨hp'.1, hq⟩).1 hp⟩
  · rintro ⟨q, hq⟩
    have hq' := X.basicOpen_le _ hq
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x))
    exact ⟨p, (key p q ⟨hq'.1, hp⟩ hq').2 hq⟩

theorem exists_nhds_nonvanishing {G : Over X} {L : LB G.left} (h : PushInvertible G L)
    {W : X.Opens} {O : G.left.Opens} (hO : G.hom ⁻¹ᵁ W ≤ O) (s : Γ(toMod L, O)) (u : G.left)
    (hu : G.hom u ∈ W) (hs : ∃ i, u ∈ G.left.basicOpen (coord s i)) :
    ∃ U : X.Opens, U ≤ W ∧ G.hom u ∈ U ∧ ∀ z ∈ U, ∃ u' : G.left, G.hom u' = z ∧
      ∃ i, u' ∈ G.left.basicOpen (coord s i) := by
  obtain ⟨V, hV, θ, -, h1, h2⟩ := h (G.hom u)
  have hle : G.hom ⁻¹ᵁ (W ⊓ V) ≤ O := (G.hom.preimage_mono inf_le_left).trans hO
  obtain ⟨a, ha, -⟩ := h1 (W ⊓ V) inf_le_right _
    (coord_mem ((toMod L).presheaf.map (homOfLE hle).op s))
  have key (i : L.ι) (u' : G.left) (h' : G.hom u' ∈ W ⊓ V) :
      u' ∈ G.left.basicOpen (coord s i) ↔
        G.hom u' ∈ X.basicOpen a ∧ u' ∈ G.left.basicOpen (θ i) := by
    have e' := congrArg (fun a => u' ∈ G.left.basicOpen a) (ha i)
    simp only [coord_map, mem_basicOpen_mul, mem_basicOpen_resG, mem_basicOpen_appLE,
      eq_iff_iff] at e'
    by_cases hi : u' ∈ L.U i
    · have hx : u' ∈ G.hom ⁻¹ᵁ (W ⊓ V) ⊓ L.U i := ⟨h', hi⟩
      simpa only [hx, true_and] using e'
    · exact ⟨fun h => (hi (G.left.basicOpen_le _ h).2).elim,
        fun h => (hi (G.left.basicOpen_le _ h.2).2).elim⟩
  obtain ⟨i, hi⟩ := hs
  refine ⟨X.basicOpen a, (X.basicOpen_le a).trans inf_le_left, ((key i u ⟨hu, hV⟩).1 hi).1,
    fun z hz => ?_⟩
  obtain ⟨u', j, rfl, hj⟩ := h2 z (X.basicOpen_le a hz).2
  exact ⟨u', rfl, j, (key j u' (X.basicOpen_le a hz)).2 ⟨hz, hj⟩⟩

theorem isQuasicoherent_pushforward {G : Over X} {L : LB G.left} (h : PushInvertible G L) :
    ((Scheme.Modules.pushforward G.hom).obj (toMod L)).IsQuasicoherent := by
  choose V hV θ hθ h1 h2 using h
  refine QCoh.isQuasicoherent_of_restrict _ (fun x => (V x).ι) (fun x => ⟨x, ?_⟩) fun x => ?_
  · rw [Scheme.Opens.opensRange_ι]; exact hV x
  · have e := Descent.freeIso (F := (Scheme.Modules.pushforward G.hom).obj (toMod L))
      (s := mkSec (θ x) (hθ x)) (Descent.bijective_smul_stalk fun W hW => by
        refine (Function.bijective_iff_existsUnique _).2 fun (s : Γ(toMod L, G.hom ⁻¹ᵁ W)) => ?_
        refine (existsUnique_congr fun a => ?_).1 (h1 x W hW _ (coord_mem s))
        refine ⟨fun h => sec_ext (L := L) fun i => (h i).symm, fun h i => ?_⟩
        exact (congrArg (fun t => coord (L := L) t i) h).symm)
    exact (SheafOfModules.isQuasicoherent (V x).toScheme.ringCatSheaf).prop_of_iso ((trivIso _).symm ≪≫ e)
      (isQuasicoherent_toMod (Out.Inh.trivLB_isLB _))

theorem exists_sec_nonvanishing {G : Over X} {L : LB G.left} (h : PushInvertible G L)
    {W : X.Opens} (hW : IsAffineOpen W) {x : X} (hx : x ∈ W) :
    ∃ (s : Γ(toMod L, G.hom ⁻¹ᵁ W)) (u : G.left), G.hom u = x ∧
      ∃ i, u ∈ G.left.basicOpen (coord s i) := by
  have := isQuasicoherent_pushforward h
  obtain ⟨V, hV, θ, hθ, -, h2⟩ := h x
  obtain ⟨b, hb, hxb⟩ := hW.exists_basicOpen_le ⟨x, hV⟩ hx
  obtain ⟨n, t, ht⟩ := QCoh.exists_pow_smul_eq_res ((Scheme.Modules.pushforward G.hom).obj (toMod L))
    hW b (X.basicOpen_le b) rfl
    ((toMod L).presheaf.map (homOfLE (G.hom.preimage_mono hb)).op (mkSec θ hθ))
  obtain ⟨u, i, rfl, hi⟩ := h2 x hV
  refine ⟨t, u, rfl, i, ?_⟩
  have e : (G.hom.appLE (X.basicOpen b) (G.hom ⁻¹ᵁ (X.basicOpen b) ⊓ L.U i) inf_le_left).hom
      (resG X (X.basicOpen_le b) b ^ n) *
        resG G.left (inf_le_inf_right _ (G.hom.preimage_mono hb)) (θ i) =
      resG G.left (inf_le_inf_right _ (G.hom.preimage_mono (X.basicOpen_le b)))
        (coord (L := L) t i) := congrArg (fun t => coord (L := L) t i) ht
  have e' := congrArg (fun a => u ∈ G.left.basicOpen a) e
  simp only [mem_basicOpen_mul, mem_basicOpen_resG, mem_basicOpen_appLE, eq_iff_iff] at e'
  have hu : u ∈ G.hom ⁻¹ᵁ (X.basicOpen b) ⊓ L.U i := ⟨hxb, (G.left.basicOpen_le _ hi).2⟩
  refine (e'.1 ⟨⟨hu, ?_⟩, hu, hi⟩).2
  have hb' : IsUnit (resG X (X.basicOpen_le b) b) := X.toRingedSpace.isUnit_res_basicOpen b
  rw [X.basicOpen_of_isUnit (hb'.pow n)]
  exact hxb

theorem le_pull_chart {L : LB X} (φ : Y ⟶ X) (O : X.Opens) (i : L.ι) :
    φ ⁻¹ᵁ (O ⊓ L.U i) ≤ φ ⁻¹ᵁ O ⊓ (L.pull φ).U (fun _ => i) :=
  le_inf (φ.preimage_mono inf_le_left)
    ((φ.preimage_mono inf_le_right).trans (pull_U φ (fun _ => i)).ge)

theorem exists_descent {Γ : Type} [Group Γ] [Fintype Γ] {Y' : Scheme.{0}} (τ : Γ →* Aut Y)
    (φ : Y ⟶ Y') (hφ : ∀ g, (τ g).hom ≫ φ = φ)
    (hq : ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V),
      (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (φ.app V).hom)
    {L : LB Y'} (O : Y'.Opens) (s : Γ(toMod (L.pull φ), φ ⁻¹ᵁ O)) :
    ∃ t : Γ(toMod L, O), ∀ i, (φ.app (O ⊓ L.U i)).hom (coord t i) =
      ∑ g : Γ, ((τ g⁻¹).hom.appLE _ _ (preimage_le_of_invariant τ φ hφ _ _)).hom
        (resG Y (le_pull_chart φ O i :
          φ ⁻¹ᵁ (O ⊓ L.U i) ≤ φ ⁻¹ᵁ O ⊓ (L.pull φ).U (fun _ => i)) (coord s (fun _ => i))) := by
  have H (i : L.ι) (u : Γ(Y, φ ⁻¹ᵁ (O ⊓ L.U i))) :
      (∑ g : Γ, ((τ g⁻¹).hom.appLE _ _ (preimage_le_of_invariant τ φ hφ _ _)).hom u) ∈
        Set.range (φ.app (O ⊓ L.U i)).hom := by
    refine (hq _).2 _ fun k _ => ?_
    let := sectionsAction τ _ (preimage_le_of_invariant τ φ hφ (O ⊓ L.U i))
    have e : k⁻¹ • ∑ g : Γ, g • u = ∑ g : Γ, g • u := by
      rw [Finset.smul_sum]
      simp only [← mul_smul]
      exact Equiv.sum_comp (Equiv.mulLeft k⁻¹) (fun g => g • u)
    have e' : ((τ k⁻¹⁻¹).hom.appLE _ _ (preimage_le_of_invariant τ φ hφ _ _)).hom
      (∑ g : Γ, g • u) = ∑ g : Γ, g • u := e
    simp only [inv_inv] at e'
    exact e'
  choose t ht using fun i => H i (resG Y (le_pull_chart φ O i :
          φ ⁻¹ᵁ (O ⊓ L.U i) ≤ φ ⁻¹ᵁ O ⊓ (L.pull φ).U (fun _ => i)) (coord s (fun _ => i)))
  refine ⟨mkSec t fun i j => ((hq _).1 ?_), ht⟩
  have l (i : L.ι) : φ ⁻¹ᵁ (O ⊓ L.U i) ≤ φ ⁻¹ᵁ O ⊓ (L.pull φ).U (fun _ => i) :=
    le_pull_chart φ O i
  have li : O ⊓ L.U i ⊓ L.U j ≤ O ⊓ L.U i := inf_le_left
  have lj : O ⊓ L.U i ⊓ L.U j ≤ O ⊓ L.U j := inf_le_inf_right _ inf_le_left
  have key (k : L.ι) (lk : O ⊓ L.U i ⊓ L.U j ≤ O ⊓ L.U k) :
      (φ.app _).hom (resG Y' lk (t k)) = ∑ g : Γ,
        ((τ g⁻¹).hom.appLE _ _ (preimage_le_of_invariant τ φ hφ (O ⊓ L.U i ⊓ L.U j) _)).hom
          (resG Y ((φ.preimage_mono lk).trans (l k)) (coord s (fun _ => k))) := by
    rw [Scheme.Hom.app_eq_appLE, appLE_resG, ← resG_app, ht k, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [resG_appLE, appLE_resG, appLE_resG]
  rw [map_mul, key i li, key j lj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [coord_rel s (fun _ => i) (fun _ => j) _ ((φ.preimage_mono lj).trans (l j))
    (le_inf (((φ.preimage_mono li).trans (l i)).trans inf_le_right)
      (((φ.preimage_mono lj).trans (l j)).trans inf_le_right)), map_mul,
    resG_pull_g φ (L := L) (fun _ => i) (fun _ => j)]
  congr 1
  rw [Scheme.Hom.app_eq_appLE, appLE_resG, ← RingHom.comp_apply, ← CommRingCat.hom_comp]
  simp only [Scheme.Hom.appLE_comp_appLE, hφ]

noncomputable def evalAt {k : Type} [Field k] (ζ : Sp k ⟶ X) (U : X.Opens) (h : ⊤ ≤ ζ ⁻¹ᵁ U) :
    Γ(X, U) →+* k :=
  (ζ.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (.of k)).hom).hom

theorem evalAt_ne_zero {k : Type} [Field k] (ζ : Sp k ⟶ X) (U : X.Opens) (h : ⊤ ≤ ζ ⁻¹ᵁ U)
    (a : Γ(X, U)) (z : Sp k) : evalAt ζ U h a ≠ 0 ↔ ζ z ∈ X.basicOpen a := by
  have e := mem_basicOpen_appLE ζ h a z
  rw [basicOpen_eq_of_affine'] at e
  have hz : z.asIdeal = ⊥ := @Ideal.eq_bot_of_prime k _ z.asIdeal z.isPrime
  have e2 : z ∈ PrimeSpectrum.basicOpen (evalAt ζ U h a) ↔ evalAt ζ U h a ≠ 0 := by
    change evalAt ζ U h a ∉ z.asIdeal ↔ _
    rw [hz, Ideal.mem_bot]
  rw [← e2]
  exact e.trans (and_iff_right trivial)

theorem evalAt_appLE {k : Type} [Field k] (ζ : Sp k ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (h : ⊤ ≤ ζ ⁻¹ᵁ V) (e : V ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) (ξ : Sp k ⟶ X) (hξ : ζ ≫ f = ξ)
    (h' : ⊤ ≤ ξ ⁻¹ᵁ U) :
    evalAt ζ V h ((f.appLE U V e).hom a) = evalAt ξ U h' a := by
  subst hξ
  simp only [evalAt, ← Scheme.Hom.appLE_comp_appLE ζ f U V ⊤ e h, CommRingCat.hom_comp,
    RingHom.comp_apply]

theorem mem_inertia_iff {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* Aut X) {W : X.Opens}
    (hW : IsAffineOpen W) (hst : ∀ g, W ≤ (ρ g).hom ⁻¹ᵁ W) (ξ : Sp k ⟶ X) (h : ⊤ ≤ ξ ⁻¹ᵁ W)
    (g : Γ) :
    letI := sectionsAction ρ W hst
    g⁻¹ ∈ (RingHom.ker (evalAt ξ W h)).inertia Γ ↔ ξ ≫ (ρ g).hom = ξ := by
  let := sectionsAction ρ W hst
  have e (b : Γ(X, W)) : g⁻¹ • b = ((ρ g).hom.appLE W W (hst g)).hom b := by
    have : g⁻¹ • b = ((ρ g⁻¹⁻¹).hom.appLE W W (hst _)).hom b := rfl
    simpa only [inv_inv] using this
  refine ⟨fun hg => ?_, fun hg b => ?_⟩
  · have e1 : ξ.appLE _ ⊤ h = (ρ g).hom.appLE _ _ (hst _) ≫ ξ.appLE _ ⊤ h := by
      rw [← cancel_mono (Scheme.ΓSpecIso (.of k)).hom]
      ext b
      have : evalAt ξ W h (g⁻¹ • b - b) = 0 := hg b
      rw [map_sub, sub_eq_zero, e] at this
      exact this.symm
    have hT := isAffineOpen_top (Sp k)
    have : IsIso hT.fromSpec := by rw [IsAffineOpen.fromSpec_top]; infer_instance
    symm
    rw [← cancel_epi hT.fromSpec, ← IsAffineOpen.SpecMap_appLE_fromSpec ξ hW hT h, e1,
      Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec _ hW hW,
      IsAffineOpen.SpecMap_appLE_fromSpec_assoc ξ hW hT h]
  · change evalAt ξ W h (g⁻¹ • b - b) = 0
    rw [map_sub, sub_eq_zero, e]
    exact evalAt_appLE ξ _ _ _ _ _ b ξ hg h

theorem nonvanishing_pullSec {L : LB X} (φ : Y ⟶ X) {O : X.Opens} (t : Γ(toMod L, O)) (y : Y) :
    (∃ j, y ∈ Y.basicOpen (coord (pullSec L φ O t) j)) ↔ ∃ i, φ y ∈ X.basicOpen (coord t i) := by
  simp only [coord_pullSec, mem_basicOpen_appLE]
  exact ⟨fun ⟨j, hj⟩ => ⟨_, hj.2⟩,
    fun ⟨i, hi⟩ => ⟨fun _ => i, le_pull_chart φ O i (X.basicOpen_le _ hi), hi⟩⟩

theorem exists_descent_nonvanishing {Γ : Type} [Group Γ] [Finite Γ] {X' G G' : Scheme.{0}}
    (ρ : Γ →* Aut X) (π : X ⟶ X') (p : G ⟶ X) (p' : G' ⟶ X') (φ : G ⟶ G') (τ : Γ →* Aut G)
    (hπ : ∀ g, (ρ g).hom ≫ π = π) (w : φ ≫ p' = p ≫ π) (hφ : ∀ g, (τ g).hom ≫ φ = φ)
    (hp : ∀ g, (τ g).hom ≫ p = p ≫ (ρ g).hom)
    (hq : ∀ V : G'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(G, φ ⁻¹ᵁ V),
      (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (φ.app V).hom)
    (htame : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X),
      (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x →
      pullback.fst p x ≫ (τ g).hom = pullback.fst p x)
    {L : LB G'} {V : X'.Opens} (hW : IsAffineOpen (π ⁻¹ᵁ V))
    (s : Γ(toMod (L.pull φ), φ ⁻¹ᵁ p' ⁻¹ᵁ V)) (u : G) (hs : ∃ j, u ∈ G.basicOpen (coord s j)) :
    ∃ (t : Γ(toMod L, p' ⁻¹ᵁ V)) (i : L.ι), φ u ∈ G'.basicOpen (coord t i) := by
  have := Fintype.ofFinite Γ
  obtain ⟨j, hj⟩ := hs
  obtain ⟨i, rfl⟩ : ∃ i : L.ι, j = fun _ => i := ⟨j PUnit.unit, rfl⟩
  have hu : u ∈ φ ⁻¹ᵁ (p' ⁻¹ᵁ V ⊓ L.U i) := pull_inf_le φ _ _ (G.basicOpen_le _ hj)
  let k := AlgebraicClosure (G.residueField u)
  let ζ : Sp k ⟶ G := Spec.map (CommRingCat.ofHom (algebraMap (G.residueField u) k)) ≫
    G.fromSpecResidueField u
  have hζ (z : Sp k) : ζ z = u :=
    (Scheme.Hom.comp_apply _ _ z).trans (Scheme.fromSpecResidueField_apply _ _)
  have e : φ ⁻¹ᵁ p' ⁻¹ᵁ V = p ⁻¹ᵁ π ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, w, Scheme.Hom.comp_preimage]
  have hA : φ ⁻¹ᵁ (p' ⁻¹ᵁ V ⊓ L.U i) ≤ p ⁻¹ᵁ π ⁻¹ᵁ V :=
    (φ.preimage_mono inf_le_left).trans e.le
  have h1 : ⊤ ≤ ζ ⁻¹ᵁ φ ⁻¹ᵁ (p' ⁻¹ᵁ V ⊓ L.U i) := fun z _ => by
    change ζ z ∈ φ ⁻¹ᵁ (p' ⁻¹ᵁ V ⊓ L.U i)
    rwa [hζ]
  have h2 : ⊤ ≤ (ζ ≫ p) ⁻¹ᵁ π ⁻¹ᵁ V := h1.trans (ζ.preimage_mono hA)
  have hst := preimage_le_of_invariant ρ π hπ V
  have hst' := preimage_le_of_invariant τ φ hφ (p' ⁻¹ᵁ V ⊓ L.U i)
  let := sectionsAction ρ _ hst
  let := sectionsAction τ _ hst'
  have hev : (evalAt ζ _ h1).comp (p.appLE _ _ hA).hom = evalAt (ζ ≫ p) _ h2 :=
    RingHom.ext fun b => evalAt_appLE ζ p _ _ h1 hA b _ rfl h2
  have hI (g : Γ) := mem_inertia_iff ρ hW hst (ζ ≫ p) h2 g
  let z : Sp k := default
  obtain ⟨c, hc⟩ := exists_trace_ne_zero (Γ := Γ) (p.appLE _ _ hA).hom (fun g b => by
      change (p.appLE _ _ hA).hom (((ρ g⁻¹).hom.appLE _ _ (hst _)).hom b) =
        ((τ g⁻¹).hom.appLE _ _ (hst' _)).hom ((p.appLE _ _ hA).hom b)
      simp only [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE, hp])
    (evalAt ζ _ h1) (by
      rw [hev]
      convert htame k (ζ ≫ p) using 2
      exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by rw [← hI, inv_mem_iff]))
    (resG G (le_pull_chart φ _ i) (coord s fun _ => i)) (fun g hg => by
      rw [hev, ← inv_inv g, hI] at hg
      have := pullback.lift ζ (𝟙 _) (Category.id_comp _).symm ≫= hfib k (ζ ≫ p) _ hg
      rw [pullback.lift_fst_assoc, pullback.lift_fst] at this
      exact evalAt_appLE ζ (τ g⁻¹).hom _ _ h1 (hst' _) _ ζ this h1)
    (by
      rw [evalAt_ne_zero _ _ _ _ z, hζ, mem_basicOpen_resG]
      exact ⟨hu, hj⟩)
  obtain ⟨t, ht⟩ := exists_descent τ φ hφ hq _ ((p.appLE _ _ e.le).hom c • s)
  refine ⟨t, i, ?_⟩
  rw [evalAt_ne_zero _ _ _ _ z, hζ] at hc
  have h3 := ht i
  rw [coord_smul (L := L.pull φ) _ s (fun _ => i), map_mul, resG_resG, resG_appLE, Scheme.Hom.app_eq_appLE] at h3
  refine ((mem_basicOpen_appLE φ le_rfl (coord t i) u).1 ?_).2
  rw [h3]
  exact hc

end GlobalTheory.DescTheta

namespace GlobalTheory

open DescTheta GlobalTheory.LB

theorem exists_secOn_nonvanishing_of_tame_quotient :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) (G' : Over X') (φ : G.left ⟶ G'.left) (τ : Γ →* Aut G.left) (L : LB G.left) (L' : LB G'.left), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsPullback φ G.hom G'.hom π → Flat G'.hom → (∀ g, (τ g).hom ≫ φ = φ ∧ (τ g).hom ≫ G.hom = G.hom ≫ (ρ g).hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x → pullback.fst G.hom x ≫ (τ g).hom = pullback.fst G.hom x) → L.IsLB → L'.IsLB → LBIso L (L'.pull φ) → PushInvertible G L → (∀ x : X', ∃ V : X'.Opens, x ∈ V ∧ ∃ θ ∈ secOn L' (G'.hom ⁻¹ᵁ V), ∀ y ∈ V, ∃ (g : G'.left) (i : L'.ι), G'.hom g = y ∧ g ∈ G'.left.basicOpen (θ i)) := by
  intro Γ _ _ X X' ρ π G G' φ τ L L' hQ H hflat hτ htame hfib hL hL' ⟨w, hw⟩ hP x'
  obtain ⟨-, hφ, hq⟩ := (quotient_flat_baseChange Γ X X' _ _ ρ π φ G.hom G'.hom hQ H hflat).2 τ hτ
  obtain ⟨-, hsurj, -, -, hopen⟩ := quotient_isIntegral_surjective_orbits Γ X X' ρ π hQ
  obtain ⟨_, hπ, -⟩ := hQ
  have hM := Semi.LB.isLB_pull hL' φ
  obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x') isOpen_univ
  have hW : IsAffineOpen (π ⁻¹ᵁ V) := IsAffineOpen.preimage hV π
  obtain ⟨x, rfl⟩ := π.surjective x'
  have e : φ ⁻¹ᵁ G'.hom ⁻¹ᵁ V = G.hom ⁻¹ᵁ π ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
  obtain ⟨s, u, rfl, i, hi⟩ := exists_sec_nonvanishing hP hW hx
  obtain ⟨t, ht⟩ := exists_descent_nonvanishing ρ π G.hom G'.hom φ τ hπ H.w hφ (fun g => (hτ g).2)
    hq htame hfib hW ((isoOfGen hL hM w hw).hom.app _ ((toMod L).presheaf.map (homOfLE e.le).op s))
    u ((nonvanishing_iso hL hM w hw _ u).2 ⟨i, by
      rw [coord_map, mem_basicOpen_resG]
      exact ⟨⟨e.ge hx, (G.left.basicOpen_le _ hi).2⟩, hi⟩⟩)
  obtain ⟨s', hs'⟩ := (ConcreteCategory.bijective_of_isIso
    ((isoOfGen hL hM w hw).hom.app (φ ⁻¹ᵁ G'.hom ⁻¹ᵁ V))).2 (pullSec L' φ _ t)
  have key (y : G.left) : (∃ i, y ∈ G.left.basicOpen (coord s' i)) ↔
      ∃ i, φ y ∈ G'.left.basicOpen (coord t i) := by
    rw [← nonvanishing_iso hL hM w hw, hs', nonvanishing_pullSec]
  obtain ⟨U, -, hxU, hU⟩ := exists_nhds_nonvanishing hP e.ge s' u hx ((key u).2 ht)
  obtain ⟨V', hV'⟩ := hopen (⨆ g, (ρ g).hom ⁻¹ᵁ U) fun g => by
    have (h : Γ) : (ρ g).hom ⁻¹ᵁ (ρ h).hom ⁻¹ᵁ U = (ρ (h * g)).hom ⁻¹ᵁ U := by
      rw [map_mul]; rfl
    simp only [Scheme.Hom.preimage_iSup, this]
    exact Equiv.iSup_comp (g := fun h => (ρ h).hom ⁻¹ᵁ U) (Equiv.mulRight g)
  have hle : G'.hom ⁻¹ᵁ (V ⊓ V') ≤ G'.hom ⁻¹ᵁ V := G'.hom.preimage_mono inf_le_left
  refine ⟨V ⊓ V', ⟨hx, hV'.ge (TopologicalSpace.Opens.mem_iSup.2 ⟨1, ?_⟩)⟩, _,
    coord_mem ((toMod L').presheaf.map (homOfLE hle).op t), fun y hy => ?_⟩
  · rw [map_one]; exact hxU
  obtain ⟨z, rfl⟩ := π.surjective y
  obtain ⟨g, hg⟩ := TopologicalSpace.Opens.mem_iSup.1 (hV'.le hy.2)
  obtain ⟨v, hv, hv'⟩ := hU _ hg
  obtain ⟨j, hj⟩ := (key v).1 hv'
  have e2 : G'.hom (φ v) = π z := by
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply, hv, ← Scheme.Hom.comp_apply, hπ]
  refine ⟨φ v, j, e2, ?_⟩
  rw [coord_map, mem_basicOpen_resG]
  exact ⟨⟨by rw [← e2] at hy; exact hy, (G'.left.basicOpen_le _ hj).2⟩, hj⟩

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.TameResidue

theorem exists_sum_ne_zero {D k K : Type} [Group D] [Fintype D] [Field k] [Field K] [Algebra k K]
    (φ : D →* (K ≃ₐ[k] K)) (h : (Nat.card φ.ker : K) ≠ 0) : ∃ w : K, ∑ g, φ g w ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hf : Function.Injective (fun σ : K ≃ₐ[k] K => (σ : K →* K)) :=
    fun σ τ hστ => AlgEquiv.ext fun x => DFunLike.congr_fun hστ x
  have hli := (linearIndependent_monoidHom K K).comp _ hf
  have hfib : ∀ σ ∈ Finset.univ.image φ,
      (Finset.univ.filter fun g => φ g = σ).card = Nat.card φ.ker := by
    intro σ hσ
    obtain ⟨g0, -, rfl⟩ := Finset.mem_image.1 hσ
    rw [MonoidHom.card_fiber_eq_of_mem_range φ ⟨g0, rfl⟩ ⟨1, rfl⟩, map_one,
      ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [MonoidHom.mem_ker])
  have hsum : ∀ w : K, ∑ g, φ g w = ∑ σ ∈ Finset.univ.image φ, (Nat.card φ.ker : K) * σ w := by
    intro w
    rw [← Finset.sum_fiberwise_of_maps_to (g := φ) (t := Finset.univ.image φ)
      (fun g _ => Finset.mem_image_of_mem φ (Finset.mem_univ g))]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [Finset.sum_congr rfl (fun g hg => by rw [(Finset.mem_filter.1 hg).2]), Finset.sum_const,
      hfib σ hσ, nsmul_eq_mul]
  refine h (linearIndependent_iff'.1 hli (Finset.univ.image φ) (fun _ => (Nat.card φ.ker : K)) ?_ (φ 1)
    (Finset.mem_image_of_mem _ (Finset.mem_univ 1)))
  funext w
  have hw := hcon w
  rw [hsum w] at hw
  simpa [Finset.sum_apply] using hw

theorem finite_separable_of_sum_mem {D k K : Type} [Group D] [Fintype D] [Field k] [Field K]
    [Algebra k K] (φ : D →* (K ≃ₐ[k] K)) (h : (Nat.card φ.ker : K) ≠ 0)
    (hT : ∀ x : K, ∃ c : k, algebraMap k K c = ∑ g, φ g x) :
    FiniteDimensional k K ∧ Algebra.IsSeparable k K := by
  classical
  obtain ⟨w, hw⟩ := exists_sum_ne_zero φ h
  obtain ⟨c, hc⟩ := hT w
  have hcw : algebraMap k K c ≠ 0 := by rw [hc]; exact hw
  have hfix : ∀ y : K, (∀ g : D, φ g y = y) → ∃ c' : k, algebraMap k K c' = y := by
    intro y hy
    obtain ⟨c', hc'⟩ := hT (y * w)
    refine ⟨c' / c, ?_⟩
    rw [map_div₀, hc', div_eq_iff hcw, hc]
    simp only [map_mul, hy, Finset.mul_sum]
  letI : MulSemiringAction D K := MulSemiringAction.compHom K φ
  have hF : ∀ x : FixedPoints.subfield D K, ∃ c' : k, algebraMap k K c' = x :=
    fun x => hfix x fun g => x.2 g
  refine ⟨?_, ?_⟩
  · let b := Module.finBasis (FixedPoints.subfield D K) K
    refine ⟨⟨Finset.univ.image b, eq_top_iff.2 fun x _ => ?_⟩⟩
    rw [← b.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c', hc'⟩ := hF (b.repr x i)
    have he : b.repr x i • b i = c' • b i := by
      rw [Algebra.smul_def, Algebra.smul_def, hc']
      rfl
    rw [he]
    exact Submodule.smul_mem _ c' (Submodule.subset_span
      (Finset.mem_coe.2 (Finset.mem_image_of_mem b (Finset.mem_univ i))))
  · refine ⟨fun x => ?_⟩
    have hsF : (minpoly (FixedPoints.subfield D K) x).Separable :=
      Algebra.IsSeparable.isSeparable (FixedPoints.subfield D K) x
    have hl : (minpoly (FixedPoints.subfield D K) x).map
        (algebraMap (FixedPoints.subfield D K) K) ∈ Polynomial.lifts (algebraMap k K) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨c', hc'⟩ := hF ((minpoly (FixedPoints.subfield D K) x).coeff n)
      exact ⟨c', hc'⟩
    obtain ⟨pk, hpk⟩ := Polynomial.mem_lifts _ |>.1 hl
    have hsep : pk.Separable := by
      rw [← Polynomial.separable_map (algebraMap k K), hpk, Polynomial.separable_map]
      exact hsF
    have hx : Polynomial.aeval x pk = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, hpk, Polynomial.eval_map,
        ← Polynomial.aeval_def, minpoly.aeval]
    exact hsep.of_dvd (minpoly.dvd k x hx)

theorem exists_not_mem_smul_mem {Γ B : Type} [Group Γ] [Finite Γ] [CommRing B]
    [MulSemiringAction Γ B] (q : Ideal B) [q.IsPrime] :
    ∃ y : B, y ∉ q ∧ ∀ g : Γ, g • q ≠ q → g • y ∈ q := by
  classical
  have hpow : ∀ h : Γ, h ^ (Nat.card Γ - 1) = h⁻¹ := fun h =>
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel Nat.card_pos, pow_card_eq_one'])
  have hex : ∀ g : Γ, ∃ a : B, a ∉ q ∧ (g • q ≠ q → g • a ∈ q) := by
    intro g
    by_cases hg : g • q = q
    · exact ⟨1, (Ideal.ne_top_iff_one q).1 (Ideal.IsPrime.ne_top inferInstance),
        fun h => absurd hg h⟩
    · by_contra hcon
      apply hg
      have h1 : ∀ a : B, g • a ∈ q → a ∈ q := fun a ha =>
        by_contra fun hn => hcon ⟨a, hn, fun _ => ha⟩
      have h2 : ∀ x ∈ q, g⁻¹ • x ∈ q := fun x hx => h1 _ (by rwa [smul_inv_smul])
      have h3 : ∀ m : ℕ, ∀ x ∈ q, (g⁻¹) ^ m • x ∈ q := by
        intro m
        induction m with
        | zero => intro x hx; rwa [pow_zero, one_smul]
        | succ m ih => intro x hx; rw [pow_succ', mul_smul]; exact h2 _ (ih x hx)
      have h5 : ∀ x ∈ q, g • x ∈ q := fun x hx => by
        have := h3 (Nat.card Γ - 1) x hx
        rwa [hpow, inv_inv] at this
      apply Ideal.ext
      intro x
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      exact ⟨fun hx => by simpa using h5 _ hx, h2 x⟩
  choose a ha using hex
  haveI := Fintype.ofFinite Γ
  refine ⟨∏ g, a g, ?_, fun g hg => ?_⟩
  · exact prod_mem (S := q.primeCompl) fun g _ => (ha g).1
  · rw [Finset.smul_prod']
    exact q.mem_of_dvd (Finset.dvd_prod_of_mem (fun i => g • a i) (Finset.mem_univ g)) ((ha g).2 hg)

theorem residue_finite_separable : ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [MulSemiringAction Γ B] [SMulCommClass Γ A B] [Algebra.IsInvariant A B Γ] (q : Ideal B) [q.IsPrime] (k K : Type) [Field k] [Field K] [Algebra (A ⧸ q.under A) k] [IsFractionRing (A ⧸ q.under A) k] [Algebra (B ⧸ q) K] [IsFractionRing (B ⧸ q) K] [Algebra k K], (∀ a : A, algebraMap k K (algebraMap (A ⧸ q.under A) k (Ideal.Quotient.mk _ a)) = algebraMap (B ⧸ q) K (Ideal.Quotient.mk q (algebraMap A B a))) → (Nat.card (q.inertia Γ) : B) ∉ q → FiniteDimensional k K ∧ Algebra.IsSeparable k K := by
  intro Γ _ _ A B _ _ _ _ _ _ q _ k K _ _ _ _ _ _ _ hcomp hin
  classical
  haveI := Fintype.ofFinite Γ
  letI : Algebra (A ⧸ q.under A) K :=
    ((algebraMap k K).comp (algebraMap (A ⧸ q.under A) k)).toAlgebra
  haveI : IsScalarTower (A ⧸ q.under A) k K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (A ⧸ q.under A) (B ⧸ q) K := IsScalarTower.of_algebraMap_eq fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hcomp a
  let ψ := Ideal.Quotient.stabilizerHom q (q.under A) Γ
  let φ : MulAction.stabilizer Γ q →* (K ≃ₐ[k] K) :=
    (IsFractionRing.fieldEquivOfAlgEquivHom k K).comp ψ
  have hφ : ∀ (g : MulAction.stabilizer Γ q) (u : B ⧸ q),
      φ g (algebraMap (B ⧸ q) K u) = algebraMap (B ⧸ q) K (ψ g u) := fun g u => by
    simp [φ, IsFractionRing.fieldEquivOfAlgEquivHom, IsFractionRing.fieldEquivOfAlgEquiv_algebraMap]
  have hψ : ∀ (g : MulAction.stabilizer Γ q) (b : B),
      ψ g (Ideal.Quotient.mk q b) = Ideal.Quotient.mk q ((g : Γ) • b) := fun g b => by
    first
      | rfl
      | simp [ψ, Ideal.Quotient.stabilizerHom]
  have hι : ∀ u : B ⧸ q, u ≠ 0 → algebraMap (B ⧸ q) K u ≠ 0 := fun u hu h0 =>
    hu (IsFractionRing.injective (B ⧸ q) K (h0.trans (map_zero _).symm))
  have hsplit : ∀ F : Γ → K, (∀ g : Γ, g ∉ MulAction.stabilizer Γ q → F g = 0) →
      ∑ g, F g = ∑ g : MulAction.stabilizer Γ q, F g := by
    intro F hF
    have hs := Finset.sum_subset (Finset.subset_univ
      (Finset.univ.map (Function.Embedding.subtype (· ∈ MulAction.stabilizer Γ q)))) (f := F)
      (fun g _ hg => hF g fun hs => hg (Finset.mem_map.2 ⟨⟨g, hs⟩, Finset.mem_univ _, rfl⟩))
    rw [← hs, Finset.sum_map]
    rfl
  have hle : q.inertia Γ ≤ MulAction.stabilizer Γ q := by
    intro g hg
    have hg' : g⁻¹ ∈ q.inertia Γ := inv_mem hg
    rw [MulAction.mem_stabilizer_iff]
    apply Ideal.ext
    intro x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have hx : g⁻¹ • x - x ∈ q := hg' x
    constructor
    · intro h1; simpa using q.sub_mem h1 hx
    · intro h1; simpa using q.add_mem hx h1
  have hmem : ∀ g : MulAction.stabilizer Γ q, g ∈ φ.ker ↔ (g : Γ) ∈ q.inertia Γ := by
    intro g
    rw [MonoidHom.mem_ker]
    constructor
    · intro h x
      have := congrArg (fun e : K ≃ₐ[k] K => e (algebraMap (B ⧸ q) K (Ideal.Quotient.mk q x))) h
      simp only [hφ, hψ, AlgEquiv.one_apply] at this
      exact Ideal.Quotient.eq.1 (IsFractionRing.injective (B ⧸ q) K this)
    · intro h
      ext z
      obtain ⟨u, v, -, rfl⟩ := IsFractionRing.div_surjective (A := B ⧸ q) z
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
      obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
      simp only [map_div₀, hφ, hψ, AlgEquiv.one_apply]
      rw [Ideal.Quotient.eq.2 (h u), Ideal.Quotient.eq.2 (h v)]
  have hcardeq : Nat.card φ.ker = Nat.card (q.inertia Γ) :=
    Nat.card_congr
      { toFun := fun g => ⟨((g.1 : MulAction.stabilizer Γ q) : Γ), (hmem g.1).1 g.2⟩
        invFun := fun h => ⟨⟨h.1, hle h.2⟩, (hmem ⟨h.1, hle h.2⟩).2 h.2⟩
        left_inv := fun g => rfl
        right_inv := fun h => rfl }
  have hkerK : ((Nat.card φ.ker : ℕ) : K) ≠ 0 := by
    rw [hcardeq]
    intro h0
    apply hin
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply IsFractionRing.injective (B ⧸ q) K
    simpa using h0
  obtain ⟨y, hyq, hy⟩ := exists_not_mem_smul_mem (Γ := Γ) q
  have hB : ∀ u : B ⧸ q, ∃ c : k, algebraMap k K c =
      ∑ g, φ g (algebraMap (B ⧸ q) K u * algebraMap (B ⧸ q) K (Ideal.Quotient.mk q y)) := by
    intro u
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := Γ) (∑ g : Γ, g • (b * y))
      (fun h => by
        rw [Finset.smul_sum]
        exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => by simp [mul_smul]))
    refine ⟨algebraMap (A ⧸ q.under A) k (Ideal.Quotient.mk _ a), ?_⟩
    rw [hcomp, ha, map_sum, map_sum]
    simp only [← map_mul, hφ, hψ]
    refine hsplit (fun g => algebraMap (B ⧸ q) K (Ideal.Quotient.mk q (g • (b * y)))) (fun g hg => ?_)
    have hne : g • q ≠ q := fun h => hg (MulAction.mem_stabilizer_iff.2 h)
    show algebraMap (B ⧸ q) K (Ideal.Quotient.mk q (g • (b * y))) = 0
    rw [smul_mul', Ideal.Quotient.eq_zero_iff_mem.2 (q.mul_mem_left _ (hy g hne)), map_zero]
  have hTinv : ∀ (x : K) (h : MulAction.stabilizer Γ q), φ h (∑ g, φ g x) = ∑ g, φ g x := by
    intro x h
    rw [map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => by simp [map_mul, AlgEquiv.mul_apply])
  have hTlin : ∀ z x : K, (∀ g, φ g z = z) → ∑ g, φ g (z * x) = z * ∑ g, φ g x := by
    intro z x hz
    simp only [map_mul, hz, Finset.mul_sum]
  obtain ⟨w0, hw0⟩ := exists_sum_ne_zero φ hkerK
  have hyq' : algebraMap (B ⧸ q) K (Ideal.Quotient.mk q y) ≠ 0 :=
    hι _ (fun h0 => hyq (Ideal.Quotient.eq_zero_iff_mem.1 h0))
  have hfixk : ∀ z : K, (∀ g, φ g z = z) → ∃ c : k, algebraMap k K c = z := by
    intro z hz
    obtain ⟨u, v, hv, huv⟩ := IsFractionRing.div_surjective (A := B ⧸ q) z
    have hv0 : algebraMap (B ⧸ q) K v ≠ 0 := hι _ (nonZeroDivisors.ne_zero hv)
    set c0 := algebraMap (B ⧸ q) K v * algebraMap (B ⧸ q) K (Ideal.Quotient.mk q y) with hc0def
    have hc0 : c0 ≠ 0 := mul_ne_zero hv0 hyq'
    have ht : ∃ t : B ⧸ q, ∑ g, φ g (c0 * algebraMap (B ⧸ q) K t) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hw0
      obtain ⟨t1, t2, ht2, hdiv⟩ := IsFractionRing.div_surjective (A := B ⧸ q) (w0 / c0)
      have ht20 : t2 ≠ 0 := nonZeroDivisors.ne_zero ht2
      set M' := ∏ g ∈ Finset.univ.erase (1 : MulAction.stabilizer Γ q), ψ g t2 with hM'
      have hM : ∏ g, ψ g t2 = t2 * M' := by
        rw [← Finset.mul_prod_erase Finset.univ (fun g => ψ g t2) (Finset.mem_univ 1), map_one]
        rfl
      have hMinv : ∀ h, φ h (algebraMap (B ⧸ q) K (∏ g, ψ g t2)) =
          algebraMap (B ⧸ q) K (∏ g, ψ g t2) := by
        intro h
        rw [hφ, map_prod]
        congr 1
        exact Fintype.prod_equiv (Equiv.mulLeft h) _ _ (fun g => by simp [map_mul, AlgEquiv.mul_apply])
      have hM0 : ∏ g, ψ g t2 ≠ 0 := Finset.prod_ne_zero_iff.2 fun g _ h0 =>
        ht20 ((ψ g).injective (h0.trans (map_zero _).symm))
      have hdiv' : algebraMap (B ⧸ q) K t1 * c0 = w0 * algebraMap (B ⧸ q) K t2 := by
        rw [div_eq_div_iff (hι _ ht20) hc0] at hdiv
        exact hdiv
      have hw : w0 * algebraMap (B ⧸ q) K (∏ g, ψ g t2) = c0 * algebraMap (B ⧸ q) K (t1 * M') := by
        rw [hM, map_mul, map_mul]
        linear_combination (-(algebraMap (B ⧸ q) K M')) * hdiv'
      have h1 : algebraMap (B ⧸ q) K (∏ g, ψ g t2) * ∑ g, φ g w0 = 0 := by
        rw [← hTlin _ w0 hMinv, mul_comm, hw]
        exact hcon _
      exact (mul_eq_zero.1 h1).resolve_left (hι _ hM0)
    obtain ⟨t, ht⟩ := ht
    obtain ⟨c1, hc1⟩ := hB (u * t)
    obtain ⟨c2, hc2⟩ := hB (v * t)
    refine ⟨c1 / c2, ?_⟩
    have e2 : ∑ g, φ g (c0 * algebraMap (B ⧸ q) K t) = algebraMap k K c2 := by
      rw [hc2, map_mul]
      refine Finset.sum_congr rfl fun g _ => congrArg (φ g) ?_
      rw [hc0def]
      ring
    have e1 : ∑ g, φ g (z * (c0 * algebraMap (B ⧸ q) K t)) = algebraMap k K c1 := by
      rw [hc1, map_mul]
      refine Finset.sum_congr rfl fun g _ => congrArg (φ g) ?_
      rw [hc0def, ← huv, div_mul_eq_mul_div, div_eq_iff hv0]
      ring
    rw [hTlin z _ hz, e2] at e1
    have hc2ne : algebraMap k K c2 ≠ 0 := by rw [← e2]; exact ht
    rw [map_div₀, ← e1, mul_div_assoc, div_self hc2ne, _root_.mul_one]
  exact finite_separable_of_sum_mem φ hkerK (fun x => hfixk _ (hTinv x))

end GlobalTheory.TameResidue
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_eq_evaluation_div {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (z : X.residueField x) : ∃ a b : Γ(X, U), z = X.evaluation U x hx a / X.evaluation U x hx b := by
  classical
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  haveI : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  have he : ∀ c, X.evaluation U x hx c =
      (X.residue x).hom (algebraMap Γ(X, U) (X.presheaf.stalk x) c) := fun c => rfl
  obtain ⟨s, rfl⟩ : ∃ s, (X.residue x).hom s = z := IsLocalRing.residue_surjective z
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl s
  change s * algebraMap Γ(X, U) (X.presheaf.stalk x) (b : Γ(X, U)) =
    algebraMap Γ(X, U) (X.presheaf.stalk x) a at hab
  have hb0 : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) (b : Γ(X, U))) :=
    IsLocalization.map_units _ b
  have hb := hb0.map (X.residue x).hom
  refine ⟨a, b, ?_⟩
  rw [he, he, eq_div_iff hb.ne_zero, ← map_mul (X.residue x).hom, hab]

theorem isFractionRing_residueField {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (q : Ideal Γ(X, U)) (hq : ∀ a, a ∈ q ↔ X.evaluation U x hx a = 0) :
    letI := (Ideal.Quotient.lift q (X.evaluation U x hx).hom fun a ha ↦ (hq a).1 ha).toAlgebra
    IsFractionRing (Γ(X, U) ⧸ q) (X.residueField x) := by
  letI : Algebra (Γ(X, U) ⧸ q) (X.residueField x) :=
    (Ideal.Quotient.lift q (X.evaluation U x hx).hom fun a ha ↦ (hq a).1 ha).toAlgebra
  have hmk : ∀ a, algebraMap (Γ(X, U) ⧸ q) (X.residueField x) (Ideal.Quotient.mk q a) =
      X.evaluation U x hx a := fun a => Ideal.Quotient.lift_mk _ _ _
  have hinj : Function.Injective (algebraMap (Γ(X, U) ⧸ q) (X.residueField x)) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hmk] at hc
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hq a).2 hc)
  haveI : NoZeroDivisors (Γ(X, U) ⧸ q) :=
    hinj.noZeroDivisors _ (map_zero _) (map_mul _)
  refine ⟨?_, ?_, ?_⟩
  · intro y
    refine isUnit_iff_ne_zero.mpr fun h => ?_
    haveI : Nontrivial (Γ(X, U) ⧸ q) :=
      ⟨⟨0, 1, fun h => by simpa using congrArg (algebraMap (Γ(X, U) ⧸ q) (X.residueField x)) h⟩⟩
    exact nonZeroDivisors.ne_zero y.2 (hinj (h.trans (map_zero _).symm))
  · intro z
    obtain ⟨a, b, hz⟩ := exists_eq_evaluation_div hU x hx z
    by_cases hb : X.evaluation U x hx b = 0
    · refine ⟨(0, 1), ?_⟩
      show z * algebraMap (Γ(X, U) ⧸ q) (X.residueField x) 1 =
        algebraMap (Γ(X, U) ⧸ q) (X.residueField x) 0
      rw [hz, hb, div_zero, zero_mul, map_zero]
    · have hb' : Ideal.Quotient.mk q b ≠ 0 := by
        intro h
        apply hb
        rw [← hmk, h, map_zero]
      refine ⟨(Ideal.Quotient.mk q a, ⟨Ideal.Quotient.mk q b, mem_nonZeroDivisors_of_ne_zero hb'⟩), ?_⟩
      show z * algebraMap (Γ(X, U) ⧸ q) (X.residueField x) (Ideal.Quotient.mk q b) =
        algebraMap (Γ(X, U) ⧸ q) (X.residueField x) (Ideal.Quotient.mk q a)
      rw [hz, hmk, hmk, div_mul_cancel₀ _ hb]
  · intro c d h
    exact ⟨1, by rw [hinj h]⟩

theorem residueFieldMap_finite_separable_of_tame {Γ : Type} [Group Γ] [Finite Γ] {X X' : Scheme.{0}}
    (ρ : Γ →* Aut X) (π : X ⟶ X') [IsAffineHom π] (hπ : ∀ g, (ρ g).hom ≫ π = π)
    (hinv : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W))
    (ht : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0)
    (x : X) :
    letI := (π.residueFieldMap x).hom.toAlgebra
    FiniteDimensional (X'.residueField (π x)) (X.residueField x) ∧
      Algebra.IsSeparable (X'.residueField (π x)) (X.residueField x) := by
  let := (π.residueFieldMap x).hom.toAlgebra
  obtain ⟨_, ⟨(W : X'.Opens), hW, rfl⟩, hx, -⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (π x)) isOpen_univ
  have hx : π x ∈ W := hx
  have hW : IsAffineOpen W := hW
  have hU : IsAffineOpen (π ⁻¹ᵁ W) := hW.preimage π
  have hst := preimage_le_of_invariant ρ π hπ W
  let := sectionsAction ρ _ hst
  let := (π.app W).hom.toAlgebra
  have hfix (g : Γ) (a : Γ(X', W)) : g • algebraMap Γ(X', W) Γ(X, π ⁻¹ᵁ W) a = algebraMap _ _ a :=
    (isInvariantSection_app ρ π hπ W a g⁻¹).2
  have : SMulCommClass Γ Γ(X', W) Γ(X, π ⁻¹ᵁ W) := ⟨fun g a s ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have : Algebra.IsInvariant Γ(X', W) Γ(X, π ⁻¹ᵁ W) Γ := ⟨fun s hs ↦
    hinv W hW s fun g ↦ ⟨hst g, by simpa only [inv_inv] using
      (show (ρ g⁻¹⁻¹).hom.appLE _ _ (hst _) s = s from hs g⁻¹)⟩⟩
  let ev := X.evaluation (π ⁻¹ᵁ W) x hx
  let q : Ideal Γ(X, π ⁻¹ᵁ W) := RingHom.ker ev.hom
  have : q.IsPrime := RingHom.ker_isPrime _
  have hq : ∀ a, a ∈ q ↔ ev a = 0 := fun a ↦ Iff.rfl
  have hnat (a : Γ(X', W)) : π.residueFieldMap x (X'.evaluation W (π x) hx a) = ev (π.app W a) :=
    Scheme.evaluation_naturality_apply π x hx a
  have hp : ∀ a, a ∈ q.under Γ(X', W) ↔ X'.evaluation W (π x) hx a = 0 := fun a ↦ by
    rw [← map_eq_zero_iff _ (π.residueFieldMap x).hom.injective, hnat]
    rfl
  let := (Ideal.Quotient.lift q ev.hom fun a ha ↦ (hq a).1 ha).toAlgebra
  let := (Ideal.Quotient.lift _ (X'.evaluation W (π x) hx).hom fun a ha ↦ (hp a).1 ha).toAlgebra
  have := isFractionRing_residueField hU x hx q hq
  have := isFractionRing_residueField hW (π x) hx _ hp
  refine TameResidue.residue_finite_separable Γ Γ(X', W) Γ(X, π ⁻¹ᵁ W) q _ _ hnat fun hc ↦ ?_
  let Ω := AlgebraicClosure (X.residueField x)
  let jΩ : X.residueField x ⟶ CommRingCat.of Ω := CommRingCat.ofHom (algebraMap (X.residueField x) Ω)
  let y : Sp Ω ⟶ X := Spec.map (ev ≫ jΩ) ≫ hU.fromSpec
  have key (g : Γ) : g⁻¹ ∈ q.inertia Γ ↔ y ≫ (ρ g).hom = y := by
    have e : y ≫ (ρ g).hom = Spec.map ((ρ g).hom.appLE _ _ (hst g) ≫ ev ≫ jΩ) ≫ hU.fromSpec := by
      rw [Spec.map_comp, Category.assoc, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec _ hU hU]
    have : Mono jΩ := ConcreteCategory.mono_of_injective _ jΩ.hom.injective
    rw [e, cancel_mono, Spec.map_inj, ← Category.assoc, cancel_mono]
    have e₂ (s) : g⁻¹ • s = (ρ g).hom.appLE _ _ (hst g) s := by
      change (ρ g⁻¹⁻¹).hom.appLE _ _ (hst _) s = _
      simp only [inv_inv]
    refine Iff.trans AddSubgroup.mem_inertia ⟨fun h ↦ ?_, fun h s ↦ ?_⟩
    · ext s
      have := (hq _).1 (h s)
      rw [map_sub, sub_eq_zero, e₂] at this
      exact this
    · refine (hq _).2 ?_
      rw [map_sub, sub_eq_zero, e₂]
      exact congr($h s)
  have hcard : Nat.card {g // y ≫ (ρ g).hom = y} = Nat.card (q.inertia Γ) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun g ↦ (key g).symm.trans (inv_mem_iff (H := q.inertia Γ)))
  apply ht Ω y
  rw [hcard]
  have := congrArg jΩ.hom ((hq _).1 hc)
  simpa using this

theorem splitFibres_descend_of_tame_quotient : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] (φ : G.left ⟶ G'.left), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0) → IsGrpPullback G G' π φ → (∀ x : X, ∃ (k : Type) (_ : Field k) (_ : Algebra (X.residueField x) k), FiniteDimensional (X.residueField x) k ∧ Algebra.IsSeparable (X.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x)).obj G)) → (∀ x : X', ∃ (k : Type) (_ : Field k) (_ : Algebra (X'.residueField x) k), FiniteDimensional (X'.residueField x) k ∧ Algebra.IsSeparable (X'.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x) k)) ≫ X'.fromSpecResidueField x)).obj G')) := by
  intro Γ _ _ X X' ρ π G _ G' _ φ hq ht hφ hS x'
  obtain ⟨-, hsurj, -⟩ := quotient_isIntegral_surjective_orbits Γ X X' ρ π hq
  obtain ⟨_, hπ, hV⟩ := hq
  obtain ⟨x, rfl⟩ := π.surjective x'
  let := (π.residueFieldMap x).hom.toAlgebra
  obtain ⟨h₁, h₂⟩ := residueFieldMap_finite_separable_of_tame ρ π hπ
    (fun W _ s hs ↦ (hV W).2 s fun g _ ↦ (hs g).2) ht x
  obtain ⟨k, _, _, hfin, hsep, S, hGt⟩ := hS x
  let : Algebra (X'.residueField (π x)) k :=
    ((algebraMap (X.residueField x) k).comp (π.residueFieldMap x).hom).toAlgebra
  have : IsScalarTower (X'.residueField (π x)) (X.residueField x) k := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine ⟨k, inferInstance, inferInstance, Module.Finite.trans (X.residueField x) k,
    Algebra.IsSeparable.trans _ (X.residueField x) k, S, ?_⟩
  have key : (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x) ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField (π x)) k)) ≫ X'.fromSpecResidueField (π x) := by
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Spec.map_comp_assoc]
    rfl
  rw [← key]
  generalize Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x = t at hGt
  obtain ⟨e, he, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback G' π)
  have : IsMonHom ((Over.pullback t).mapIso e).hom := by
    rw [Functor.mapIso_hom]
    infer_instance
  have h₃ := isGt_of_iso ((Over.pullback t).mapIso e) hGt
  have : IsMonHom (pullCompIso t π G').symm.hom := inferInstanceAs (IsMonHom (pullCompIso t π G').inv)
  exact isGt_of_iso (pullCompIso t π G').symm h₃

end GlobalTheory
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.QuotTriple

open GlobalTheory.CechPic

theorem isPullback_lift {X X' : Scheme.{0}} {π : X ⟶ X'} {P Q : Over X} {P' Q' : Over X'} {a : P.left ⟶ P'.left}
    {b : Q.left ⟶ Q'.left} (ha : IsPullback a P.hom P'.hom π) (hb : IsPullback b Q.hom Q'.hom π) :
    IsPullback (lift (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q))).left (P ⊗ Q).hom (P' ⊗ Q').hom π := by
  have big : IsPullback ((snd P Q).left ≫ b) (fst P Q).left Q'.hom (P.hom ≫ π) :=
    (IsPullback.of_hasPullback P.hom Q.hom).flip.paste_horiz hb
  have e₁ : (lift (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q))).left ≫ (fst P' Q').left = (fst P Q).left ≫ a :=
    congrArg (fun z => z.left) (lift_fst (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q)))
  have e₂ : (lift (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q))).left ≫ (snd P' Q').left = (snd P Q).left ≫ b :=
    congrArg (fun z => z.left) (lift_snd (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q)))
  have h₁ : IsPullback (lift (pushPt ha.w (fst P Q)) (pushPt hb.w (snd P Q))).left (fst P Q).left
      (fst P' Q').left a := by
    refine IsPullback.of_right (h₁₂ := (snd P' Q').left) (v₁₃ := Q'.hom) (h₂₂ := P'.hom) ?_ e₁
      (IsPullback.of_hasPullback P'.hom Q'.hom).flip
    rw [e₂, ha.w]
    exact big
  exact h₁.paste_vert ha

section Cube

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem pull_cls_cube (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hc : pull φ (cls L hL) = cls L' hL') {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (T ⟶ G)) (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) :
    pull U.left (cls (cubeLB G x L) (LB.isLB_linComb hL _ _)) = cls (cubeLB G' x' L') (LB.isLB_linComb hL' _ _) := by
  refine (congrArg (pull U.left) (cls_linComb hL _ _ _)).trans (Eq.trans ?_ (cls_linComb hL' _ _ _).symm)
  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← hc, ← pull_comp]
  exact congrArg (fun q => _ • pull q (cls L hL)) (psum_push h x' x U hx I.down).symm

theorem psum_one {T : Over S} {n : ℕ} (I : Finset (Fin n)) : psum G (fun _ => (1 : T ⟶ G)) I = 1 := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => rfl
  | cons k l ih => exact (congrArg ((1 : T ⟶ G) * ·) ih).trans (_root_.mul_one _)

theorem one_left : (1 : 𝟙_ (Over S) ⟶ G).left = eSec G := by
  rw [Hom.one_def]; simp [eSec]

theorem pull_cls_cube_origin {L : LB G.left} (hL : L.IsLB) (h0 : pull (eSec G) (cls L hL) = 0) {T : Over S} {n : ℕ}
    (x : Fin n → (T ⟶ G)) (o : 𝟙_ (Over S) ⟶ T) (ho : ∀ i, o ≫ x i = 1) :
    pull o.left (cls (cubeLB G x L) (LB.isLB_linComb hL _ _)) = 0 := by
  refine (congrArg (pull o.left) (cls_linComb hL _ _ _)).trans ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun I _ => ?_
  have e : o ≫ psum G x I.down = 1 :=
    (psum_hom (preHom o) x I.down).trans ((congrArg (fun z => psum G z I.down) (funext ho)).trans (psum_one _))
  rw [map_zsmul, ← pull_comp, ← Over.comp_left, e, one_left, h0, smul_zero]

end Cube

section Quot

variable {Γ : Type} [Group Γ] [Finite Γ] {X X' : Scheme.{0}} {ρ : Γ →* Aut X} {π : X ⟶ X'}

theorem eq_zero_of_pull (hq : IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens,
      Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)),
        ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom)
    {P : Over X} {P' : Over X'} {Φ : P.left ⟶ P'.left} (hΦ : IsPullback Φ P.hom P'.hom π) (hs' : Smooth P'.hom)
    (hs : Smooth P.hom) (hg : GeometricallyIntegral P.hom) (hr : IsReduced X) (hab : genericPoints X ⊆ abLocus P)
    (o : 𝟙_ (Over X) ⟶ P) (o' : 𝟙_ (Over X') ⟶ P') (ho : o.left ≫ Φ = π ≫ o'.left) (c : Pic P'.left)
    (h₀ : pull o'.left c = 0) (h₁ : pull Φ c = 0) : c = 0 := by
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  exact (cls_eq_zero_iff hN).2 (exists_gen_of_quotient_of_rigid Γ X X' ρ π P P' Φ o.left o'.left N hq hΦ
    inferInstance (Over.w o) (Over.w o') ho
    (eq_one_of_appLE_section_eq_one X P o.left (Over.w o) hs hg ⟨hr, hab⟩) hN
    ((cls_eq_zero_iff (pull_isLB hN _)).1 h₀) ((cls_eq_zero_iff (pull_isLB hN _)).1 h₁))

theorem genericPoints_subset_image [Surjective π] : genericPoints X' ⊆ π '' genericPoints X := by
  intro y hy
  obtain ⟨x, rfl⟩ := π.surjective y
  let C : irreducibleComponents X := ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩
  have hs : (genericPoints.ofComponent C).1 ⤳ x :=
    (genericPoints.isGenericPoint_ofComponent C).specializes mem_irreducibleComponent
  exact ⟨_, (genericPoints.ofComponent C).2, eq_of_specializes_of_mem_genericPoints hy (hs.map π.continuous)⟩

end Quot

theorem exists_sab_of_quotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (t : SAB H X) (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (a' : OAct (𝓞 E) G') (φ : t.G.left ⟶ G'.left) (L' : LB G'.left), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsReduced X ∧ genericPoints X ⊆ abLocus t.G) → IsSemiAbelian G' → IsGrpPullback t.G G' π φ → (∀ x, (t.act.act x).left ≫ φ = φ ≫ (a'.act x).left) → L'.IsLB → LBIso t.PP.L (L'.pull φ) → ∃ (t' : SAB H X') (ν : SABMap t t' π) (e : t'.G ≅ G'), ν.φ ≫ e.hom.left = φ := by
  intro E _ _ _ H Γ _ _ X X' ρ π t G' _ _ a' φ L' hq ⟨hr, hab⟩ hG' gp hact hL' hiso
  obtain ⟨-, hsurj, -⟩ := quotient_isIntegral_surjective_orbits Γ X X' ρ π hq
  have hr' : IsReduced X' := ⟨fun V => isReduced_of_injective _ (hq.2.2 V).1⟩
  have hab' : genericPoints X' ⊆ abLocus G' := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := genericPoints_subset_image (π := π) hy
    exact (abLocus_pullback abLocusOne hG' gp.1 x).2 (hab hx)
  have he : eSec t.G ≫ φ = π ≫ eSec G' := (cubeMapOf gp).e_comm
  have hp : eSec G' ≫ G'.hom = 𝟙 X' := Over.w _
  have c₀ : pull (eSec t.G) (cls t.PP.L t.PP.isLB) = 0 :=
    (cls_eq_zero_iff (pull_isLB t.PP.isLB _)).2 ⟨_, t.PP.rigGen⟩
  have cl : cls t.PP.L t.PP.isLB = pull φ (cls L' hL') := (cls_eq_iff _ (pull_isLB hL' φ)).2 hiso
  obtain ⟨M, hM, cM⟩ := cls_surj (cls L' hL' - pull (G'.hom ≫ eSec G') (cls L' hL'))
  have m₀ : pull (eSec G') (cls M hM) = 0 := by
    have e : eSec G' ≫ G'.hom ≫ eSec G' = eSec G' :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ eSec G') hp).trans (Category.id_comp _))
    rw [cM, map_sub, ← pull_comp, e, sub_self]
  have m₁ : pull φ (cls M hM) = cls t.PP.L t.PP.isLB := by
    have e : φ ≫ G'.hom ≫ eSec G' = t.G.hom ≫ eSec t.G ≫ φ := by
      rw [he, ← Category.assoc, gp.1.w, Category.assoc]
    rw [cM, map_sub, ← pull_comp, e, pull_comp, pull_comp, ← cl, c₀, map_zero, sub_zero]
  obtain ⟨r, hrig⟩ := (cls_eq_zero_iff (pull_isLB hM (eSec G'))).1 m₀
  let PP : RigLB G' := ⟨M, r, hM, hrig⟩
  have a₁ := t.semi.smooth
  have := t.semi.geomConnected
  have b₁ := grpObj_geometricallyIntegral_of_smooth X t.G
  obtain ⟨a₂, b₂, c₂⟩ := smooth_geometricallyIntegral_abLocus_tensorObj X t.G t.G a₁ a₁ b₁ b₁
  have d₂ := (Set.subset_inter hab hab).trans c₂
  obtain ⟨a₃, b₃, c₃⟩ := smooth_geometricallyIntegral_abLocus_tensorObj X t.G _ a₁ a₂ b₁ b₂
  have d₃ := (Set.subset_inter hab d₂).trans c₃
  have a₁' := hG'.smooth
  have a₂' : Smooth (G' ⊗ G').hom := smooth_tensorObj_hom _ _
  have a₃' : Smooth (G' ⊗ G' ⊗ G').hom := smooth_tensorObj_hom _ _
  have p₂ := isPullback_lift gp.1 gp.1
  have p₃ := isPullback_lift gp.1 p₂
  have o₁ : (1 : 𝟙_ (Over X) ⟶ t.G).left ≫ φ = π ≫ (1 : 𝟙_ (Over X') ⟶ G').left := by
    rw [one_left, one_left]; exact he
  have pa : ∀ {T : Over X} (x : T ⟶ t.G) a, pushPt gp.1.w (x ≫ t.act.act a) = pushPt gp.1.w x ≫ a'.act a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have ol : ∀ {P Q : Over X} {P' Q' : Over X'} {a : P.left ⟶ P'.left} {b : Q.left ⟶ Q'.left}
      (wa : a ≫ P'.hom = P.hom ≫ π) (wb : b ≫ Q'.hom = Q.hom ≫ π) (u : 𝟙_ _ ⟶ P) (v : 𝟙_ _ ⟶ Q) (u' : 𝟙_ _ ⟶ P')
      (v' : 𝟙_ _ ⟶ Q'), u.left ≫ a = π ≫ u'.left → v.left ≫ b = π ≫ v'.left →
      (lift u v).left ≫ (lift (pushPt wa (fst P Q)) (pushPt wb (snd P Q))).left = π ≫ (lift u' v').left := by
    intro P Q P' Q' a b wa wb u v u' v' hu hv
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst P' Q').left = (_ ≫ _) ≫ (fst P' Q').left
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, ← hu]
      show _ ≫ (fst P Q).left ≫ a = _
      rw [← Category.assoc, ← Over.comp_left, lift_fst]
    · show (_ ≫ _) ≫ (snd P' Q').left = (_ ≫ _) ≫ (snd P' Q').left
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, ← hv]
      show _ ≫ (snd P Q).left ≫ b = _
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
  have o₂ := ol gp.1.w gp.1.w 1 1 1 1 o₁ o₁
  have o₃ := ol gp.1.w p₂.w 1 _ 1 _ o₁ o₂
  have aone : ∀ a, (1 : 𝟙_ (Over X') ⟶ G') ≫ a'.act a = 1 := fun a => by
    have := a'.hom a
    exact MonObj.one_comp _
  have hΘ : ∃ s : (Theta G' M).Gen, s.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 (eq_zero_of_pull hq p₃ a₃' a₃ b₃ hr d₃ _ _ o₃ _
      (pull_cls_cube_origin hM m₀ (x3 G') _ fun i => by fin_cases i <;> simp [x3])
      ((pull_cls_cube gp hM t.PP.isLB m₁ (x3 t.G) (x3 G') _ fun i => ?_).trans
        ((cls_eq_zero_iff _).2 ⟨_, t.cub.isGen⟩)))
    fin_cases i
    · simp [x3]
    · refine Eq.trans ?_ (congrArg (· ≫ fst G' G') (lift_snd _ _).symm |>.trans (Category.assoc _ _ _))
      refine Over.OverMorphism.ext ?_
      exact (Category.assoc _ _ _).trans ((congrArg (fun z => (snd t.G (t.G ⊗ t.G)).left ≫ z.left)
        (lift_fst (pushPt gp.1.w (fst t.G t.G)) (pushPt gp.1.w (snd t.G t.G)))).symm.trans (Category.assoc _ _ _).symm)
    · refine Eq.trans ?_ (congrArg (· ≫ snd G' G') (lift_snd _ _).symm |>.trans (Category.assoc _ _ _))
      refine Over.OverMorphism.ext ?_
      exact (Category.assoc _ _ _).trans ((congrArg (fun z => (snd t.G (t.G ⊗ t.G)).left ≫ z.left)
        (lift_snd (pushPt gp.1.w (fst t.G t.G)) (pushPt gp.1.w (snd t.G t.G)))).symm.trans (Category.assoc _ _ _).symm)
  have hsym : LBIso M (M.pull (GrpObj.inv (X := G')).left) := by
    have e₁ : φ ≫ (GrpObj.inv (X := G')).left = (GrpObj.inv (X := t.G)).left ≫ φ := by
      have e := congrArg (fun z => z.left) (map_inv (pushHom gp t.G) (𝟙 t.G))
      exact (congrArg (· ≫ (GrpObj.inv (X := G')).left) (Category.id_comp φ).symm).trans
        (e.symm.trans (congrArg (· ≫ φ) (Category.id_comp _)))
    have e₂ : (1 : 𝟙_ (Over X') ⟶ G') ≫ GrpObj.inv (X := G') = 1 := inv_one (G := 𝟙_ (Over X') ⟶ G')
    obtain ⟨-, w, hw, -⟩ := t.sym
    have e₃ : cls t.PP.L t.PP.isLB = pull (GrpObj.inv (X := t.G)).left (cls t.PP.L t.PP.isLB) :=
      (cls_eq_iff _ (pull_isLB t.PP.isLB _)).2 ⟨w, hw⟩
    refine (cls_eq_iff hM (pull_isLB hM _)).1 (sub_eq_zero.1 (eq_zero_of_pull hq gp.1 a₁' a₁ b₁ hr hab 1 1 o₁ _ ?_ ?_))
    · rw [map_sub, cls_pull hM, ← pull_comp, ← Over.comp_left, e₂, sub_self]
    · rw [map_sub, cls_pull hM, ← pull_comp, e₁, pull_comp, m₁, ← e₃, sub_self]
  have hadj : ∀ a, LBIso (cubeLB G' ![fst G' G' ≫ a'.act a, snd G' G'] M)
      (cubeLB G' ![fst G' G', snd G' G' ≫ a'.act (H.bar a)] M) := fun a => by
    refine (cls_eq_iff (LB.isLB_linComb hM _ _) (LB.isLB_linComb hM _ _)).1
      (sub_eq_zero.1 (eq_zero_of_pull hq p₂ a₂' a₂ b₂ hr d₂ _ _ o₂ _ ?_ ?_))
    · rw [map_sub, sub_eq_zero]
      exact (pull_cls_cube_origin hM m₀ _ _ fun i => by fin_cases i <;> simp [aone]).trans
        (pull_cls_cube_origin hM m₀ _ _ fun i => by fin_cases i <;> simp [aone]).symm
    · rw [map_sub, sub_eq_zero]
      refine (pull_cls_cube gp hM t.PP.isLB m₁ _ _ _ fun i => ?_).trans
        (((cls_eq_iff _ _).2 (t.adj a)).trans (pull_cls_cube gp hM t.PP.isLB m₁ _ _ _ fun i => ?_).symm)
      · fin_cases i
        · exact (pa _ a).trans (by simp)
        · simp
      · fin_cases i
        · simp
        · exact (pa _ _).trans (by simp)
  have hprim : LBIso M (cubeLB G' ![𝟙 G', a'.act H.w0] M) := by
    refine (cls_eq_iff hM (LB.isLB_linComb hM _ _)).1
      (sub_eq_zero.1 (eq_zero_of_pull hq gp.1 a₁' a₁ b₁ hr hab 1 1 o₁ _ ?_ ?_))
    · rw [map_sub, sub_eq_zero]
      exact (one_left (G := G') ▸ m₀).trans
        (pull_cls_cube_origin hM m₀ _ _ fun i => by fin_cases i <;> simp [aone]).symm
    · rw [map_sub, sub_eq_zero, m₁]
      refine ((cls_eq_iff _ (LB.isLB_linComb t.PP.isLB _ _)).2 t.prim).trans (Eq.trans
        (pull_cls_cube gp hM t.PP.isLB m₁ _ ![𝟙 G', a'.act H.w0] (pushPt gp.1.w (𝟙 t.G)) fun i => ?_).symm ?_)
      · fin_cases i
        · simp
        · exact (congrArg (pushPt gp.1.w) (Category.id_comp _).symm).trans (pa _ _)
      · exact congrArg (fun q => pull q _) (Category.id_comp φ)
  obtain ⟨k₁, k₂⟩ := CubeGen.cubical_and_symmetric X' G' PP hG' ⟨hr', hab'⟩
  obtain ⟨cub⟩ := k₁ hΘ
  let t' : SAB H X' := ⟨G', hG', a', PP, cub, k₂ hsym, hadj, hprim⟩
  obtain ⟨ν, hν⟩ := exists_sabMap_of_lbIso E H X' X t' t π φ ⟨hr, hab⟩ gp hact
    ((cls_eq_iff _ (pull_isLB hM φ)).1 m₁.symm)
  exact ⟨t', ν, Iso.refl _, (Category.comp_id _).trans hν⟩

end GlobalTheory.QuotTriple
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.exists_semiAbelianTriple_of_finiteQuotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (t : SAB H X) (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (a' : OAct (𝓞 E) G') (φ : t.G.left ⟶ G'.left) (L' : LB G'.left), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsReduced X ∧ genericPoints X ⊆ abLocus t.G) → IsSemiAbelian G' → IsGrpPullback t.G G' π φ → (∀ x, (t.act.act x).left ≫ φ = φ ≫ (a'.act x).left) → L'.IsLB → LBIso t.PP.L (L'.pull φ) → ∃ (t' : SAB H X') (ν : SABMap t t' π) (e : t'.G ≅ G'), ν.φ ≫ e.hom.left = φ := by
  first | exact @GlobalTheory.QuotTriple.exists_sab_of_quotient | exact GlobalTheory.QuotTriple.exists_sab_of_quotient | (intros; apply GlobalTheory.QuotTriple.exists_sab_of_quotient <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem fixes_iff_fixes_image {X Y T : Scheme.{0}} (p : Y ⟶ X) (r : X ⟶ X) (q : Y ⟶ Y) (y : T ⟶ Y)
    (w : q ≫ p = p ≫ r)
    (h : (y ≫ p) ≫ r = y ≫ p → pullback.fst p (y ≫ p) ≫ q = pullback.fst p (y ≫ p)) :
    y ≫ q = y ↔ (y ≫ p) ≫ r = y ≫ p := by
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [Category.assoc, ← w, ← Category.assoc, hy]
  · have := pullback.lift y (𝟙 _) (Category.id_comp _).symm ≫= h hy
    rwa [pullback.lift_fst_assoc, pullback.lift_fst] at this

theorem exists_sab_descent_of_tame_quotient :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (R : Type) [CommRing R] (X X' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (π : X ⟶ X') (t : SAB H X) (s : X ⟶ Sp R) (τ : Γ →* Aut t.G.left) (mu : ∀ g, SABMap t t (ρ g).hom), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsFinite π → IsQProjOver (t.G.hom ≫ s) → (IsReduced X ∧ genericPoints X ⊆ abLocus t.G) → (∀ g, (mu g).φ = (τ g).hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x → pullback.fst t.G.hom x ≫ (τ g).hom = pullback.fst t.G.hom x) → ∃ (t' : SAB H X') (ν : SABMap t t' π), (∀ g, (τ g).hom ≫ ν.φ = ν.φ) ∧ (Good t → PushInvertible t.G t.PP.L → Good t') := by
  intro E _ _ _ H Γ _ _ R _ X X' _ ρ π t s τ mu hQ hfin hqp hga hmu htame hfib
  have hsemi := t.semi
  have hcart (g : Γ) : IsGrpPullback t.G t.G (ρ g).hom (τ g).hom := hmu g ▸ (mu g).cart
  have hw (g : Γ) : (τ g).hom ≫ t.G.hom = t.G.hom ≫ (ρ g).hom := (hcart g).1.w
  have hact (g : Γ) (c) : (t.act.act c).left ≫ (τ g).hom = (τ g).hom ≫ (t.act.act c).left :=
    hmu g ▸ (mu g).act c
  have he (g : Γ) : eSec t.G ≫ (τ g).hom = (ρ g).hom ≫ eSec t.G := by
    have := (mu g).cm.e_comm
    rw [(mu g).base] at this
    rw [← hmu g]
    exact this
  have hL (g : Γ) : LBIso t.PP.L (t.PP.L.pull (τ g).hom) := by
    obtain ⟨w, hw, -⟩ := (mu g).lin
    rw [← hmu g]
    exact ⟨w, hw⟩
  have hsec : eSec t.G ≫ t.G.hom = 𝟙 X := Over.w (η[t.G])
  have hgi : GeometricallyIntegral t.G.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hsemi.smooth hsemi.geomConnected
  obtain ⟨-, hsurj, -⟩ := quotient_isIntegral_surjective_orbits Γ X X' ρ π hQ
  obtain ⟨G', φ, hpb, hsm, hinv⟩ :=
    exists_smooth_descent_of_tame_quotient Γ R X X' ρ π t.G s τ hQ hfin hqp hsemi.smooth hw htame hfib
  obtain ⟨_, _, a', hgp, ha⟩ := quotient_descend_grpObj Γ (𝓞 E) X X' ρ π t.G G' φ τ t.act hQ hpb inferInstance
    fun g => ⟨hinv g, hcart g, hact g⟩
  have hsemi' := (SemiAbelianDescent.main X X' π t.G G' φ inferInstance hsurj hgp hsm hsemi).1
  obtain ⟨u, hu₁, hu₂, hu₃⟩ := RigidLinearisation.exists_linearisation Γ X t.G (eSec t.G) ρ τ t.PP.L hsec hgi
    (eq_one_of_appLE_section_eq_one X t.G (eSec t.G) hsec hsemi.smooth hgi hga) (fun g => ⟨hw g, he g⟩) hfib
    t.PP.isLB ⟨t.PP.rig, t.PP.rigGen⟩ hL
  have hQ' := (quotient_flat_baseChange Γ X X' _ _ ρ π φ t.G.hom G'.hom hQ hpb inferInstance).2 τ
    fun g => ⟨hinv g, hw g⟩
  obtain ⟨L', hL', hiso⟩ := LinDescent.exists_descent_of_tame Γ _ _ τ φ t.PP.L hQ' (fun k _ _ y => by
    convert htame k (y ≫ t.G.hom) using 2
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g =>
      fixes_iff_fixes_image t.G.hom _ _ y (hw g) (hfib k _ g))) t.PP.isLB u hu₁ hu₂ hu₃
  obtain ⟨t', ν, e, hν⟩ := T.exists_semiAbelianTriple_of_finiteQuotient E H Γ X X' ρ π t G' a' φ L' hQ hga hsemi' hgp ha hL' hiso
  have hinv' (g : Γ) : (τ g).hom ≫ ν.φ = ν.φ := by
    rw [← cancel_mono e.hom.left, Category.assoc, hν, hinv]
  refine ⟨t', ν, hinv', fun ⟨h₁, h₂, _⟩ hP => ⟨?_, ?_, ?_⟩⟩
  · exact (SemiAbelianDescent.main X X' π t.G t'.G ν.φ inferInstance hsurj ν.cart t'.semi.smooth hsemi).2 h₁
  · exact splitFibres_descend_of_tame_quotient Γ X X' ρ π t.G t'.G ν.φ hQ htame ν.cart h₂
  · obtain ⟨w, hw', -⟩ := ν.lin
    have := t'.semi.smooth
    exact exists_secOn_nonvanishing_of_tame_quotient Γ X X' ρ π t.G t'.G ν.φ τ t.PP.L t'.PP.L hQ ν.cart.1
      inferInstance (fun g => ⟨hinv' g, hw g⟩) htame hfib t.PP.isLB t'.PP.isLB ⟨w, hw'⟩ hP

end GlobalTheory
end
