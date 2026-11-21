import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogTarget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogenyTargetOfPointPairFieldExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgClosedEmbeddingsOfFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePIsogenyTargetsAtCharPPointStatement

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem finite_dvr_limits_of_finite_snd : ∀ (X Y₀ S : Scheme.{0}) (q : X ⟶ S) (U : X.Opens) (s₀ t₀ : Y₀ ⟶ X)
    (gt : Y₀ ⟶ U.toScheme), IsSeparated q → IsAffine S → s₀ ≫ q = t₀ ≫ q → gt ≫ U.ι = t₀ → IsFinite gt →
    ∀ z : X, z ∈ U → {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀),
      spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧
      y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  intro X Y₀ S q U s₀ t₀ gt hq hS _ hgt hfin z hz
  refine ((gt.finite_preimage_singleton ⟨z, hz⟩).image s₀).subset ?_
  rintro u ⟨V, K, _, _, _, _, _, _, y', z', x, h1, h2, rfl, rfl⟩

  have hr : Set.range z' ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint w).map z'.continuous).mem_open U.isOpen hz
  set z'' := IsOpenImmersion.lift U.ι z' hr with hz''
  have hfac : z'' ≫ U.ι = z' := IsOpenImmersion.lift_fac _ _ _

  have hsq : x ≫ gt = spMap (algebraMap V K) ≫ z'' := by
    rw [← cancel_mono U.ι, Category.assoc, hgt, Category.assoc, hfac, h2]
  have hE : ValuativeCriterion.Existence gt :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed gt) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) gt).1
  obtain ⟨l, hl1, hl2⟩ := (hE { R := V, K := K, i₁ := x, i₂ := z'', commSq := ⟨hsq⟩ }).exists_lift
  dsimp only at hl1 hl2

  have hU := IsSeparated.valuativeCriterion (q ≫ terminal.from S)
  have hsq' : (x ≫ s₀) ≫ (q ≫ terminal.from S) = spMap (algebraMap V K) ≫ terminal.from _ :=
    terminal.hom_ext _ _
  have hy : y' = l ≫ s₀ := by
    have := hU { R := V, K := K, i₁ := x ≫ s₀, i₂ := terminal.from _, commSq := ⟨hsq'⟩ }
    have e := this.elim ⟨y', h1, terminal.hom_ext _ _⟩
      ⟨l ≫ s₀, by change spMap (algebraMap V K) ≫ l ≫ s₀ = x ≫ s₀; rw [← Category.assoc, hl1], terminal.hom_ext _ _⟩
    exact congrArg CommSq.LiftStruct.l e
  refine ⟨l (IsLocalRing.closedPoint V), ?_, ?_⟩
  · show gt (l _) = _
    apply Subtype.ext
    change (l ≫ gt ≫ U.ι) _ = z' _
    rw [← Category.assoc, hl2, hfac]
  · rw [hy]; rfl

end GlobalTheory.UPel.HT.ES
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dvr_limits_correspondence_finite_snd : ∀ (X Y₀ S : Scheme.{0}) (q : X ⟶ S) (U : X.Opens) (s₀ t₀ : Y₀ ⟶ X) (gt : Y₀ ⟶ U.toScheme), IsSeparated q → IsAffine S → s₀ ≫ q = t₀ ≫ q → gt ≫ U.ι = t₀ → IsFinite gt → ∀ z : X, z ∈ U → {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.finite_dvr_limits_of_finite_snd) | (exact GlobalTheory.UPel.HT.ES.finite_dvr_limits_of_finite_snd) | (intros; apply GlobalTheory.UPel.HT.ES.finite_dvr_limits_of_finite_snd  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.ClosedPtIsog

theorem charP_of_notMem_basicOpen {X : Scheme.{0}} {k : Type} [Field k] {p : ℕ} (hp : p.Prime) (h : Sp k ⟶ X)
    (hz : h (IsLocalRing.closedPoint k) ∉ X.basicOpen ((p : ℕ) : Γ(X, ⊤))) : CharP k p := by
  refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
  by_contra hne
  apply hz
  have hu : IsUnit ((p : ℕ) : Γ(Sp k, h ⁻¹ᵁ ⊤)) := by
    have := (IsUnit.mk0 _ hne).map
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Sp k).presheaf.map (homOfLE (le_top (a := h ⁻¹ᵁ ⊤))).op).hom)
    rwa [map_natCast] at this
  have hm : IsLocalRing.closedPoint k ∈ h ⁻¹ᵁ X.basicOpen ((p : ℕ) : Γ(X, ⊤)) := by
    rw [Scheme.preimage_basicOpen, map_natCast, Scheme.basicOpen_of_isUnit _ hu]
    trivial
  exact hm

theorem exists_isPIsog_closedPoint : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (c : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → IsPIsog c o₀ o₀' ψ₀ → ∀ z : M.X, z ∉ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)) → {u : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z} ⊆ {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u} := by
  intro p _ D R _ _ _ _ b N hN hNp _ c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ z hz u hu
  obtain ⟨V, K, _, _, _, _, _, _, y', z', x, hy, hz', hyu, hzz⟩ := hu
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing V K
  have hyz : y' ≫ M.s = z' ≫ M.s :=
    GlobalTheory.ExtUnique.hom_ext_of_dominant (Spec.map (CommRingCat.ofHom (Int.castRingHom R))) (specZIsTerminal.hom_ext _ _)
      (spMap (algebraMap V K)) (by rw [reassoc_of% hy, reassoc_of% hz', hst])
  have pull : ∀ {S S' : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (f : S' ⟶ S) (σ : S' ⟶ Sp R), f ≫ s = σ →
      ∃ o₁ : Obj b N σ, Nonempty (ObjMap o₁ o f) := by
    rintro S S' s o f σ rfl
    exact GlobalTheory.HTPull.exists_objMap_pull p D R b N S S' s f o
  obtain ⟨oV, ⟨mV⟩⟩ := pull M.univ y' (z' ≫ M.s) hyz
  obtain ⟨oV', ⟨mV'⟩⟩ := pull M.univ z' (z' ≫ M.s) rfl
  obtain ⟨oK, ⟨nK⟩⟩ := pull o₀ x _ rfl
  obtain ⟨oK', ⟨nK'⟩⟩ := pull o₀' x _ rfl
  obtain ⟨ψK, hψK, -⟩ := ValExt.isPIsog_pull p D R b N c _ _ _ _ x o₀ o₀' oK oK' nK nK' ψ₀ hψ
  have m₁ : ObjMap oK M.univ (spMap (algebraMap V K) ≫ y') := hy ▸ GlobalTheory.UPel.HT.ObjMap.comp nK ms₀
  have m₁' : ObjMap oK' M.univ (spMap (algebraMap V K) ≫ z') := hz' ▸ GlobalTheory.UPel.HT.ObjMap.comp nK' mt₀
  obtain ⟨n₁, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ m₁ mV
  obtain ⟨n₁', -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ m₁' mV'
  obtain ⟨e, he⟩ := hψ.exists_eq_pow
  have hdom : IsDominant (spMap (algebraMap V K)) := inferInstance
  obtain ⟨ψV, hψV, -⟩ := PIsogExt.exists_isPIsog_extend p D R b N hN hNp 0 c
    ⟨e, he, fun h => absurd h (lt_irrefl 0)⟩ _ _ (spMap (algebraMap V K)) _ (z' ≫ M.s)
    (GlobalTheory.isOpenImmersion_spMap_of_isDiscreteValuationRing V K) hdom inferInstance
    (fun y => (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_Sp V y).2)
    (fun y => (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_Sp V y).1) oV oV' oK oK' n₁ n₁' ψK hψK
  let k := AlgebraicClosure (IsLocalRing.ResidueField V)
  let φ : V →+* k := (algebraMap (IsLocalRing.ResidueField V) k).comp (IsLocalRing.residue V)
  let g : Sp k ⟶ Sp V := spMap φ
  have hg : g (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint φ
  have hζ : (g ≫ z') (IsLocalRing.closedPoint k) = z :=
    (Scheme.Hom.comp_apply g z' _).trans ((congrArg z' hg).trans hzz)
  have hυ : (g ≫ y') (IsLocalRing.closedPoint k) = u :=
    (Scheme.Hom.comp_apply g y' _).trans ((congrArg y' hg).trans hyu)
  obtain ⟨ou, ⟨nu⟩⟩ := pull oV g ((g ≫ z') ≫ M.s) (Category.assoc _ _ _).symm
  obtain ⟨oz, ⟨nz⟩⟩ := pull oV' g ((g ≫ z') ≫ M.s) (Category.assoc _ _ _).symm
  obtain ⟨ψk, hψk, -⟩ := ValExt.isPIsog_pull p D R b N c _ _ _ _ g oV oV' ou oz nu nz ψV hψV
  exact ⟨k, inferInstance, inferInstance, charP_of_notMem_basicOpen Fact.out (g ≫ z') (hζ ▸ hz), g ≫ z', g ≫ y', ou, oz,
    GlobalTheory.UPel.HT.ObjMap.comp nu mV, GlobalTheory.UPel.HT.ObjMap.comp nz mV', ψk,
    by rw [Category.assoc, Category.assoc, hyz], hψk, hζ, hυ⟩

end GlobalTheory.UPel.HT.ES.ClosedPtIsog
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pIsogeny_at_closedPoint_of_dvr_limit : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (c : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → IsPIsog c o₀ o₀' ψ₀ → ∀ z : M.X, z ∉ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)) → {u : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z} ⊆ {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u} := by
  first | (exact @GlobalTheory.UPel.HT.ES.ClosedPtIsog.exists_isPIsog_closedPoint) | (exact GlobalTheory.UPel.HT.ES.ClosedPtIsog.exists_isPIsog_closedPoint) | (intros; apply GlobalTheory.UPel.HT.ES.ClosedPtIsog.exists_isPIsog_closedPoint  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.UPel.HT.ES.SourceFin

open GlobalTheory.UPel.HT.ESDual GlobalTheory.UPel.HT.ES.CorrQF

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

def scaleMap {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S}
    (m : ObjMap o' o f) (e : ℕ) : ObjMap (scale o' e rfl) (scale o e rfl) f where
  φ := m.φ
  φ₂ := m.φ₂
  cart := m.cart
  sq := m.sq
  act := m.act
  pol := m.pol
  eta y := m.eta _

theorem exists_scale_mono (hN : 0 < N) (hp : N.Coprime p) (M : Model b N) (e : ℕ) :
    ∃ τ : M.X ⟶ M.X, Mono τ ∧ τ ≫ M.s = M.s ∧ Nonempty (ObjMap (scale M.univ e rfl) M.univ τ) := by
  obtain ⟨f, hf⟩ := exists_inv_exp hN hp e
  obtain ⟨τ, ⟨hτ, ⟨m⟩⟩, -⟩ := M.rep _ _ (scale M.univ e rfl)
  obtain ⟨τ', ⟨hτ', ⟨m'⟩⟩, -⟩ := M.rep _ _ (scale M.univ f rfl)
  have n : ObjMap (scale (scale M.univ e rfl) f rfl) M.univ (𝟙 M.X) :=
    { φ := (idMap M.univ).φ
      φ₂ := (idMap M.univ).φ₂
      cart := (idMap M.univ).cart
      sq := (idMap M.univ).sq
      act := (idMap M.univ).act
      pol := (idMap M.univ).pol
      eta := fun y => by
        have h : (scale (scale M.univ e rfl) f rfl).eta y = M.univ.eta y := by
          show M.univ.eta (p ^ e • p ^ f • y) = _
          rw [smul_smul, ← pow_add, eta_congr M.univ hf (pow_pos (Fact.out : p.Prime).pos _)]
        rw [h]
        exact (idMap M.univ).eta y }
  have h1 : τ ≫ τ' = 𝟙 M.X :=
    (M.rep _ _ (scale (scale M.univ e rfl) f rfl)).unique
      ⟨by rw [Category.assoc, hτ', hτ], ⟨compMap (scaleMap m f) m'⟩⟩ ⟨Category.id_comp _, ⟨n⟩⟩
  exact ⟨τ, mono_of_mono_fac h1, hτ, ⟨m⟩⟩

theorem exists_isPIsog_scale {S : Scheme.{0}} {s : S ⟶ Sp R} {e : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (hψ : IsPIsog (p ^ e) o o' ψ) : ∃ ψ' : o'.A ⟶ (scale o e rfl).A, IsPIsog (p ^ e) o' (scale o e rfl) ψ' := by
  obtain ⟨ψ', hm, h₁, h₂⟩ := hψ.2.2.2.2.2
  obtain ⟨a, l, P⟩ := dual_clauses hψ h₁ h₂
  exact ⟨ψ', ⟨e, rfl⟩, hm, a, l, P, ψ, hψ.2.1, h₂, h₁⟩

theorem not_mem_basicOpen {X : Scheme.{0}} (z : X) {k : Type} [Field k] [CharP k p]
    (h : X.residueField z →+* k) : z ∉ X.basicOpen ((p : ℕ) : Γ(X, ⊤)) := by
  rw [Scheme.mem_basicOpen_top, map_natCast]
  intro hu
  have := hu.map (h.comp (X.residue z).hom)
  rw [map_natCast, CharP.cast_eq_zero] at this
  exact not_isUnit_zero this

theorem exists_residueField_hom {X : Scheme.{0}} {k : Type} [Field k] (ζ : Sp k ⟶ X) {z : X}
    (hz : ζ (IsLocalRing.closedPoint k) = z) :
    ∃ h : X.residueField z →+* k, spMap h ≫ X.fromSpecResidueField z = ζ := by
  subst hz
  exact ⟨(X.descResidueField (Scheme.stalkClosedPointTo ζ)).hom,
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X ζ⟩

theorem finite_isogSource : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (c : ℕ), D.m = 1 → ∀ (M : Model b N) (z : M.X), {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u}.Finite := by
  intro p _ D R _ _ _ _ b N hN hNp _ c hm M z
  set Z := {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u} with hZ
  rcases Z.eq_empty_or_nonempty with h0 | ⟨u₀, k₀, _, _, _, ζ₀, _, _, _, -, -, _, -, hψ₀, hz₀, -⟩
  · rw [h0]; exact Set.finite_empty
  obtain ⟨e, rfl⟩ := hψ₀.1
  obtain ⟨h₀, -⟩ := exists_residueField_hom ζ₀ hz₀
  have hz := not_mem_basicOpen (p := p) z h₀
  obtain ⟨τ, hmono, hτ, ⟨mτ⟩⟩ := exists_scale_mono (by omega) hNp M e
  have key : ∀ u : Z, ∃ (k : Type) (_ : Field k) (σ : M.X.residueField z →+* k) (υ : Sp k ⟶ M.X),
      (∀ q, υ q = u.1) ∧ IsogTarget M (p ^ e) (spMap σ ≫ M.X.fromSpecResidueField z) (υ ≫ τ) := by
    rintro ⟨u, k, _, _, _, ζ, υ, ou, oz, mu, mz, ψ, hs, hψ, hζ, hu⟩
    obtain ⟨σ, hσ⟩ := exists_residueField_hom ζ hζ
    obtain ⟨ψ', hψ'⟩ := exists_isPIsog_scale hψ
    refine ⟨k, inferInstance, σ, υ, fun q => ?_, ?_⟩
    · rw [Subsingleton.elim q (IsLocalRing.closedPoint k)]
      exact hu
    · rw [hσ]
      exact ⟨by rw [Category.assoc, hτ, hs], oz, scale ou e rfl, ψ', ⟨mz⟩, ⟨compMap (scaleMap mu e) mτ⟩, hψ'⟩
  choose k hk σ υ hυ hT using key
  obtain ⟨L, _, _, g, h, hg⟩ := GlobalTheory.T.exists_isAlgClosed_compatible_embeddings_of_family (M.X.residueField z) Z k σ
  have hfin := (GlobalTheory.T.finite_pIsogenyTargets_at_charP_point p D R b N hN hNp hm (p ^ e) M z hz L h).preimage
    (f := fun υ' : Sp L ⟶ M.X => υ' ≫ τ) (fun x _ y _ hxy => (cancel_mono τ).1 hxy)
  refine (Set.Finite.biUnion hfin fun υ' _ => Set.finite_range (fun q : Sp L => υ' q)).subset ?_
  intro u hu
  have h1 := isogTarget_spMap p D R b N M (p ^ e) (k ⟨u, hu⟩) L (g ⟨u, hu⟩) _ _ (hT ⟨u, hu⟩)
  have e1 : spMap (g ⟨u, hu⟩) ≫ spMap (σ ⟨u, hu⟩) ≫ M.X.fromSpecResidueField z =
      spMap h ≫ M.X.fromSpecResidueField z := by
    rw [← Category.assoc, ← hg ⟨u, hu⟩]
    simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  rw [e1, ← Category.assoc] at h1
  simp only [Set.mem_iUnion, Set.mem_range]
  refine ⟨spMap (g ⟨u, hu⟩) ≫ υ ⟨u, hu⟩, h1, Classical.arbitrary _, ?_⟩
  rw [Scheme.Hom.comp_apply, hυ ⟨u, hu⟩ _]

end GlobalTheory.UPel.HT.ES.SourceFin
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_pIsogenySources_at_charP_point : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (c : ℕ), D.m = 1 → ∀ (M : Model b N) (z : M.X), {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.SourceFin.finite_isogSource) | (exact GlobalTheory.UPel.HT.ES.SourceFin.finite_isogSource) | (intros; apply GlobalTheory.UPel.HT.ES.SourceFin.finite_isogSource <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem GlobalTheory.UPel.HT.ES.finite_dvrPartners_snd : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ z : M.X, {u : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  intro p _ D R _ _ _ _ b N hN hNp hpR r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt _ _ hgtf _ hψ _ z
  by_cases hz : z ∈ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))
  · exact GlobalTheory.T.finite_dvr_limits_correspondence_finite_snd M.X Y₀ (Sp R) M.s _ s₀ t₀ gt (GlobalTheory.ZM.isSeparated_of_isQProjOver M.qproj) inferInstance hst hgt
      hgtf z hz
  · exact (GlobalTheory.T.finite_pIsogenySources_at_charP_point p D R b N hN hNp hpR c hm M z).subset
      (GlobalTheory.T.exists_pIsogeny_at_closedPoint_of_dvr_limit p D R b N hN hNp hpR c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ z hz)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_points_closure_genericCorrespondence_snd : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ z : M.X, {u : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.finite_dvrPartners_snd) | (exact GlobalTheory.UPel.HT.ES.finite_dvrPartners_snd) | (intros; apply GlobalTheory.UPel.HT.ES.finite_dvrPartners_snd <;> assumption)
end
