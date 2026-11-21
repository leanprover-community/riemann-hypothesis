import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasisOnAny
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LieFreeNearTwoPrimes

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoPrimeSection

open TopologicalSpace

section General

variable {X : Scheme.{0}} {L : LB X}

theorem exists_global [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) (a : Γ(X, ⊤)) {V : X.Opens}
    (hV : X.basicOpen a ≤ V) {θ : ∀ i, Γ(X, V ⊓ L.U i)} (hθ : θ ∈ secOn L V) {g : X} (hg : g ∈ X.basicOpen a)
    {i : L.ι} (hi : g ∈ X.basicOpen (θ i)) : ∃ u : L.Sec, g ∈ Out.nonzeroLocus u := by
  obtain ⟨n, t, ht⟩ := AbLaw.SecOn.exists_pow_smul_eq_restrict hL (V := ⊤) isCompact_univ
    isQuasiSeparated_univ a le_top rfl
    (AbLaw.SecOn.restrict L hV ((AbLaw.SecOn.equivFamilies _ _).symm ⟨θ, hθ⟩))
  have hi' : g ∈ V ⊓ L.U i := X.basicOpen_le _ hi
  have hm : (𝟙 X : X ⟶ X) g ∈ X.basicOpen a ⊓ L.U i := ⟨hg, hi'.2⟩
  refine ⟨AbLaw.SecOn.topEquiv _ t, (mem_nonzeroLocus _ _).2 ⟨i, hi'.2, ?_⟩⟩
  have q := congrArg (fun s => gs (𝟙 X) g _ (GlobalTheory.LB.coord s i)) ht
  have e : gs (𝟙 X) g (L.U i) ((AbLaw.SecOn.topEquiv _ t).f i) =
      gs (𝟙 X) g ⊤ a ^ n * gs (𝟙 X) g (V ⊓ L.U i) (θ i) := by
    refine (gs_res (𝟙 X) g _ hi'.2 _).trans ((gs_res (𝟙 X) g _ hm _).symm.trans (q.symm.trans
      ((gs_mul (𝟙 X) g _ hm _ _).trans (congrArg₂ (· * ·) ?_ (gs_res (𝟙 X) g _ hm _)))))
    exact (gs_res (𝟙 X) g _ hm _).trans ((LBGerm.gs_pow (𝟙 X) g _ hg _ _).trans
      (congrArg (· ^ n) (gs_res (𝟙 X) g _ hg _)))
  rw [e]
  exact (((LBGerm.isUnit_gs_iff (𝟙 X) g ⊤ trivial a).2 hg).pow n).mul
    ((LBGerm.isUnit_gs_iff (𝟙 X) g _ hi' _).2 hi)

def add (s t : L.Sec) : L.Sec :=
  ⟨fun i => s.f i + t.f i, fun i j => by rw [map_add, map_add, s.compat i j, t.compat i j, mul_add]⟩

theorem add_comm' (s t : L.Sec) : add s t = add t s := by
  unfold add
  simp only [add_comm (s.f _)]

theorem mem_nonzeroLocus_add {s t : L.Sec} {y : X} (hs : y ∈ Out.nonzeroLocus s) (ht : y ∉ Out.nonzeroLocus t) :
    y ∈ Out.nonzeroLocus (add s t) := by
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hs
  refine (mem_nonzeroLocus _ _).2 ⟨k, hk, ?_⟩
  have hn : ¬ IsUnit (gs (𝟙 X) y (L.U k) (t.f k)) := fun h => ht ((mem_nonzeroLocus _ _).2 ⟨k, hk, h⟩)
  have e : gs (𝟙 X) y (L.U k) ((add s t).f k) = gs (𝟙 X) y (L.U k) (s.f k) + gs (𝟙 X) y (L.U k) (t.f k) :=
    gs_add (𝟙 X) y _ hk _ _
  rw [e]
  by_contra h
  have h₁ := (IsLocalRing.mem_maximalIdeal _).2 h
  have h₂ := (IsLocalRing.mem_maximalIdeal _).2 hn
  have h₃ := Ideal.sub_mem _ h₁ h₂
  rw [add_sub_cancel_right] at h₃
  exact (IsLocalRing.mem_maximalIdeal _).1 h₃ u

end General

theorem exists_basicOpen_two {R : Type} [CommRing R] {U : Set (PrimeSpectrum R)} (hU : IsOpen U)
    {p q : PrimeSpectrum R} (hp : p ∈ U) (hq : q ∈ U) :
    ∃ r : R, r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∀ z : PrimeSpectrum R, r ∉ z.asIdeal → z ∈ U := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hU.isClosed_compl
  have key : ∀ z : PrimeSpectrum R, z ∈ U ↔ ¬ I ≤ z.asIdeal := fun z => by
    rw [← Set.notMem_compl_iff, hI]
    rfl
  have : ¬ (I : Set R) ⊆ p.asIdeal ∪ q.asIdeal := fun h =>
    (Ideal.subset_union.1 h).elim ((key p).1 hp) ((key q).1 hq)
  obtain ⟨r, hr, hn⟩ := Set.not_subset.1 this
  exact ⟨r, fun h => hn (Or.inl h), fun h => hn (Or.inr h), fun z hz => (key z).2 fun h => hz (h hr)⟩

theorem exists_sec_fibre (hL : Out.Laws) (hL₂ : Out.Laws2) {R : Type} [CommRing R] (Q : Out.PolAV (Sp R)) (p : Sp R) :
    ∃ th : Q.L.Sec, ∃ x : Q.A.left, Q.A.hom x = p ∧ x ∈ Out.nonzeroLocus th := by
  obtain ⟨V, hV, θ, hθ, -, nz⟩ := PushInv.pushInvertible_any hL₂.secBaseChangeAny hL.globalSectionsRank _ Q p
  obtain ⟨g, i, hg, hi⟩ := nz p hV
  obtain ⟨f, hf, hpf⟩ := (isAffineOpen_top (Sp R)).exists_basicOpen_le (V := V) ⟨p, hV⟩ trivial
  have := Q.isAb.proper
  have : CompactSpace Q.A.left := QuasiCompact.compactSpace_of_compactSpace Q.A.hom
  have : QuasiSeparatedSpace Q.A.left := quasiSeparatedSpace_of_quasiSeparated Q.A.hom
  have e := Scheme.preimage_basicOpen_top Q.A.hom f
  obtain ⟨u, hu⟩ := exists_global Q.isLB (Q.A.hom.appTop f) (e.ge.trans (Q.A.hom.preimage_mono hf)) hθ
    (g := g) (e.le (show Q.A.hom g ∈ (Sp R).basicOpen f from hg ▸ hpf)) hi
  exact ⟨u, g, hg, hu⟩

open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem main : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Q : Out.PolAV (Sp R)) (p q : PrimeSpectrum R), ∃ (th : Q.L.Sec) (r : R), r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∀ z : Sp R, r ∉ z.asIdeal → ∃ x : Q.A.left, Q.A.hom x = z ∧ x ∈ Out.nonzeroLocus th := by
  intro hL hL₂ R _ _ Q p q
  obtain ⟨th, hp, hq⟩ : ∃ th : Q.L.Sec, (∃ x : Q.A.left, Q.A.hom x = p ∧ x ∈ Out.nonzeroLocus th) ∧
      ∃ x : Q.A.left, Q.A.hom x = q ∧ x ∈ Out.nonzeroLocus th := by
    obtain ⟨s, x, hx, hs⟩ := exists_sec_fibre hL hL₂ Q p
    obtain ⟨t, y, hy, ht⟩ := exists_sec_fibre hL hL₂ Q q
    by_cases h₁ : y ∈ Out.nonzeroLocus s
    · exact ⟨s, ⟨x, hx, hs⟩, y, hy, h₁⟩
    by_cases h₂ : x ∈ Out.nonzeroLocus t
    · exact ⟨t, ⟨x, hx, h₂⟩, y, hy, ht⟩
    exact ⟨add s t, ⟨x, hx, mem_nonzeroLocus_add hs h₂⟩, y, hy, add_comm' t s ▸ mem_nonzeroLocus_add ht h₁⟩
  have := Q.isAb.smooth
  obtain ⟨x, hx, hx'⟩ := hp
  obtain ⟨y, hy, hy'⟩ := hq
  obtain ⟨r, h₁, h₂, h₃⟩ := exists_basicOpen_two (R := R) (p := p) (q := q)
    (Q.A.hom.isOpenMap _ (Out.nonzeroLocus th).isOpen) ⟨x, hx', hx⟩ ⟨y, hy', hy⟩
  refine ⟨th, r, h₁, h₂, fun z hz => ?_⟩
  obtain ⟨w, hw, e⟩ := h₃ z hz
  exact ⟨w, e, hw⟩

end GlobalTheory.TwoPrimeSection
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalPolarization_section_nonzero_near_two_primes : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Q : Out.PolAV (Sp R)) (p q : PrimeSpectrum R), ∃ (th : Q.L.Sec) (r : R), r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∀ z : Sp R, r ∉ z.asIdeal → ∃ x : Q.A.left, Q.A.hom x = z ∧ x ∈ Out.nonzeroLocus th := by
  atlas_forward_decl GlobalTheory.TwoPrimeSection.main
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieBasis_away_avoiding_two_primes : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ), SmoothOfRelativeDimension n G.hom → ∀ p q : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∃ v : Fin n → (epsR (Localization.Away r) ⟶ (Over.pullback (spMap (algebraMap R (Localization.Away r)))).obj G), IsLieBasis v := by
  first | exact @GlobalTheory.LieTwo.lie_free_near_two_primes | exact GlobalTheory.LieTwo.lie_free_near_two_primes | (intros; apply GlobalTheory.LieTwo.lie_free_near_two_primes <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem exists_keyIn_polPB {R R₁ R' : Type} [CommRing R] [CommRing R₁] [CommRing R'] (Q : Out.PolAV (Sp R))
    (hg : 1 ≤ Q.g) (f₁ : R →+* R₁) (g : R₁ →+* R') (f : R →+* R') (hf : g.comp f₁ = f) (th : Q.L.Sec)
    (hth : ∀ s : Sp R', ∃ x : Q.A.left, Q.A.hom x = spMap f s ∧ x ∈ Out.nonzeroLocus th)
    (v : Fin Q.g → (epsR R₁ ⟶ (Over.pullback (spMap f₁)).obj Q.A)) (hv : IsLieBasis v) :
    ∃ (y : KeyIn R') (φ : y.P.A.left ⟶ Q.A.left), PolPB y.P Q (spMap f) φ := by
  have h := isGrpPullback_pullback Q.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj Q.A).left ⟶ Q.A.left := pullback.fst Q.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := pull_isLB Q.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R') :=
    { A := (Over.pullback (spMap f)).obj Q.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) Q.A Q.isAb
      g := Q.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 Q.smoothDim
      L := Q.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h Q.rigid
      sym := PolBaseChange.sym_pull h Q.sym
      ample := relAmple_pull h.1 Q.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) Q.ample
      ktriv := kTriv_pull h Q.isLB hL' hw Q.ktriv }
  obtain ⟨rig, hr⟩ := P'.rigid
  obtain ⟨th', hth'⟩ := sec_pull_down hw Q.isLB hL' th
  have h₁ := isGrpPullback_pullback Q.A (spMap f₁)
  have hA₁ := Out.TLinPf.isAb_pullback (spMap f₁) Q.A Q.isAb
  have c₁ := hA₁.comm
  have c₂ : IsCommMonObj P'.A := P'.isAb.comm
  have e : spMap g ≫ spMap f₁ = spMap f := by
    rw [← hf, ← Spec.map_comp]; rfl
  have w : φ ≫ Q.A.hom = P'.A.hom ≫ spMap g ≫ spMap f₁ := by rw [e]; exact h.1.w
  have w₁ : φ ≫ Q.A.hom = (P'.A.hom ≫ spMap g) ≫ spMap f₁ := by rw [Category.assoc]; exact w
  have h₂ : IsGrpPullback P'.A _ (spMap g) (h₁.1.lift _ _ w₁) :=
    IsGrpPullback.cancel h₁ (h.congr e.symm (h₁.1.lift_fst _ _ w₁).symm) (h₁.1.lift_snd _ _ w₁)
  obtain ⟨v', hb', -⟩ := exists_isLieBasis_baseChange R₁ R' g _ P'.A _ h₂ hA₁.smooth Q.g v hv
  refine ⟨⟨P', hg, rig, hr, th', fun s => ?_, v', hb'⟩, φ, h, rfl, ⟨idIso _, idIso_isGen hL'⟩⟩
  obtain ⟨z, hz, hz'⟩ := hth s
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
  refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
  have u₁ : IsUnit (gs φ y _ (th.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
  have e := hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
  rw [Category.id_comp] at e
  exact isUnit_of_mul_isUnit_right (e ▸ u₁)

theorem exists_keyIn_near_two : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Q : Out.PolAV (Sp R)) (p q : PrimeSpectrum R), 1 ≤ Q.g → ∃ r : R, r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∃ (y : KeyIn (Localization.Away r)) (φ : y.P.A.left ⟶ Q.A.left), PolPB y.P Q (spMap (algebraMap R (Localization.Away r))) φ := by
  intro hL hL₂ R _ _ Q p q hg
  obtain ⟨th, a, ap, aq, ha⟩ := GlobalTheory.T.exists_principalPolarization_section_nonzero_near_two_primes hL hL₂ R Q p q
  have c : IsCommMonObj Q.A := Q.isAb.comm
  obtain ⟨b, bp, bq, v, hv⟩ := GlobalTheory.T.exists_lieBasis_away_avoiding_two_primes R Q.A Q.g Q.smoothDim p q
  refine ⟨b * a, fun h => (p.isPrime.mem_or_mem h).elim bp ap, fun h => (q.isPrime.mem_or_mem h).elim bq aq, ?_⟩
  refine exists_keyIn_polPB Q hg (algebraMap R (Localization.Away b))
    (IsLocalization.Away.awayToAwayRight (S := Localization.Away b) (P := Localization.Away (b * a)) b a) _
    (RingHom.ext fun x => IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away b) b a x) th
    (fun s => ha _ fun h => ?_) v hv
  have h' : algebraMap R (Localization.Away (b * a)) a ∈ s.asIdeal := h
  have u : IsUnit (algebraMap R (Localization.Away (b * a)) (b * a)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at u
  exact s.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (isUnit_of_mul_isUnit_right u))

end GlobalTheory.KeyFam
end
end
