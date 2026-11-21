import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafPtWPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.SecondDegreeKilling

def LeafHrelZero : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E), Eqv R f F →
  ∀ n, Subsingleton (Hrel R f F n)

def LeafClosedLift : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {B W : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι]
  (s : Sp A ⟶ B), (∃ x, s.base x ∈ Set.range ι.base) →
  ∃ w : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ W, w ≫ ι = Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s

def ProperBaseChangeClosedFiberStrictlyHenselianEquivalence : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (A : Type) [CommRing A] [IsLocalRing A] (s : Sp A ⟶ B), SH A →
  ∀ w : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ W,
    w ≫ ι = Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s →
  Eqv (ZMod q) (sch.map (prS p ι s)) (tw q i)

theorem LeafPtW_of (hZ : LeafHrelZero) (hL : LeafClosedLift) (hE : ProperBaseChangeClosedFiberStrictlyHenselianEquivalence) : LateralTheory.E.SecondDegreeKilling.LeafPtW := by
  intro hH q _ k _ hq i B W Y toK ι _ V hV p hp A _ s hA hs m
  obtain ⟨hh, _⟩ := hA
  have hx : ∃ x, s.base x ∈ Set.range ι.base := by
    by_contra hc
    push Not at hc
    apply hs
    rintro _ ⟨x, rfl⟩
    have : s.base x ∈ (V : Set B) := by
      rw [hV]; exact hc x
    exact this
  obtain ⟨w, hw⟩ := hL A ι s hx
  exact hZ (ZMod q) (tw q i) (sch.map (prS p ι s)) (hE hH q k hq i toK ι p hp A s ⟨hh, ‹_›⟩ w hw) m

end LateralTheory.E.LeafPtWPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafPtWPf

theorem closedLift : LeafClosedLift := by
  intro A _ _ B W ι _ s hx
  set t := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s with ht
  have hcl : IsClosed (s.base ⁻¹' Set.range ι.base) :=
    (ι.isClosedEmbedding.isClosed_range).preimage s.continuous
  obtain ⟨x, hx⟩ := hx
  have hc : s.base (IsLocalRing.closedPoint A) ∈ Set.range ι.base :=
    (IsLocalRing.specializes_closedPoint (R := A) x).mem_closed hcl hx
  have : Surjective (pullback.fst t ι) := by
    constructor
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]
    intro y
    simp only [Set.mem_preimage]
    have hy : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))).base y = IsLocalRing.closedPoint A := by
      have : y = IsLocalRing.closedPoint (IsLocalRing.ResidueField A) := Subsingleton.elim _ _
      subst this
      exact IsLocalRing.comap_closedPoint (IsLocalRing.residue A)
    rw [ht, Scheme.Hom.comp_base, TopCat.comp_app, hy]
    exact hc
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.fst t ι)
  refine ⟨inv (pullback.fst t ι) ≫ pullback.snd t ι, ?_⟩
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

end LateralTheory.E.LeafPtWPf
end
end
