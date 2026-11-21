import Development.EtaleCohomology.EtaleSheaves.LineHigh

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.LineZeroCut

def LZNonempty : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)),
  UniversallyClosed p → Nonempty X → Nonempty ↑(pullback p (cpt A))

def LZDescend : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z L : Scheme.{0}} (u : Z ⟶ L) (l : L ⟶ Spec (CommRingCat.of A)),
  IsIntegralHom u → IsProper l → ¬ PreconnectedSpace ↑(pullback (u ≫ l) (cpt A)) →
  ∃ (Y : Scheme.{0}) (v : Z ⟶ Y) (r : Y ⟶ Spec (CommRingCat.of A)),
    IsProper r ∧ Surjective v ∧ v ≫ r = u ≫ l ∧ ¬ PreconnectedSpace ↑(pullback r (cpt A))

def LZProper : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] {X : Scheme.{0}}
  (r : X ⟶ Spec (CommRingCat.of A)), IsProper r → ConnectedSpace X → PreconnectedSpace ↑(pullback r (cpt A))

theorem lzNonempty : LZNonempty := by
  intro A _ _ X p hp hX
  obtain ⟨x⟩ := hX
  have hc : IsClosed (Set.range p.base) := p.isClosedMap.isClosed_range
  have h1 : IsLocalRing.closedPoint A ∈ Set.range p.base := by
    have : IsLocalRing.closedPoint A ∈ closure {p.base x} :=
      (PrimeSpectrum.le_iff_mem_closure _ _).1 (IsLocalRing.le_maximalIdeal (p.base x).isPrime.ne_top)
    exact closure_minimal (by simp) hc this
  obtain ⟨z, hz⟩ := h1
  have h2 : (cpt A) (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) = IsLocalRing.closedPoint A :=
    have : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (IsLocalRing.residue A))) :=
      (inferInstance : IsLocalHom (IsLocalRing.residue A))
    Spec_closedPoint
  obtain ⟨w, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := cpt A) z
    (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) (by rw [hz, h2])
  exact ⟨w⟩

theorem goal_of (h2 : LZDescend) (h3 : LZProper) : LateralTheory.E.t_E2Cut.LineZero := by
  intro A _ _ hSH Z p hIL hZ
  obtain ⟨hH, -⟩ := hSH
  obtain ⟨L, u, l, hu, hl, rfl⟩ := hIL
  have := hl.1
  have := hZ.1
  have hne : Nonempty ↑(pullback (u ≫ l) (cpt A)) := lzNonempty A (u ≫ l) inferInstance inferInstance
  have hpre : PreconnectedSpace ↑(pullback (u ≫ l) (cpt A)) := by
    by_contra hn
    obtain ⟨Y, v, r, hr, hv, -, hY⟩ := h2 A u l hu hl.1 hn
    have hZc : ConnectedSpace Z := inferInstance
    have hYc : ConnectedSpace Y := hv.surj.connectedSpace v.continuous
    exact hY (h3 A r hr hYc)
  exact { toPreconnectedSpace := hpre, toNonempty := hne }

end LateralTheory.E.LineZeroCut
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.LineZeroCut

namespace LateralTheory.E.LZProperCut

def LZReduce : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] {X : Scheme.{0}}
  (r : X ⟶ Spec (CommRingCat.of A)), IsProper r → ConnectedSpace X → ¬ PreconnectedSpace ↑(pullback r (cpt A)) →
  ∃ (A' : Type) (_ : CommRing A') (_ : IsLocalRing A') (_ : HenselianLocalRing A') (_ : IsNoetherianRing A')
    (X' : Scheme.{0}) (r' : X' ⟶ Spec (CommRingCat.of A')),
    IsProper r' ∧ ConnectedSpace X' ∧ ¬ PreconnectedSpace ↑(pullback r' (cpt A'))

def LZStein : Prop := ∀ (A : Type) [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
  (r : X ⟶ Spec (CommRingCat.of A)), IsProper r →
  ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Finite A B) (s : X ⟶ Spec (CommRingCat.of B)),
    s ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = r ∧
    (ConnectedSpace X → ConnectedSpace ↑(Spec (CommRingCat.of B))) ∧
    ∀ y : ↑(Spec (CommRingCat.of B)), _root_.IsPreconnected (s.base ⁻¹' {y})

def LZHensFinite : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
  (B : Type) [CommRing B] [Algebra A B] [Module.Finite A B],
  ConnectedSpace ↑(Spec (CommRingCat.of B)) → IsLocalRing B

def LZPreimage : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Type) [CommRing B] [Algebra A B]
  [Module.Finite A B] [IsLocalRing B],
  (Spec.map (CommRingCat.ofHom (algebraMap A B))).base ⁻¹' {IsLocalRing.closedPoint A} = {IsLocalRing.closedPoint B}

def LZFibre : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (r : X ⟶ Spec (CommRingCat.of A)),
  _root_.IsPreconnected (r.base ⁻¹' {IsLocalRing.closedPoint A}) → PreconnectedSpace ↑(pullback r (cpt A))

theorem noeth_of (hS : LZStein) (hH : LZHensFinite) (hP : LZPreimage) (hF : LZFibre)
    (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    (r : X ⟶ Spec (CommRingCat.of A)) (hr : IsProper r) (hX : ConnectedSpace X) :
    PreconnectedSpace ↑(pullback r (cpt A)) := by
  apply hF A r
  obtain ⟨B, _, _, _, s, hs, hconn, hfib⟩ := hS A r hr
  have hB := hconn hX
  have : IsLocalRing B := hH A B hB
  have key : r.base ⁻¹' {IsLocalRing.closedPoint A} = s.base ⁻¹' {IsLocalRing.closedPoint B} := by
    rw [← hP A B, ← hs]
    rfl
  rw [key]
  exact hfib _

theorem goal_of (hR : LZReduce) (hS : LZStein) (hH : LZHensFinite) (hP : LZPreimage) (hF : LZFibre) :
    LateralTheory.E.LineZeroCut.LZProper := by
  intro A _ _ _ X r hr hX
  by_contra hn
  obtain ⟨A', _, _, _, _, X', r', hr', hX', hn'⟩ := hR A r hr hX hn
  exact hn' (noeth_of hS hH hP hF A' r' hr' hX')

end LateralTheory.E.LZProperCut
end
end
