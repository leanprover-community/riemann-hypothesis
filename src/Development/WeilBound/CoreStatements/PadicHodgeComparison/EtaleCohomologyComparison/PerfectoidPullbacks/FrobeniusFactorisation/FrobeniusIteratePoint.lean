import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.MuMor
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.OmMorPullIndep

section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.IterG

variable {O : Type} [CommRing O] {F : B.Fn O} {b : Base} {ht : b.t = 1} {κ κ' : O →+* b.R ⧸ b.I}

theorem gen_mu_nu {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) {φb : b.R →+* b.R} (dφ : IsDPMorphism b.γ b.γ φb)
    (P : F.ptK κ ⟶ F.ptK κ) (str : ∀ (B₀ : CommRingCat.{0}) (y : (F.ptK κ).obj B₀) (r : b.R),
      (P.app B₀ y).1.1 (Ideal.Quotient.mk _ r) = y.1.1 (Ideal.Quotient.mk _ (φb r)))
    {σ₀ : Λ →+* Λ} (hc : ∀ a, φb (c a) = c (σ₀ a)) (N : ℕ) (d₁ : IsDPMorphism b.γ b.γ (RingHom.id b.R))
    (Pi : F.ptK κ ⟶ F.ptK κ') (si) (hi : ∀ a, RingHom.id b.R (c a) = c (RingHom.id Λ a)) (d₂ : IsDPMorphism b.γ b.γ (φb ^ N))
    (Po : F.ptK κ' ⟶ F.ptK κ) (so) (ho : ∀ a, (φb ^ N) (c a) = c ((σ₀ ^ N) a))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F.ptK κ).obj B₀), (Po.app B₀ (Pi.app B₀ y)).1.2 = ((PtN P N).app B₀ y).1.2)
    (j : ℕ) (x : CH.H (B.OM (F.cr b ht κ) c) j) :
    (B.omMor (c := c) (c' := c) (B.crMor (F := F) (F' := F) (ht := ht) (ht' := ht) (RingHom.id b.R) rfl d₁ Pi si) (RingHom.id Λ) hi).pull j
      ((B.omMor (c := c) (c' := c) (B.crMor (F := F) (F' := F) (ht := ht) (ht' := ht) (φb ^ N) rfl d₂ Po so) (σ₀ ^ N) ho).pull j x) =
      (⇑((B.omMor (c := c) (c' := c) (B.crMor (F := F) (F' := F) (ht := ht) (ht' := ht) φb rfl dφ P str) σ₀ hc).pull j))^[N] x := by
  have h1 := comp_eq (ht := ht) c Pi d₁ si hi d₂ Po so (PtN P N) (strN P str N) ho hpt j x
  have h2 := iter_pull (ht := ht) c dφ P str hc j N x
  exact h1.trans h2.symm

end CrystallineSemistableComparison.IterG
end
end

section
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg

namespace CrystallineSemistableComparison.Pb.Mid

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem frobenius_iterate_point {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l) (n N : ℕ) (B₀ : CommRingCat.{0})
    (y : (F.ptK (B.κb κ true n)).obj B₀) (h : (l : B₀) = 0) :
    ((IterG.PtN (B.phiPt F κ n) N).app B₀ y).1.2 = F.Pt.map (CommRingCat.ofHom (frbN h N)) y.1.2 := by
  induction N with
  | zero =>
    change y.1.2 = F.Pt.map (CommRingCat.ofHom (RingHom.id _)) y.1.2
    rw [CommRingCat.ofHom_id, F.Pt.map_id]
    rfl
  | succ N ih =>
    change F.Pt.map (CommRingCat.ofHom (B.frb h)) ((IterG.PtN (B.phiPt F κ n) N).app B₀ y).1.2 = _
    rw [ih]
    have e : CommRingCat.ofHom (frbN h (N + 1)) = CommRingCat.ofHom (frbN h N) ≫ CommRingCat.ofHom (B.frb h) :=
      CommRingCat.hom_ext (RingHom.ext fun _ => rfl)
    rw [e, F.Pt.map_comp]
    rfl

theorem frobenius_mu_nu_iterate (r : Res l K) (N : ℕ) (hT : TeichmullerCongruence r N) (M : Model l K) (n j : ℕ)
    (x : B.Hc (B.schFn M.p) (okToOC l K) true n j) :
    mu r M n j hT (nu r M n j hT x) = (⇑(B.phiHc (B.schFn M.p) (okToOC l K) n j))^[N] x := by
  unfold mu nu muMor nuMor mIn mOut B.phiHc B.phiMorC phiP phiA
  exact IterG.gen_mu_nu (b := B.bs l true n) (ht := rfl) (F := B.schFn M.p) (κ := B.κb (okToOC l K) true n) (κ' := κm r n)
    ((base l).cris n) _ (B.phiPt (B.schFn M.p) (okToOC l K) n) _ _ N _ (ptIn (B.schFn M.p) n hT) _ _ _ (ptOut (B.schFn M.p) n hT) _ _
    (fun B₀ y => (frobenius_iterate_point (B.schFn M.p) (okToOC l K) n N B₀ y (l_zero y.1.1)).symm) j x

end CrystallineSemistableComparison.Pb.Mid
end
end
