import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKummerEqOfPicardTorsionFree

open AlgebraicGeometry GlobalTheory.EtC

theorem UpperTheory.Cb.exists_unit_kummer_eq_of_picard_torsionFree :
    ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → (∀ c : CommRing.Pic A, c ^ q = 1 → c = 1) → ∀ x : Ht q (sp A) 1 1, ∃ u : (Γ(Spec (CommRingCat.of A), ⊤))ˣ, kum q u = x :=
  _root_.GlobalTheory.EtC.kum_surjective
