import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedFieldPairsEquivDefiniteFieldPairsOdd
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DPairOneIrr

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.markedFieldPairs_equiv_definiteFieldPairs_odd : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (sel : Polynomial G.F → ℂ), IsSel G sel → ∃ e : {q : Cls G // Irreducible (Quot.out q).pol ∧ (Quot.out q).Mark (sel (Quot.out q).pol)} ≃ {q : DCls G // Irreducible (Quot.out q).pol}, ∀ q, (Quot.out (e q).1).pol = (Quot.out q.1).pol ∧ ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → (Quot.out (e q).1).term Kf f r K φ = (Quot.out q.1).term Kf f r K φ := by
  first | (exact @GlobalTheory.LKDef.cls_equiv_dcls_irr) | (exact GlobalTheory.LKDef.cls_equiv_dcls_irr) | (intros; apply GlobalTheory.LKDef.cls_equiv_dcls_irr <;> assumption)
end

section
open scoped Classical

namespace GlobalTheory

theorem finsum_ite_eq_of_equiv {A B : Type} (PA : A → Prop) (PB : B → Prop)
    (e : {a // PA a} ≃ {b // PB b}) (g : A → ℂ) (h : B → ℂ)
    (hgh : ∀ a, h (e a).1 = g a.1) :
    (∑ᶠ a, if PA a then g a else 0) = ∑ᶠ b, if PB b then h b else 0 := by
  have hA : (∑ᶠ a, if PA a then g a else 0) = ∑ᶠ a : {a // PA a}, g a.1 := by
    rw [finsum_subtype_eq_finsum_cond]
    exact finsum_congr fun a => (finsum_eq_if).symm
  have hB : (∑ᶠ b, if PB b then h b else 0) = ∑ᶠ b : {b // PB b}, h b.1 := by
    rw [finsum_subtype_eq_finsum_cond]
    exact finsum_congr fun b => (finsum_eq_if).symm
  rw [hA, hB, ← finsum_comp_equiv e]
  exact finsum_congr fun a => (hgh a).symm

example : ∀ {A B : Type} (PA : A → Prop) (PB : B → Prop) (e : {a // PA a} ≃ {b // PB b}) (g : A → ℂ) (h : B → ℂ), (∀ a, h (e a).1 = g a.1) → (∑ᶠ a, if PA a then g a else 0) = ∑ᶠ b, if PB b then h b else 0 :=
  fun PA PB e g h hgh => finsum_ite_eq_of_equiv PA PB e g h hgh

end GlobalTheory
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

theorem marked_field_pairs_sum_eq_definite_pairs_sum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (wt sel : Polynomial G.F → ℂ), IsSel G sel → ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → markedSumIrr G wt sel Kf f r K φ = dSumIrr G wt Kf f r K φ := by
  intro p _ G ha hn wt sel hsel Kf f r K φ hr hf hφ
  obtain ⟨e, he⟩ := GlobalTheory.T.markedFieldPairs_equiv_definiteFieldPairs_odd p G ha hn sel hsel
  unfold markedSumIrr dSumIrr
  convert GlobalTheory.finsum_ite_eq_of_equiv _ _ e (fun a : Cls G => wt (Quot.out a).pol * (Quot.out a).term Kf f r K φ)
    (fun b : DCls G => wt (Quot.out b).pol * (Quot.out b).term Kf f r K φ) fun q => by
    obtain ⟨hpol, hterm⟩ := he q
    show wt (Quot.out (e q).1).pol * (Quot.out (e q).1).term Kf f r K φ = wt (Quot.out q.1).pol * (Quot.out q.1).term Kf f r K φ
    rw [hpol, hterm Kf f r K φ hr hf hφ]

end GlobalTheory.LKDef
end
