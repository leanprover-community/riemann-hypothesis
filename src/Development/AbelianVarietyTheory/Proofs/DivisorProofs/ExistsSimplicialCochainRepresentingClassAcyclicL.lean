module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyPresheafClassesAsCocyclesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicPropertiStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.LeraySurj

variable {R : Type} [CommRing R]

theorem chains_d_eq (E : Spc) (n : ℕ) :
    ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (chainsXIso R E (n + 1)).hom ≫ (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫
        (chainsXIso R E n).inv := by
  have h2 : ((chainsN R).obj E).d (n + 1) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ _
  rw [← h2]
  exact HomologicalComplex.extend_d_eq _ _ rfl rfl

theorem step (E : Spc) (F : Shv R) {n : ℤ} (z : Cocycle ((chains R).obj E) (res R F) n) (k : ℕ)
    (hv : ∀ p q (hpq : p + n = q), -(k : ℤ) < p → z.1.v p q hpq = 0)
    (hex : ∀ t : (free R).obj (E.obj (op ⦋k⦌)) ⟶ (res R F).X (n - k), t ≫ (res R F).d (n - k) (n - k + 1) = 0 →
      ∃ y : (free R).obj (E.obj (op ⦋k⦌)) ⟶ (res R F).X (n - k - 1), t = y ≫ (res R F).d (n - k - 1) (n - k)) :
    ∃ z' : Cocycle ((chains R).obj E) (res R F) n, CohomologyClass.mk z' = CohomologyClass.mk z ∧
      ∀ p q (hpq : p + n = q), -((k + 1 : ℕ) : ℤ) < p → z'.1.v p q hpq = 0 := by
  have hcl : z.1.v (-(k : ℤ)) (n - k) (by omega) ≫ (res R F).d (n - k) (n - k + 1) = 0 := by
    have h := Cochain.congr_v (Cocycle.δ_eq_zero z (n + 1)) (-(k : ℤ)) (n - k + 1) (by omega)
    rw [δ_v n (n + 1) rfl _ _ _ _ (n - k) (-(k : ℤ) + 1) (by omega) rfl,
      hv (-(k : ℤ) + 1) _ _ (by omega)] at h
    simpa using h
  obtain ⟨y, hy⟩ := hex ((chainsXIso R E k).inv ≫ z.1.v (-(k : ℤ)) (n - k) (by omega))
    (by rw [Category.assoc, hcl, Limits.comp_zero])
  let β : Cochain ((chains R).obj E) (res R F) (n - 1) :=
    Cochain.single (p := -(k : ℤ)) (q := n - k - 1) ((chainsXIso R E k).hom ≫ y) (n - 1)
  let c : Cocycle ((chains R).obj E) (res R F) n := Cocycle.mk (δ (n - 1) n β) (n + 1) (by omega) (δ_δ _ _ _ _)
  refine ⟨z - c, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, sub_eq_self, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    exact ⟨β, rfl⟩
  · intro p q hpq hp
    have hβ1 : β.v (p + 1) q (by omega) = 0 := Cochain.single_v_eq_zero _ _ _ _ _ (by omega)
    have hc : c.1.v p q hpq = β.v p (q - 1) (by omega) ≫ (res R F).d (q - 1) q := by
      change (δ (n - 1) n β).v p q hpq = _
      rw [δ_v (n - 1) n (by omega) _ _ _ _ (q - 1) (p + 1) rfl rfl, hβ1]
      simp
    rw [Cocycle.coe_sub, Cochain.sub_v, hc]
    rcases lt_or_eq_of_le (show -(k : ℤ) ≤ p by omega) with h | h
    · rw [hv p q hpq h, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
      simp
    · subst h
      obtain rfl : q = n - k := by omega
      rw [Cochain.single_v]
      have hz : z.1.v (-(k : ℤ)) (n - k) hpq = (chainsXIso R E k).hom ≫ ((chainsXIso R E k).inv ≫ z.1.v (-(k : ℤ)) (n - k) hpq) := by
        rw [Iso.hom_inv_id_assoc]
      rw [hz, hy]
      simp

theorem exact_of_vanish (F : Shv R) (P : PSh) (m : ℤ) (h0 : ∀ y : H R (disc.obj P) F m, y = 0)
    (t : (free R).obj P ⟶ (res R F).X m) (ht : t ≫ (res R F).d m (m + 1) = 0) :
    ∃ y : (free R).obj P ⟶ (res R F).X (m - 1), t = y ≫ (res R F).d (m - 1) m := by
  obtain ⟨cl, -, hinj, hzero, -⟩ := GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles R F
  have h : cl P m t ht = cl P m 0 Limits.zero_comp := by rw [hzero]; exact h0 _
  obtain ⟨y, hy⟩ := (hinj P m t ht 0 Limits.zero_comp).1 h
  exact ⟨y, by rw [hy, zero_add]⟩

theorem reduce (F : Shv R) (E : Spc) (n : ℕ)
    (hyp : ∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0)
    (x : H R E F n) (j : ℕ) (hj : j ≤ n) :
    ∃ z : Cocycle ((chains R).obj E) (res R F) n, CohomologyClass.mk z = x ∧
      ∀ (p q : ℤ) (hpq : p + n = q), -(j : ℤ) < p → z.1.v p q hpq = 0 := by
  induction j with
  | zero =>
    obtain ⟨z, rfl⟩ := x.mk_surjective
    refine ⟨z, rfl, fun p q hpq hp => ?_⟩
    exact ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F).2.2.2.2.2 E p (by omega)).eq_of_src _ _
  | succ j ih =>
    obtain ⟨z, hz, hv⟩ := ih (by omega)
    obtain ⟨z', hz', hv'⟩ := step E F z j hv (fun t ht => by
      have hm : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by omega
      have h0 := hyp j (n - j) (by omega) (by omega)
      rw [hm] at h0
      have := exact_of_vanish F _ ((n : ℤ) - j) h0 t ht
      exact this)
    exact ⟨z', hz'.trans hz, hv'⟩

end GlobalTheory.EtC.LeraySurj

