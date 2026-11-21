import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNeighbourhoodLocalRingIsDirected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingTransitionMapIsLocalHomInjecti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNbhdTransitionMapDirectedSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingToHenselisationInjectiveOfNbhd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveResidueCompEtaleHenselian
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingToHenselisationAlgebraMap

section
section
open IsLocalRing

noncomputable section

namespace GlobalTheory.Henselisation

namespace LocalLimit

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem directedSystem_trans :
    DirectedSystem (fun i : EtNbhd R => i.B) (fun i j h => ⇑(EtNbhd.trans h : i.B →+* j.B)) where
  map_self := fun i x => (GlobalTheory.T.pointedEtaleNbhd_transitionMap_directedSystem R).1 i x
  map_map := fun {k j i} hij hjk x => (GlobalTheory.T.pointedEtaleNbhd_transitionMap_directedSystem R).2 i j k hij hjk x

theorem directed : IsDirected (EtNbhd R) (· ≤ ·) := GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R

theorem of_injective (i : EtNbhd R) : Function.Injective (Hens.of i) := by
  haveI := directedSystem_trans (R := R)
  haveI := directed (R := R)
  exact Ring.DirectLimit.of_injective (G := fun i : EtNbhd R => i.B)
    (fun i j h => EtNbhd.trans h) (fun i j h => (GlobalTheory.T.etaleNbhdLocalRingTransitionMap_isLocalHom_injective R i j h).2) i

theorem exists_of (z : Hens R) : ∃ (i : EtNbhd R) (x : i.B), Hens.of i x = z := by
  haveI := directed (R := R)
  exact Ring.DirectLimit.exists_of z

theorem of_trans {i j : EtNbhd R} (h : i ≤ j) (x : i.B) :
    Hens.of j (EtNbhd.trans h x) = Hens.of i x :=
  Ring.DirectLimit.of_f (G := fun i : EtNbhd R => i.B) (f := fun _ _ h => ⇑(EtNbhd.trans h)) h x

theorem nontrivial : Nontrivial (Hens R) := by
  refine nontrivial_of_ne (1 : Hens R) 0 ?_
  intro h
  rw [← map_one (Hens.of (EtNbhd.base (R := R))), ← map_zero (Hens.of (EtNbhd.base (R := R)))] at h
  exact one_ne_zero (of_injective _ h)

theorem isUnit_or_isUnit_of_add_one {a b : Hens R} (hab : a + b = 1) : IsUnit a ∨ IsUnit b := by
  obtain ⟨i, x, rfl⟩ := exists_of a
  obtain ⟨j, y, rfl⟩ := exists_of b
  haveI := directed (R := R)
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have h1 : EtNbhd.trans hik x + EtNbhd.trans hjk y = 1 := by
    apply of_injective k
    rw [map_add, of_trans, of_trans, map_one, hab]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h
  · left
    rw [← of_trans hik]
    exact h.map _
  · right
    rw [← of_trans hjk]
    exact h.map _

theorem isLocalHom_of (i : EtNbhd R) : IsLocalHom (Hens.of i) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨u, hu⟩ := hx
  obtain ⟨j, y, hy⟩ := exists_of (↑u⁻¹ : Hens R)
  haveI := directed (R := R)
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have h1 : EtNbhd.trans hik x * EtNbhd.trans hjk y = 1 := by
    apply of_injective k
    rw [map_mul, of_trans, of_trans, map_one, hy, ← hu, Units.mul_inv]
  haveI := (GlobalTheory.T.etaleNbhdLocalRingTransitionMap_isLocalHom_injective R i k hik).1
  exact isUnit_of_map_unit (EtNbhd.trans hik) x (IsUnit.of_mul_eq_one _ h1)

end LocalLimit

theorem hens_isLocalRing_and_isLocalHom_of :
    ∀ (R : Type) [CommRing R] [IsLocalRing R], IsLocalRing (Hens R) ∧ ∀ i : EtNbhd R, IsLocalHom (Hens.of i) := by
  intro R _ _
  haveI := LocalLimit.nontrivial (R := R)
  exact ⟨IsLocalRing.of_is_unit_or_is_unit_of_add_one LocalLimit.isUnit_or_isUnit_of_add_one,
    LocalLimit.isLocalHom_of⟩

end GlobalTheory.Henselisation

end
end

open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalRing_hens_and_isLocalHom_of : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsLocalRing (Hens R) ∧ ∀ i : EtNbhd R, IsLocalHom (Hens.of i) := by
  atlas_forward_decl GlobalTheory.Henselisation.hens_isLocalRing_and_isLocalHom_of
end

section
section
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.Henselisation

namespace StageHensel

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem trans_algebraMap_eq_of_comp {i j : EtNbhd R} (hij : i ≤ j) (φ : i.A →ₐ[R] j.A)
    (hφ : j.pt.comp φ = i.pt) (a : i.A) :
    EtNbhd.trans hij (algebraMap i.A i.B a) = algebraMap j.A j.B (φ a) := by
  have h1 : EtNbhd.trans hij (algebraMap i.A i.B a) = algebraMap j.A j.B (hij.choose a) :=
    Localization.localRingHom_to_map _ _ _ _ _
  rw [h1]
  have key : (IsScalarTower.toAlgHom R j.A j.B).comp hij.choose =
      (IsScalarTower.toAlgHom R j.A j.B).comp φ := by
    apply GlobalTheory.EtaleHensel.algHom_eq_of_residue_eq
    intro x
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← map_sub,
      IsLocalization.AtPrime.to_map_mem_maximal_iff j.B j.q]
    show _ ∈ RingHom.ker j.pt
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (congr($(hij.choose_spec) x)).trans (congr($hφ x)).symm
  exact congr($key a)

end StageHensel

open StageHensel in

theorem exists_le_isRoot_of_simple_root (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R)
    (h : Polynomial i.A) (a₀ : i.A) (hm : h.Monic) (h0 : i.pt (h.eval a₀) = 0)
    (h1 : i.pt (h.derivative.eval a₀) ≠ 0) :
    ∃ (j : EtNbhd R) (hij : i ≤ j) (c : j.B),
      (h.map ((EtNbhd.trans hij).comp (algebraMap i.A i.B))).IsRoot c ∧
      c - EtNbhd.trans hij (algebraMap i.A i.B a₀) ∈ maximalIdeal j.B := by
  let P : StandardEtalePair i.A := ⟨h, hm, derivative h, ⟨1, 0, 1, by simp⟩⟩
  letI : Algebra R P.Ring := ((algebraMap i.A P.Ring).comp (algebraMap R i.A)).toAlgebra
  haveI : IsScalarTower R i.A P.Ring := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.Etale R P.Ring := Algebra.Etale.comp R i.A P.Ring
  letI : Algebra i.A (ResidueField R) := (i.pt : i.A →+* ResidueField R).toAlgebra
  haveI : IsScalarTower R i.A (ResidueField R) :=
    IsScalarTower.of_algebraMap_eq' (i.pt.comp_algebraMap).symm
  have hmap : P.HasMap (i.pt a₀) := by
    constructor
    · show eval₂ (i.pt : i.A →+* ResidueField R) ((i.pt : i.A →+* ResidueField R) a₀) h = 0
      rw [eval₂_at_apply]
      exact h0
    · show IsUnit (eval₂ (i.pt : i.A →+* ResidueField R)
        ((i.pt : i.A →+* ResidueField R) a₀) (derivative h))
      rw [eval₂_at_apply]
      exact isUnit_iff_ne_zero.2 h1
  let x : P.Ring →ₐ[R] ResidueField R := (P.lift _ hmap).restrictScalars R
  have hxA : ∀ a : i.A, x (algebraMap i.A P.Ring a) = i.pt a := fun a => (P.lift _ hmap).commutes a
  have hxX : x P.X = i.pt a₀ := P.lift_X _ hmap
  obtain ⟨n, f, hf⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType R P.Ring)
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  let j : EtNbhd R := ⟨n, RingHom.ker f, Algebra.Etale.of_equiv e.symm, x.comp (e : _ →ₐ[R] P.Ring)⟩
  have hjpt : ∀ y : P.Ring, j.pt (e.symm y) = x y := fun y => by
    show x (e (e.symm y)) = x y
    rw [AlgEquiv.apply_symm_apply]
  let φ : i.A →ₐ[R] j.A := (e.symm : P.Ring →ₐ[R] j.A).comp (IsScalarTower.toAlgHom R i.A P.Ring)
  have hφa : ∀ a, φ a = e.symm (algebraMap i.A P.Ring a) := fun a => rfl
  have hφ : j.pt.comp φ = i.pt := AlgHom.ext fun a => by
    rw [AlgHom.comp_apply, hφa, hjpt, hxA]
  refine ⟨j, ⟨φ, hφ⟩, algebraMap j.A j.B (e.symm P.X), ?_, ?_⟩
  · have hc : (EtNbhd.trans (⟨φ, hφ⟩ : i ≤ j)).comp (algebraMap i.A i.B) =
        ((algebraMap j.A j.B).comp (e.symm : P.Ring →+* j.A)).comp (algebraMap i.A P.Ring) :=
      RingHom.ext fun a => by
        rw [RingHom.comp_apply, trans_algebraMap_eq_of_comp _ φ hφ, hφa]
        rfl
    rw [hc, IsRoot, eval_map]
    have hX := (StandardEtalePair.hasMap_X (P := P)).1
    rw [aeval_def] at hX
    have : eval₂ (((algebraMap j.A j.B).comp (e.symm : P.Ring →+* j.A)).comp
        (algebraMap i.A P.Ring)) (algebraMap j.A j.B (e.symm P.X)) h =
        ((algebraMap j.A j.B).comp (e.symm : P.Ring →+* j.A)) (eval₂ (algebraMap i.A P.Ring) P.X h) := by
      rw [hom_eval₂]
      rfl
    rw [this]
    change _ = (0 : j.B)
    rw [show eval₂ (algebraMap i.A P.Ring) P.X h = 0 from hX, map_zero]
  · haveI : j.q.IsPrime := RingHom.ker_isPrime _
    rw [trans_algebraMap_eq_of_comp _ φ hφ, ← map_sub, IsLocalization.AtPrime.to_map_mem_maximal_iff j.B j.q]
    show _ ∈ RingHom.ker j.pt
    rw [RingHom.mem_ker, map_sub, hjpt, hxX, sub_eq_zero]
    exact (congr($hφ a₀)).symm

end GlobalTheory.Henselisation

end
end

open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_le_isRoot_of_simpleRoot_pointedEtaleNbhd : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (h : Polynomial i.A) (a₀ : i.A), h.Monic → i.pt (h.eval a₀) = 0 → i.pt (h.derivative.eval a₀) ≠ 0 → ∃ (j : EtNbhd R) (hij : i ≤ j) (c : j.B), (h.map ((EtNbhd.trans hij).comp (algebraMap i.A i.B))).IsRoot c ∧ c - EtNbhd.trans hij (algebraMap i.A i.B a₀) ∈ maximalIdeal j.B := by
  atlas_forward_decl GlobalTheory.Henselisation.exists_le_isRoot_of_simple_root
end

section
section
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem EtNbhd.exists_sub_mem_maximalIdeal :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (b : i.B),
      ∃ r : R, b - algebraMap R i.B r ∈ maximalIdeal i.B := by
  intro R _ _ i b
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective i.q.primeCompl b
  obtain ⟨r₁, hr₁⟩ := residue_surjective (i.pt a)
  obtain ⟨r₂, hr₂⟩ := residue_surjective (i.pt (s : i.A))
  have hs : i.pt (s : i.A) ≠ 0 := by
    intro h
    exact s.2 (show (s : i.A) ∈ RingHom.ker i.pt from h)
  have hu : IsUnit r₂ := by
    by_contra hn
    apply hs
    rw [← hr₂]
    exact (residue_eq_zero_iff r₂).2 hn
  obtain ⟨u, rfl⟩ := hu
  refine ⟨r₁ * ((u⁻¹ : Rˣ) : R), ?_⟩
  have key : IsLocalization.mk' i.B a s - algebraMap R i.B (r₁ * ((u⁻¹ : Rˣ) : R)) =
      IsLocalization.mk' i.B (a - (s : i.A) * algebraMap R i.A (r₁ * ((u⁻¹ : Rˣ) : R))) s := by
    rw [IsLocalization.eq_mk'_iff_mul_eq, sub_mul, IsLocalization.mk'_spec, map_sub]
    simp only [map_mul, ← IsScalarTower.algebraMap_apply R i.A i.B]
    ring
  rw [key, IsLocalization.AtPrime.mk'_mem_maximal_iff (S := i.B) (I := i.q)]
  show _ ∈ RingHom.ker i.pt
  rw [RingHom.mem_ker, map_sub, map_mul, AlgHom.commutes, ← hr₁, ← hr₂]
  rw [show algebraMap R (ResidueField R) = residue R from rfl, ← map_mul, ← map_sub]
  rw [residue_eq_zero_iff]
  have : r₁ - (u : R) * (r₁ * ((u⁻¹ : Rˣ) : R)) = 0 := by
    rw [mul_left_comm, Units.mul_inv, mul_one, sub_self]
  rw [this]
  exact zero_mem _

end GlobalTheory.Henselisation
end

open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sub_mem_maximalIdeal_pointedEtaleNeighbourhood : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (b : i.B), ∃ r : R, b - algebraMap R i.B r ∈ maximalIdeal i.B := by
  atlas_forward_decl GlobalTheory.Henselisation.EtNbhd.exists_sub_mem_maximalIdeal
end

section
section
open IsLocalRing GlobalTheory.Henselisation Polynomial

namespace GlobalTheory.Henselisation

theorem eval_derivative_scaleRoots_mul {S : Type*} [CommRing S] (p : S[X]) (s x : S) :
    (derivative (p.scaleRoots s)).eval (s * x) = s ^ (p.natDegree - 1) * (derivative p).eval x := by
  have h1 : (derivative (p.scaleRoots s)).natDegree < p.natDegree + 1 := by
    have := natDegree_derivative_le (p.scaleRoots s)
    rw [natDegree_scaleRoots] at this; omega
  have h2 : (derivative p).natDegree < p.natDegree + 1 := by
    have := natDegree_derivative_le p; omega
  rw [eval_eq_sum_range' h1, eval_eq_sum_range' h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_derivative, coeff_derivative, coeff_scaleRoots]
  by_cases hkd : k + 1 ≤ p.natDegree
  · have e : s ^ (p.natDegree - (k + 1)) * (s * x) ^ k = s ^ (p.natDegree - 1) * x ^ k := by
      rw [mul_pow, ← mul_assoc, ← pow_add]; congr 2; omega
    calc _ = p.coeff (k + 1) * (↑k + 1) * (s ^ (p.natDegree - (k + 1)) * (s * x) ^ k) := by ring
      _ = _ := by rw [e]; ring
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; ring

theorem isUnit_of_sub_mem_maximalIdeal {S : Type*} [CommRing S] [IsLocalRing S] {x u : S}
    (hu : IsUnit u) (h : x - u ∈ maximalIdeal S) : IsUnit x := by
  by_contra hx
  have hx' : x ∈ maximalIdeal S := (mem_maximalIdeal x).2 hx
  have : u ∈ maximalIdeal S := by
    have := Ideal.sub_mem _ hx' h; simpa using this
  exact (mem_maximalIdeal u).1 this hu

theorem henselianLocalRing_hens : ∀ (R : Type) [CommRing R] [IsLocalRing R],
    HenselianLocalRing (Hens R) := by
  intro R _ _
  haveI : IsDirected (EtNbhd R) (· ≤ ·) := GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R
  obtain ⟨hloc, hofloc⟩ := GlobalTheory.T.isLocalRing_hens_and_isLocalHom_of R
  letI := hloc
  refine { toIsLocalRing := hloc, is_henselian := ?_ }
  intro f hf a₀ hfa₀ hf'a₀

  obtain ⟨i', b₀, hb₀⟩ : ∃ (i : EtNbhd R) (b : i.B), Hens.of i b = a₀ :=
    Ring.DirectLimit.exists_of a₀
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_sub_mem_maximalIdeal_pointedEtaleNeighbourhood R i' b₀
  set ρ := algebraMap R (Hens R) r with hρdef
  have hρ : a₀ - ρ ∈ maximalIdeal (Hens R) := by
    haveI := hofloc i'
    rw [← hb₀, hρdef, ← GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R i' r, ← map_sub]; exact map_nonunit _ _ hr
  have hfρ : f.eval ρ ∈ maximalIdeal (Hens R) := by
    have hd := sub_dvd_eval_sub ρ a₀ f
    have : f.eval ρ - f.eval a₀ ∈ maximalIdeal (Hens R) := by
      obtain ⟨c, hc⟩ := hd
      rw [hc]; apply Ideal.mul_mem_right
      have := (Ideal.neg_mem_iff _).2 hρ; simpa using this
    simpa using Ideal.add_mem _ this hfa₀
  have hf'ρ : IsUnit (f.derivative.eval ρ) := by
    refine isUnit_of_sub_mem_maximalIdeal hf'a₀ ?_
    obtain ⟨c, hc⟩ := sub_dvd_eval_sub ρ a₀ (derivative f)
    rw [hc]; apply Ideal.mul_mem_right
    have := (Ideal.neg_mem_iff _).2 hρ; simpa using this

  obtain ⟨i, g, hg⟩ : ∃ (i : EtNbhd R) (g : Polynomial i.B), g.map (Hens.of i) = f :=
    Ring.DirectLimit.Polynomial.exists_of (f' := fun _ _ h => EtNbhd.trans h) f
  haveI := hofloc i
  have hgm : g.Monic := monic_of_injective (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_injective_of_nbhd R i) (hg ▸ hf)
  let M := i.q.primeCompl
  let ψ : i.A →+* i.B := algebraMap i.A i.B
  let s : M := IsLocalization.commonDenom M g.support g.coeff
  have hl := IsLocalization.scaleRoots_commonDenom_mem_lifts M g
    (by rw [hgm.leadingCoeff]; exact ⟨1, map_one _⟩)
  obtain ⟨h, hhmap, -, hhm⟩ := lifts_and_natDegree_eq_and_monic hl
    ((monic_scaleRoots_iff _).2 hgm)
  let Φ : i.A →+* Hens R := (Hens.of i).comp ψ
  let u : Hens R := Φ s
  have hu : IsUnit u := (IsLocalization.map_units i.B s).map (Hens.of i)
  have hΦr : Φ (algebraMap R i.A r) = ρ := by
    simp only [Φ, ψ, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    exact GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R i r
  let a₀' : i.A := (s : i.A) * algebraMap R i.A r
  have hΦa₀' : Φ a₀' = u * ρ := by simp only [a₀', map_mul, hΦr]; rfl
  have hhΦ : h.map Φ = f.scaleRoots u := by
    rw [show Φ = (Hens.of i).comp ψ from rfl, ← Polynomial.map_map, hhmap, map_scaleRoots _ _ _
      (by rw [hgm.leadingCoeff, map_one]; exact one_ne_zero), hg]
    rfl
  have key1 : Φ (h.eval a₀') = u ^ f.natDegree * f.eval ρ := by
    rw [← eval₂_at_apply, ← eval_map, hhΦ, hΦa₀']
    exact scaleRoots_eval₂_mul (RingHom.id _) ρ u
  have key2 : Φ (h.derivative.eval a₀') = u ^ (f.natDegree - 1) * f.derivative.eval ρ := by
    rw [← eval₂_at_apply, ← eval_map, ← derivative_map, hhΦ, hΦa₀']
    exact eval_derivative_scaleRoots_mul f u ρ
  have hpt1 : i.pt (h.eval a₀') = 0 := by
    have hm : ψ (h.eval a₀') ∈ maximalIdeal i.B := by
      intro hun
      have : Φ (h.eval a₀') ∈ maximalIdeal (Hens R) := by
        rw [key1]; exact Ideal.mul_mem_left _ _ hfρ
      exact (mem_maximalIdeal _).1 this (hun.map (Hens.of i))
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff i.B i.q _).1 hm
    exact (RingHom.mem_ker).1 this
  have hpt2 : i.pt (h.derivative.eval a₀') ≠ 0 := by
    intro h0
    have hq : h.derivative.eval a₀' ∈ i.q := RingHom.mem_ker.2 h0
    have hm := (IsLocalization.AtPrime.to_map_mem_maximal_iff i.B i.q _).2 hq
    have hΦm : Φ (h.derivative.eval a₀') ∈ maximalIdeal (Hens R) := map_nonunit (Hens.of i) _ hm
    rw [key2] at hΦm
    exact (mem_maximalIdeal _).1 hΦm ((hu.pow _).mul hf'ρ)
  obtain ⟨j, hij, c, hc, hcm⟩ := GlobalTheory.T.exists_le_isRoot_of_simpleRoot_pointedEtaleNbhd R i h a₀' hhm hpt1 hpt2
  haveI := hofloc j
  have hofj : (Hens.of j).comp (EtNbhd.trans hij) = Hens.of i :=
    RingHom.ext fun x => Ring.DirectLimit.of_f hij x
  have hΦj : (Hens.of j).comp ((EtNbhd.trans hij).comp ψ) = Φ := by
    rw [← RingHom.comp_assoc, hofj]
  set c' := Hens.of j c
  have hroot : (f.scaleRoots u).eval c' = 0 := by
    rw [← hhΦ, ← hΦj, ← Polynomial.map_map, eval_map, eval₂_at_apply, hc.eq_zero, map_zero]
  have hcm' : c' - u * ρ ∈ maximalIdeal (Hens R) := by
    have := map_nonunit (Hens.of j) _ hcm
    rwa [map_sub, ← RingHom.comp_apply (Hens.of j) (EtNbhd.trans hij),
      ← RingHom.comp_apply ((Hens.of j).comp (EtNbhd.trans hij)) ψ, hofj,
      show (Hens.of i).comp ψ = Φ from rfl, hΦa₀'] at this
  refine ⟨↑hu.unit⁻¹ * c', ?_, ?_⟩
  · have hc' : c' = u * (↑hu.unit⁻¹ * c') := by
      rw [← mul_assoc, hu.mul_val_inv, one_mul]
    have e := scaleRoots_eval₂_mul (p := f) (RingHom.id _) (↑hu.unit⁻¹ * c') u
    simp only [RingHom.id_apply] at e
    change eval (u * _) _ = u ^ _ * eval _ f at e
    rw [← hc', hroot] at e
    exact (((hu.pow _).mul_right_eq_zero).1 e.symm)
  · have e1 : ↑hu.unit⁻¹ * c' - ρ = ↑hu.unit⁻¹ * (c' - u * ρ) := by
      rw [mul_sub, ← mul_assoc, hu.val_inv_mul, one_mul]
    have e2 : ↑hu.unit⁻¹ * c' - a₀ = (↑hu.unit⁻¹ * c' - ρ) - (a₀ - ρ) := by ring
    rw [e2, e1]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hcm') hρ

end GlobalTheory.Henselisation
end

open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.henselianLocalRing_hens' : ∀ (R : Type) [CommRing R] [IsLocalRing R], HenselianLocalRing (Hens R) := by
  atlas_forward_decl GlobalTheory.Henselisation.henselianLocalRing_hens
end

section
section
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation.EtNbhd

instance isLocalHom_algebraMap_B {R : Type} [CommRing R] [IsLocalRing R] (i : EtNbhd R) :
    IsLocalHom (algebraMap R i.B) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hm : a ∈ maximalIdeal R := hna
  have hq : algebraMap R i.A a ∈ i.q := by
    show i.pt (algebraMap R i.A a) = 0
    rw [AlgHom.commutes]
    exact (residue_eq_zero_iff a).2 hm
  have : algebraMap R i.B a ∈ maximalIdeal i.B := by
    rw [IsScalarTower.algebraMap_apply R i.A i.B]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff i.B i.q _).2 hq
  exact this ha

theorem maximalIdeal_B_eq_map (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) :
    maximalIdeal i.B = (maximalIdeal R).map (algebraMap R i.B) :=
  Algebra.FormallyUnramified.map_maximalIdeal.symm

end GlobalTheory.Henselisation.EtNbhd
end

open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalIdeal_pointedEtaleNeighbourhood_eq_map : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), maximalIdeal i.B = (maximalIdeal R).map (algebraMap R i.B) := by
  atlas_forward_decl GlobalTheory.Henselisation.EtNbhd.maximalIdeal_B_eq_map
end

section
section
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem EtNbhd.flat_B : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), Module.Flat R i.B := by
  intro R _ _ i
  haveI : Module.Flat i.A i.B := IsLocalization.flat i.B i.q.primeCompl
  exact Module.Flat.trans R i.A i.B

end GlobalTheory.Henselisation
end

open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_localRing_pointedEtaleNeighbourhood : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), Module.Flat R i.B := by
  atlas_forward_decl GlobalTheory.Henselisation.EtNbhd.flat_B
end

section
section
open IsLocalRing GlobalTheory.Henselisation

noncomputable section

namespace GlobalTheory.Henselisation

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem Hens.of_trans {i j : EtNbhd R} (h : i ≤ j) (y : i.B) :
    Hens.of j (EtNbhd.trans h y) = Hens.of i y :=
  Ring.DirectLimit.of_f h y

theorem Hens.exists_of (hdir : IsDirected (EtNbhd R) (· ≤ ·)) (z : Hens R) :
    ∃ (i : EtNbhd R) (y : i.B), Hens.of i y = z :=
  haveI : IsDirectedOrder (EtNbhd R) := hdir
  Ring.DirectLimit.exists_of (G := fun i : EtNbhd R => i.B)
    (f := fun _ _ h => ⇑(EtNbhd.trans h)) z

theorem Hens.exists_of_fin (hdir : IsDirected (EtNbhd R) (· ≤ ·)) :
    ∀ (l : ℕ) (x : Fin l → Hens R), ∃ (i : EtNbhd R) (y : Fin l → i.B), ∀ k, Hens.of i (y k) = x k := by
  intro l
  induction l with
  | zero => exact fun x => ⟨EtNbhd.base, fun k => k.elim0, fun k => k.elim0⟩
  | succ l ih =>
    intro x
    obtain ⟨i, y, hy⟩ := ih (fun k => x k.castSucc)
    obtain ⟨j, z, hz⟩ := Hens.exists_of hdir (x (Fin.last l))
    obtain ⟨m, him, hjm⟩ := directed_of (· ≤ ·) i j
    refine ⟨m, Fin.lastCases (EtNbhd.trans hjm z) (fun k => EtNbhd.trans him (y k)), ?_⟩
    intro k
    induction k using Fin.lastCases with
    | last => dsimp only; rw [Fin.lastCases_last, Hens.of_trans, hz]
    | cast k => dsimp only; rw [Fin.lastCases_castSucc, Hens.of_trans, hy]

theorem flat_hens_of_stages (hdir : IsDirected (EtNbhd R) (· ≤ ·))
    (hinj : ∀ i : EtNbhd R, Function.Injective (Hens.of i))
    (halg : ∀ (i : EtNbhd R) (r : R), Hens.of i (algebraMap R i.B r) = algebraMap R (Hens R) r)
    (hflat : ∀ i : EtNbhd R, Module.Flat R i.B) : Module.Flat R (Hens R) := by
  have hsmul : ∀ (i : EtNbhd R) (r : R) (y : i.B), Hens.of i (r • y) = r • Hens.of i y := by
    intro i r y
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, halg]
  refine Module.Flat.iff_forall_isTrivialRelation.mpr ?_
  intro l f x hfx
  obtain ⟨i, y, hy⟩ := Hens.exists_of_fin hdir l x
  have h0 : ∑ k, f k • y k = 0 := by
    apply hinj i
    rw [map_zero, map_sum]
    simp only [hsmul, hy]
    exact hfx
  obtain ⟨k, a, z, hya, haf⟩ := Module.Flat.iff_forall_isTrivialRelation.mp (hflat i) h0
  refine ⟨k, a, fun j => Hens.of i (z j), fun m => ?_, haf⟩
  rw [← hy m, hya m, map_sum]
  simp only [hsmul]

theorem flat_hens : ∀ (R : Type) [CommRing R] [IsLocalRing R], Module.Flat R (Hens R) :=
  fun R _ _ => flat_hens_of_stages (GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R) (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_injective_of_nbhd R) (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R) (GlobalTheory.T.flat_localRing_pointedEtaleNeighbourhood R)

end GlobalTheory.Henselisation
end
end

open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_hens' : ∀ (R : Type) [CommRing R] [IsLocalRing R], Module.Flat R (Hens R) := by
  atlas_forward_decl GlobalTheory.Henselisation.flat_hens
end

section
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem exists_henselisation : ∀ (R : Type) [CommRing R] [IsLocalRing R], ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (_ : HenselianLocalRing S) (_ : IsLocalHom (algebraMap R S)), Module.Flat R S ∧ (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧ Function.Bijective (ResidueField.map (algebraMap R S)) ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  intro R _ _
  haveI : IsDirected (EtNbhd R) (· ≤ ·) := GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R
  obtain ⟨hloc, hofloc⟩ := GlobalTheory.T.isLocalRing_hens_and_isLocalHom_of R
  haveI : HenselianLocalRing (Hens R) := GlobalTheory.T.henselianLocalRing_hens' R
  let ofA : ∀ i : EtNbhd R, i.B →ₐ[R] Hens R := fun i =>
    { toRingHom := Hens.of i, commutes' := GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R i }
  have hof_trans : ∀ {i j : EtNbhd R} (h : i ≤ j) (x : i.B),
      Hens.of j (EtNbhd.trans h x) = Hens.of i x := fun h x => Ring.DirectLimit.of_f h x
  have hexists : ∀ s : Hens R, ∃ i b, Hens.of i b = s := fun s => Ring.DirectLimit.exists_of s
  have hlocB : ∀ i : EtNbhd R, IsLocalHom (algebraMap R i.B) := fun i => ⟨fun r hr => by
    by_contra hn
    have hm : algebraMap R i.B r ∈ maximalIdeal i.B := by
      rw [GlobalTheory.T.maximalIdeal_pointedEtaleNeighbourhood_eq_map R i]; exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal r).2 hn)
    exact (mem_maximalIdeal _).1 hm hr⟩
  haveI : IsLocalHom (algebraMap R (Hens R)) := by
    have e : algebraMap R (Hens R) =
        (Hens.of EtNbhd.base).comp (algebraMap R (EtNbhd.base (R := R)).B) := rfl
    rw [e]
    haveI := hlocB EtNbhd.base
    haveI := hofloc EtNbhd.base
    infer_instance
  have hmax : (maximalIdeal R).map (algebraMap R (Hens R)) = maximalIdeal (Hens R) := by
    apply le_antisymm
    · exact Ideal.map_le_iff_le_comap.2 fun r hr => map_nonunit (algebraMap R (Hens R)) r hr
    · intro s hs
      obtain ⟨i, b, rfl⟩ := hexists s
      have hb : b ∈ maximalIdeal i.B := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact (mem_maximalIdeal _).1 hs (hu.map (Hens.of i))
      rw [GlobalTheory.T.maximalIdeal_pointedEtaleNeighbourhood_eq_map R i] at hb
      have hm := Ideal.mem_map_of_mem (Hens.of i) hb
      rwa [Ideal.map_map, show (Hens.of i).comp (algebraMap R i.B) = algebraMap R (Hens R) from
        RingHom.ext (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R i)] at hm
  have hres : Function.Bijective (ResidueField.map (algebraMap R (Hens R))) := by
    refine ⟨RingHom.injective _, fun y => ?_⟩
    obtain ⟨s, rfl⟩ := residue_surjective y
    obtain ⟨i, b, rfl⟩ := hexists s
    obtain ⟨r, hr⟩ := GlobalTheory.T.exists_sub_mem_maximalIdeal_pointedEtaleNeighbourhood R i b
    refine ⟨residue R r, ?_⟩
    rw [ResidueField.map_residue, eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
      ← GlobalTheory.T.etaleNbhdLocalRingToHenselisation_algebraMap R i r, ← map_sub]
    exact map_nonunit (Hens.of i) _ hr
  refine ⟨Hens R, inferInstance, inferInstance, inferInstance, inferInstance, GlobalTheory.T.flat_hens' R, hmax, hres,
    EtNbhd R, inferInstance, inferInstance, inferInstance, fun i => (ofA i).range, ?_, ?_, ?_⟩
  · intro i j h y hy
    obtain ⟨x, rfl⟩ := (AlgHom.mem_range _).1 hy
    exact (AlgHom.mem_range _).2 ⟨EtNbhd.trans h x, hof_trans h x⟩
  · intro s
    obtain ⟨i, b, rfl⟩ := hexists s
    exact ⟨i, (AlgHom.mem_range _).2 ⟨b, rfl⟩⟩
  · intro i
    exact ⟨i.A, inferInstance, inferInstance, inferInstance, i.q, inferInstance,
      ⟨AlgEquiv.ofInjective (ofA i) (GlobalTheory.T.etaleNbhdLocalRingToHenselisation_injective_of_nbhd R i)⟩⟩

end GlobalTheory.Henselisation
end
