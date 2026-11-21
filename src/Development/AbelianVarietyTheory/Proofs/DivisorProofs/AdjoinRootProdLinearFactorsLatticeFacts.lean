import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
import BuildAid.ForwardExisting

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

noncomputable section
namespace GlobalTheory.RingFacts

variable {O : Type} [CommRing O] {S : Type} [Fintype S] [DecidableEq S]

theorem monic_Q (a : S → O) : (∏ s, (X - Polynomial.C (a s)) : O[X]).Monic :=
  monic_prod_of_monic _ _ fun s _ => monic_X_sub_C (a s)

theorem lin_eq (a : S → O) (s : S) :
    lin a s = AdjoinRoot.mk (∏ s, (X - Polynomial.C (a s)) : O[X]) (X - Polynomial.C (a s)) := by
  simp [lin, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

theorem cofac_eq (a : S → O) (τ : S) :
    cofac a τ = AdjoinRoot.mk (∏ s, (X - Polynomial.C (a s)) : O[X])
      (∏ s ∈ Finset.univ.erase τ, (X - Polynomial.C (a s))) := by
  rw [cofac, map_prod]
  exact Finset.prod_congr rfl fun s _ => lin_eq a s

theorem ev_mk (a : S → O) (τ : S) (f : O[X]) :
    ev a τ (AdjoinRoot.mk _ f) = f.eval (a τ) := by
  simp [ev]

theorem exists_lin_mul_of_ev_eq_zero (a : S → O) (τ : S) (r : RS a) (hr : ev a τ r = 0) :
    ∃ r', r = lin a τ * r' := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [ev_mk] at hr
  obtain ⟨h, hh⟩ := (Polynomial.dvd_iff_isRoot).2 hr
  exact ⟨AdjoinRoot.mk _ h, by rw [hh, map_mul, lin_eq]⟩

theorem eq_algebraMap_add_lin_mul (a : S → O) (τ : S) (r : RS a) :
    ∃ g, r = algebraMap O (RS a) (ev a τ r) + lin a τ * g := by
  obtain ⟨g, hg⟩ := exists_lin_mul_of_ev_eq_zero a τ (r - algebraMap O (RS a) (ev a τ r))
    (by rw [map_sub, AlgHom.commutes]; simp)
  exact ⟨g, by rw [← hg]; ring⟩

theorem lin_mul_cofac (a : S → O) (τ : S) : lin a τ * cofac a τ = 0 := by
  rw [cofac, Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Finset.prod_congr rfl
    (fun s _ => lin_eq a s), ← map_prod]
  exact AdjoinRoot.mk_self

theorem ev_cofac (a : S → O) (τ : S) :
    ev a τ (cofac a τ) = ∏ s ∈ Finset.univ.erase τ, (a τ - a s) := by
  rw [cofac, map_prod]
  exact Finset.prod_congr rfl fun s _ => ev_lin a τ s

theorem eq_smul_cofac_of_lin_mul_eq_zero [IsDomain O] (a : S → O) (τ : S) (r : RS a)
    (hr : lin a τ * r = 0) : ∃ c : O, r = algebraMap O (RS a) c * cofac a τ := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [lin_eq, ← map_mul, AdjoinRoot.mk_eq_zero] at hr
  obtain ⟨g, hg⟩ := hr
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), mul_assoc] at hg
  have hf : f = (∏ s ∈ Finset.univ.erase τ, (X - Polynomial.C (a s))) * g :=
    mul_left_cancel₀ (X_sub_C_ne_zero (a τ)) hg
  obtain ⟨h, hh⟩ := eq_algebraMap_add_lin_mul a τ (AdjoinRoot.mk _ g)
  refine ⟨ev a τ (AdjoinRoot.mk _ g), ?_⟩
  have hc := lin_mul_cofac a τ
  calc AdjoinRoot.mk _ f = cofac a τ * AdjoinRoot.mk _ g := by rw [hf, map_mul, cofac_eq]
    _ = cofac a τ * (algebraMap O (RS a) (ev a τ (AdjoinRoot.mk _ g)) + lin a τ * h) := by
        rw [← hh]
    _ = algebraMap O (RS a) (ev a τ (AdjoinRoot.mk _ g)) * cofac a τ
        + (lin a τ * cofac a τ) * h := by ring
    _ = _ := by rw [hc]; simp

theorem ring_facts : ∀ (O : Type) [CommRing O] [IsDomain O] (S : Type) [Fintype S] [DecidableEq S]
    (a : S → O) (τ : S), Module.Free O (RS a) ∧ Module.Finite O (RS a) ∧
    lin a τ * cofac a τ = 0 ∧ ev a τ (cofac a τ) = ∏ s ∈ Finset.univ.erase τ, (a τ - a s) ∧
    (∀ r : RS a, ev a τ r = 0 → ∃ r', r = lin a τ * r') ∧
    (∃ g : RS a, cofac a τ = algebraMap O (RS a) (ev a τ (cofac a τ)) + lin a τ * g) ∧
    (∀ r : RS a, lin a τ * r = 0 → ∃ c : O, r = algebraMap O (RS a) c * cofac a τ) := by
  intro O _ _ S _ _ a τ
  let pb := AdjoinRoot.powerBasis' (monic_Q a)
  exact ⟨Module.Free.of_basis pb.basis, pb.finite, lin_mul_cofac a τ, ev_cofac a τ,
    exists_lin_mul_of_ev_eq_zero a τ, eq_algebraMap_add_lin_mul a τ (cofac a τ),
    eq_smul_cofac_of_lin_mul_eq_zero a τ⟩

end GlobalTheory.RingFacts
end
end

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoinRootProdLinearFactors_structure : ∀ (O : Type) [CommRing O] [IsDomain O] (S : Type) [Fintype S] [DecidableEq S] (a : S → O) (τ : S), Module.Free O (RS a) ∧ Module.Finite O (RS a) ∧ lin a τ * cofac a τ = 0 ∧ ev a τ (cofac a τ) = ∏ s ∈ Finset.univ.erase τ, (a τ - a s) ∧ (∀ r : RS a, ev a τ r = 0 → ∃ r', r = lin a τ * r') ∧ (∃ g : RS a, cofac a τ = algebraMap O (RS a) (ev a τ (cofac a τ)) + lin a τ * g) ∧ (∀ r : RS a, lin a τ * r = 0 → ∃ c : O, r = algebraMap O (RS a) c * cofac a τ) := by
  atlas_forward_decl GlobalTheory.RingFacts.ring_facts
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

theorem GlobalTheory.herbrand_lattice_facts : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ev a τ (cofac a τ) ≠ 0 ∧ (∀ x : Fin N → RS a, comp a N τ x = 0 ↔ mulR a N (cofac a τ) x = 0) ∧ LinearMap.ker (comp a N τ) = LinearMap.range (mulR a N (lin a τ)) ∧ preEig a Fil τ ⊓ LinearMap.ker (comp a N τ) ≤ Fil.restrictScalars (Int0 v) ∧ (preEig a Fil τ).map (mulR a N (lin a τ)) = filKer a Fil τ ∧ eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ) = ⊥ ∧ (eigSub a τ (Fin N → RS a)).map (comp a N τ) = (⊤ : Submodule (Int0 v) (Fin N → Int0 v)).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) (ev a τ (cofac a τ))) ∧ (preEig a Fil τ).map (proj a Fil) = eigSub a τ ((Fin N → RS a) ⧸ Fil) ∧ eigSub a τ (Fin N → RS a) ≤ preEig a Fil τ ∧ Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ ∧ (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x = 0 → x = 0) ∧ (∃ g : RS a, ∀ x : Fin N → RS a, ev a τ (cofac a τ) • x = cofac a τ • x - g • (lin a τ • x)) := by
  intro C _ v S _ _ a ha N Fil hFil τ
  obtain ⟨hfree, hfin, hlc, hev, hker, ⟨g, hg⟩, hann⟩ := GlobalTheory.T.adjoinRootProdLinearFactors_structure (Int0 v) S a τ
  have hd : ev a τ (cofac a τ) ≠ 0 := by
    rw [hev]
    exact Finset.prod_ne_zero_iff.mpr fun s hs =>
      sub_ne_zero.mpr fun h => Finset.ne_of_mem_erase hs (ha h).symm
  have hid : ∀ x : Fin N → RS a, ev a τ (cofac a τ) • x = cofac a τ • x - g • (lin a τ • x) := by
    intro x
    have : cofac a τ • x = ev a τ (cofac a τ) • x + g • (lin a τ • x) := by
      conv_lhs => rw [hg]
      rw [add_smul, algebraMap_smul, mul_comm, mul_smul]
    rw [this, add_sub_cancel_right]
  have htf : ∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x = 0 → x = 0 := by
    intro c x hc hx
    haveI := hfree
    haveI : Module.IsTorsionFree (Int0 v) (Fin N → RS a) :=
      (Module.Free.chooseBasis (Int0 v) (Fin N → RS a)).isTorsionFree
    exact (smul_eq_zero_iff_right hc).mp hx
  have hcomp0 : ∀ x : Fin N → RS a, comp a N τ x = 0 ↔ ∀ i, ev a τ (x i) = 0 := by
    intro x
    constructor
    · intro h i; exact congrFun h i
    · intro h; funext i; exact h i
  have h2 : ∀ x : Fin N → RS a, comp a N τ x = 0 ↔ mulR a N (cofac a τ) x = 0 := by
    intro x
    rw [hcomp0]
    constructor
    · intro h
      show cofac a τ • x = 0
      funext i
      obtain ⟨r', hr'⟩ := hker _ (h i)
      show cofac a τ * x i = 0
      rw [hr', ← mul_assoc, mul_comm (cofac a τ), hlc, zero_mul]
    · intro h i
      have hi : cofac a τ * x i = 0 := congrFun h i
      have := congrArg (ev a τ) hi
      rw [map_mul, map_zero] at this
      exact (mul_eq_zero.mp this).resolve_left hd
  have h3 : LinearMap.ker (comp a N τ) = LinearMap.range (mulR a N (lin a τ)) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_range, hcomp0]
    constructor
    · intro h
      choose r hr using fun i => hker _ (h i)
      exact ⟨r, funext fun i => (hr i).symm⟩
    · rintro ⟨y, rfl⟩ i
      show ev a τ (lin a τ * y i) = 0
      rw [map_mul, ev_lin, sub_self, zero_mul]
  have hcz : ∀ x : Fin N → RS a, comp a N τ x = 0 → cofac a τ • x = 0 := fun x h => (h2 x).mp h
  refine ⟨hd, h2, h3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htf, ⟨g, hid⟩⟩
  ·
    rintro x ⟨hx1, hx2⟩
    have hx1' : lin a τ • x ∈ Fil := hx1
    have hc : cofac a τ • x = 0 := hcz x hx2
    apply hFil _ x hd
    rw [hid, hc, zero_sub]
    exact Fil.neg_mem (Fil.smul_mem g hx1')
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : lin a τ • x ∈ Fil := hx
      refine ⟨hx', ?_⟩
      show cofac a τ • (lin a τ • x) = 0
      rw [smul_smul, mul_comm, hlc, zero_smul]
    · rintro ⟨hy1, hy2⟩
      have hy2' : mulR a N (cofac a τ) y = 0 := hy2
      have hk : y ∈ LinearMap.ker (comp a N τ) := (h2 y).mpr hy2'
      rw [h3] at hk
      obtain ⟨x, rfl⟩ := hk
      exact ⟨x, hy1, rfl⟩
  · rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hx1' : lin a τ • x = 0 := hx1
    have hc : cofac a τ • x = 0 := hcz x hx2
    have : ev a τ (cofac a τ) • x = 0 := by rw [hid, hc, hx1', smul_zero, sub_zero]
    exact (Submodule.mem_bot _).mpr (htf _ x hd this)
  · ext y
    simp only [Submodule.mem_map, Submodule.mem_top, true_and, LinearMap.lsmul_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : lin a τ • x = 0 := hx
      choose c hc using fun i => hann (x i) (congrFun hx' i)
      refine ⟨c, funext fun i => ?_⟩
      show ev a τ (cofac a τ) * c i = ev a τ (x i)
      rw [hc i, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
    · rintro ⟨c, rfl⟩
      refine ⟨fun i => algebraMap (Int0 v) (RS a) (c i) * cofac a τ, ?_, ?_⟩
      · show lin a τ • (fun i => algebraMap (Int0 v) (RS a) (c i) * cofac a τ) = 0
        funext i
        show lin a τ * (algebraMap (Int0 v) (RS a) (c i) * cofac a τ) = 0
        rw [mul_left_comm, hlc, mul_zero]
      · funext i
        show ev a τ (algebraMap (Int0 v) (RS a) (c i) * cofac a τ) = ev a τ (cofac a τ) * c i
        rw [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
  · ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : lin a τ • x ∈ Fil := hx
      show lin a τ • Fil.mkQ x = 0
      rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx'
    · intro hq
      have hq' : lin a τ • q = 0 := hq
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective Fil q
      refine ⟨x, ?_, rfl⟩
      show lin a τ • x ∈ Fil
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      exact hq'
  · intro x hx
    have hx' : lin a τ • x = 0 := hx
    show lin a τ • x ∈ Fil
    rw [hx']; exact Fil.zero_mem
  · intro x hx
    show lin a τ • x ∈ Fil
    exact Fil.smul_mem _ hx
end

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoinRootProdLinearFactors_lattice_facts : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ev a τ (cofac a τ) ≠ 0 ∧ (∀ x : Fin N → RS a, comp a N τ x = 0 ↔ mulR a N (cofac a τ) x = 0) ∧ LinearMap.ker (comp a N τ) = LinearMap.range (mulR a N (lin a τ)) ∧ preEig a Fil τ ⊓ LinearMap.ker (comp a N τ) ≤ Fil.restrictScalars (Int0 v) ∧ (preEig a Fil τ).map (mulR a N (lin a τ)) = filKer a Fil τ ∧ eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ) = ⊥ ∧ (eigSub a τ (Fin N → RS a)).map (comp a N τ) = (⊤ : Submodule (Int0 v) (Fin N → Int0 v)).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) (ev a τ (cofac a τ))) ∧ (preEig a Fil τ).map (proj a Fil) = eigSub a τ ((Fin N → RS a) ⧸ Fil) ∧ eigSub a τ (Fin N → RS a) ≤ preEig a Fil τ ∧ Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ ∧ (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x = 0 → x = 0) ∧ (∃ g : RS a, ∀ x : Fin N → RS a, ev a τ (cofac a τ) • x = cofac a τ • x - g • (lin a τ • x)) := by
  atlas_forward_decl GlobalTheory.herbrand_lattice_facts
end
