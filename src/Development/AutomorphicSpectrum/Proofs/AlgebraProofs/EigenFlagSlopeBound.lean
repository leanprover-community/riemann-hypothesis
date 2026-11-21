import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeDegreeNeg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LmuNumNonneg
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactFirstTermBundle
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LinearIndependentMapVec
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
import Development.WeilBound.CoreStatements.HodgeTatePoints.ChSplit
import Development.WeilBound.CoreStatements.HodgeTatePoints.EigFrob
import Development.WeilBound.CoreStatements.HodgeTatePoints.DegLeOfEquiv

section
open TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem isSplit_injective_and_exists (O k S : Type) [CommRing O] [Field k] [Fintype S]
    (χ : S → (O →+* k)) (h : IsSplit χ) :
    Function.Injective χ ∧ ∀ ψ : O →+* k, ∃ s, χ s = ψ := by
  classical
  unfold IsSplit at h
  set F := Algebra.TensorProduct.lift (Algebra.ofId k (S → k))
    (Pi.algHom ℤ (fun _ : S => k) fun s => (χ s).toIntAlgHom)
    (fun _ _ => Commute.all _ _) with hF
  have hv : ∀ (a : k) (x : O) (s : S), F (a ⊗ₜ[ℤ] x) s = a * χ s x := by
    intro a x s
    simp [hF, Algebra.ofId_apply]
  constructor
  · intro s t hst
    by_contra hne
    obtain ⟨y, hy⟩ := h.2 (Pi.single s 1)
    have key : ∀ y : TensorProduct ℤ k O, F y s = F y t := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => rw [hv, hv, hst]
      | add u v hu hv' => simp [map_add, hu, hv']
    have h1 := key y
    rw [hy] at h1
    simp [Pi.single_apply, Ne.symm hne] at h1
  · intro ψ
    let Ψ : TensorProduct ℤ k O →ₐ[k] k :=
      Algebra.TensorProduct.lift (AlgHom.id k k) ψ.toIntAlgHom (fun _ _ => Commute.all _ _)
    choose y hy using fun s => h.2 (Pi.single s (1 : k))
    have hsum : ∑ s, y s = 1 := by
      apply h.1
      rw [map_sum, map_one]
      simp only [hy]
      ext t
      simp [Finset.sum_apply, Pi.single_apply]
    have hne : ∑ s, Ψ (y s) ≠ 0 := by
      rw [← map_sum, hsum, map_one]
      exact one_ne_zero
    obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    refine ⟨s, ?_⟩
    have hmul : ∀ z, z * y s = (F z s) • y s := by
      intro z
      apply h.1
      rw [map_mul, map_smul, hy]
      ext t
      by_cases hts : t = s
      · subst hts
        simp
      · simp [Pi.single_apply, hts]
    ext o
    have h1 := congrArg Ψ (hmul ((1 : k) ⊗ₜ[ℤ] o))
    have h2 : Ψ ((1 : k) ⊗ₜ[ℤ] o) = ψ o := by
      simp [Ψ]
    rw [map_mul, map_smul, hv, h2, smul_eq_mul, one_mul] at h1
    exact (mul_right_cancel₀ hs h1).symm

end GlobalTheory.CompanionTheory.Ar.Crv
end

section
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem eigen_ses_subDeg : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ (ρ : O → V →ₗ[K] V) (ρ' : O →+* Module.End K V') (ρ'' : O → V'' →ₗ[K] V''), IsBun C L' → (∀ a, IsHom C L' L' (ρ' a)) → ShortExact C L L' L'' f g → (∀ a x, f (ρ a x) = ρ' a (f x)) → (∀ a y, g (ρ' a y) = ρ'' a (g y)) → ∀ s, subDeg C L' (eig (fun a => ρ' a) (fun a => algebraMap k K (χ s a))) = subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) + subDeg C L'' (eig (fun a => ρ'' a) (fun a => algebraMap k K (χ s a))) :=
  @PositivityTheory.HtPt.Ch.split_ses

end GlobalTheory.CompanionTheory.Ar.Crv
end

open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_exact_eigen_sub_degree : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ (ρ : O → V →ₗ[K] V) (ρ' : O →+* Module.End K V') (ρ'' : O → V'' →ₗ[K] V''), IsBun C L' → (∀ a, IsHom C L' L' (ρ' a)) → ShortExact C L L' L'' f g → (∀ a x, f (ρ a x) = ρ' a (f x)) → (∀ a y, g (ρ' a y) = ρ'' a (g y)) → ∀ s, subDeg C L' (eig (fun a => ρ' a) (fun a => algebraMap k K (χ s a))) = subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) + subDeg C L'' (eig (fun a => ρ'' a) (fun a => algebraMap k K (χ s a))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.eigen_ses_subDeg
end

section
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem eig_frobenius_twist : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) (ρ : O → Matrix (Fin d) (Fin d) K) (χ : O → K), eig (fun a => Matrix.toLin' ((ρ a).map (· ^ p))) (fun a => χ a ^ p) = frobSub p (eig (fun a => Matrix.toLin' (ρ a)) χ) :=
  PositivityTheory.HtPt.Ci.eig_frob

end GlobalTheory.CompanionTheory.Ar.Crv
end

open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenspace_frobenius_twist : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) (ρ : O → Matrix (Fin d) (Fin d) K) (χ : O → K), eig (fun a => Matrix.toLin' ((ρ a).map (· ^ p))) (fun a => χ a ^ p) = frobSub p (eig (fun a => Matrix.toLin' (ρ a)) χ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.eig_frobenius_twist
end

section
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.EigDual

theorem eig_dual_deg : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Matrix (Fin d) (Fin d) K, IsBun C L → (∀ a, IsHom C L L (Matrix.toLin' (ρ a))) → ∀ s, subDeg C (dotDual C L) (eig (fun a => Matrix.toLin' (ρ a).transpose) (fun a => algebraMap k K (χ s a))) = - subDeg C L (eig (fun a => Matrix.toLin' (ρ a)) (fun a => algebraMap k K (χ s a))) :=
  PositivityTheory.HtPt.Ci.eig_dual

end GlobalTheory.CompanionTheory.Ar.Crv.EigDual
end

open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_eigen_sub_degree_transpose : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Matrix (Fin d) (Fin d) K, IsBun C L → (∀ a, IsHom C L L (Matrix.toLin' (ρ a))) → ∀ s, subDeg C (dotDual C L) (eig (fun a => Matrix.toLin' (ρ a).transpose) (fun a => algebraMap k K (χ s a))) = - subDeg C L (eig (fun a => Matrix.toLin' (ρ a)) (fun a => algebraMap k K (χ s a))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.EigDual.eig_dual_deg
end

section
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.ConjEq

theorem eq_zero_of_scale {S : Type} [Finite S] (h : S → ℤ) (p : ℕ) (hp : 2 ≤ p)
    (H : ∀ s, ∃ u, h u = p * h s) (s : S) : h s = 0 := by
  haveI : Nonempty S := ⟨s⟩
  obtain ⟨m, hm⟩ := Finite.exists_max (fun s => |h s|)
  obtain ⟨u, hu⟩ := H m
  have h1 : |h u| = p * |h m| := by
    rw [hu, abs_mul, Nat.abs_cast]
  have h2 : |h u| ≤ |h m| := hm u
  have h3 : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have h4 : |h m| = 0 := by
    have h5 : 0 ≤ |h m| := abs_nonneg _
    nlinarith
  have h6 : |h s| ≤ 0 := h4 ▸ hm s
  exact abs_eq_zero.1 (le_antisymm h6 (abs_nonneg _))

variable {K : Type} [Field K]

theorem eig_star {O V : Type} [CommRing O] [StarRing O] [AddCommGroup V] [Module K V]
    (ρ : O → V →ₗ[K] V) (χ χ' : O → K) (h : ∀ a, χ' a = χ (star a)) :
    eig (fun a => ρ (star a)) χ = eig ρ χ' := by
  ext x
  simp only [eig, Submodule.mem_iInf]
  constructor
  · intro H a
    have := H (star a)
    rwa [star_star, ← h] at this
  · intro H a
    have := H (star a)
    rwa [h, star_star] at this

section Data

variable (C : ACurve K) {p : ℕ} {O : Type} [CommRing O] [StarRing O] {d : ℕ}
  (D : ConjData C p O d)

theorem lie_hom (a : O) : IsHom C D.lie D.lie (Matrix.toLin' (D.ρ a)) := by
  intro i x hx
  obtain ⟨y, hy, rfl⟩ := (D.hodge.2.2.2.2 i x).1 hx
  refine (D.hodge.2.2.2.2 i _).2 ⟨D.ρH a y, D.ρH_hom a i y hy, ?_⟩
  simpa using D.ρH_fst a y

theorem dual_bun : IsBun C (dotDual C D.lie) :=
  (deg_shortExact K C _ _ _ _ _ _ _ _ D.H_bun D.hodge).1

variable {k S : Type} [Field k] [Algebra k K] [Fintype S] (χ : S → (O →+* k))

theorem hodge_eq (hχ : IsSplit χ) (hk : ∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) (s t : S)
    (hst : ∀ a, χ t a = χ s (star a)) :
    subDeg C D.H (eig (fun a => D.ρH a) (fun a => algebraMap k K (χ s a))) =
      subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) -
      subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a))) := by
  classical
  have h1 := GlobalTheory.T.short_exact_eigen_sub_degree K C _ _ _ (dotDual C D.lie) D.H D.lie (LinearMap.inr K _ _)
    (LinearMap.fst K _ _) O k S χ hχ hk (fun a => Matrix.toLin' (D.ρ (star a)).transpose) D.ρH
    (fun a => Matrix.toLin' (D.ρ a)) D.H_bun D.ρH_hom D.hodge
    (fun a x => by simpa using (D.ρH_inr a x).symm) (fun a y => by simpa using D.ρH_fst a y) s
  have h2 := eig_star (K := K) (fun a => Matrix.toLin' (D.ρ a).transpose)
    (fun a => algebraMap k K (χ s a)) (fun a => algebraMap k K (χ t a))
    (fun a => by rw [hst])
  have h3 := GlobalTheory.T.dual_eigen_sub_degree_transpose K C d D.lie O k S χ hχ hk D.ρ D.lie_bun (lie_hom C D) t
  rw [h1, h2, h3]
  ring

theorem conj_eq [Fact p.Prime] [CharP K p] (hχ : IsSplit χ)
    (hk : ∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) (s t u : S)
    (hst : ∀ a, χ t a = χ s (star a)) (hu : ∀ a, χ u a = χ s a ^ p) :
    subDeg C D.H (eig (fun a => D.ρH a) (fun a => algebraMap k K (χ u a))) =
      p * (subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) -
      subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a)))) := by
  classical
  have h1 := GlobalTheory.T.short_exact_eigen_sub_degree K C _ _ _ (frobLat C p D.lie) D.H (frobLat C p (dotDual C D.lie))
    D.α D.β O k S χ hχ hk (fun a => Matrix.toLin' ((D.ρ a).map (· ^ p))) D.ρH
    (fun a => Matrix.toLin' ((D.ρ (star a)).transpose.map (· ^ p))) D.H_bun D.ρH_hom D.conj
    (fun a x => by simpa using D.α_act a x) (fun a y => by simpa using D.β_act a y) u
  have hc : (fun a => algebraMap k K (χ u a)) = fun a => algebraMap k K (χ s a) ^ p := by
    funext a
    rw [hu, map_pow]
  have h2 := GlobalTheory.T.eigenspace_frobenius_twist K p d O (fun a => D.ρ a) (fun a => algebraMap k K (χ s a))
  have h3 := GlobalTheory.T.eigenspace_frobenius_twist K p d O (fun a => (D.ρ (star a)).transpose)
    (fun a => algebraMap k K (χ s a))
  have h4 := eig_star (K := K) (fun a => Matrix.toLin' (D.ρ a).transpose)
    (fun a => algebraMap k K (χ s a)) (fun a => algebraMap k K (χ t a))
    (fun a => by rw [hst])
  have h5 := GlobalTheory.T.dual_eigen_sub_degree_transpose K C d D.lie O k S χ hχ hk D.ρ D.lie_bun (lie_hom C D) t
  rw [h1, hc, h2, h3, SubFrob.subDeg_frob K C p d _ _ D.lie_bun,
    SubFrob.subDeg_frob K C p d _ _ (dual_bun C D), h4, h5]
  ring

end Data

theorem subDeg_eig_conj : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O k S : Type) [CommRing O] [StarRing O] [Field k] [Algebra k K] [Fintype S] (χ : S → (O →+* k)) (d : ℕ) (D : ConjData C p O d), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ s t : S, (∀ a, χ t a = χ s (star a)) → subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) = subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a))) := by
  intro K _ C p _ _ O k S _ _ _ _ _ χ d D hχ hk s t hst
  have hp : p.Prime := Fact.out
  haveI : CharP k p := (algebraMap k K).charP (algebraMap k K).injective p
  haveI : ExpChar k p := ExpChar.prime hp
  have hall := (isSplit_injective_and_exists O k S χ hχ).2
  have hconj : ∀ s, ∃ t, ∀ a, χ t a = χ s (star a) := fun s => by
    obtain ⟨t, ht⟩ := hall ((χ s).comp (starRingEnd O))
    exact ⟨t, fun a => by rw [ht]; rfl⟩
  have hfrob : ∀ s, ∃ u, ∀ a, χ u a = χ s a ^ p := fun s => by
    obtain ⟨u, hu⟩ := hall ((frobenius k p).comp (χ s))
    exact ⟨u, fun a => by rw [hu]; rfl⟩
  have hzero := eq_zero_of_scale
    (fun s => subDeg C D.H (eig (fun a => D.ρH a) (fun a => algebraMap k K (χ s a))))
    p hp.two_le (fun s => by
      obtain ⟨t, ht⟩ := hconj s
      obtain ⟨u, hu⟩ := hfrob s
      refine ⟨u, ?_⟩
      rw [conj_eq C D χ hχ hk s t u ht hu, hodge_eq C D χ hχ hk s t ht]) s
  have h := hodge_eq C D χ hχ hk s t hst
  rw [hzero] at h
  exact sub_eq_zero.1 h.symm

end GlobalTheory.CompanionTheory.Ar.Crv.ConjEq
end

open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_eigen_sub_degree_eq : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O k S : Type) [CommRing O] [StarRing O] [Field k] [Algebra k K] [Fintype S] (χ : S → (O →+* k)) (d : ℕ) (D : ConjData C p O d), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ s t : S, (∀ a, χ t a = χ s (star a)) → subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) = subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.ConjEq.subDeg_eig_conj
end

section
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem subDeg_le_map_of_injective : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (f : V →ₗ[K] V') (W : Submodule K V), IsBun C L → IsBun C L' → Function.Injective f → IsHom C L L' f → subDeg C L W ≤ subDeg C L' (W.map f) :=
  PositivityTheory.HtPt.Ch.deg_inj

end GlobalTheory.CompanionTheory.Ar.Crv
end

open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_degree_mono_injective_hom : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (f : V →ₗ[K] V') (W : Submodule K V), IsBun C L → IsBun C L' → Function.Injective f → IsHom C L L' f → subDeg C L W ≤ subDeg C L' (W.map f) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_map_of_injective
end

section
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem deg_le_deg_of_le : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L L' : C.I → AddSubgroup V), IsBun C L → IsBun C L' → (∀ i, L i ≤ L' i) → deg C L ≤ deg C L' :=
  @PositivityTheory.HtPt.Ch.deg_mono

end GlobalTheory.CompanionTheory.Ar.Crv
end

open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_mono_lattice_le : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L L' : C.I → AddSubgroup V), IsBun C L → IsBun C L' → (∀ i, L i ≤ L' i) → deg C L ≤ deg C L' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.deg_le_deg_of_le
end

section
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem subDeg_le_zero_of_trivial : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ) (b : Module.Basis (Fin n) K V) (L : C.I → AddSubgroup V) (W : Submodule K V), (∀ i, IsLatOf C i b (L i)) → subDeg C L W ≤ 0 :=
  @PositivityTheory.HtPt.Ch.subdeg_trivial

end GlobalTheory.CompanionTheory.Ar.Crv
end

open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_degree_nonpos_trivial_lattice : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ) (b : Module.Basis (Fin n) K V) (L : C.I → AddSubgroup V) (W : Submodule K V), (∀ i, IsLatOf C i b (L i)) → subDeg C L W ≤ 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_zero_of_trivial
end

section
section
noncomputable section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubdegMax

variable {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]

def latOf (i : C.I) {n : ℕ} (b : Module.Basis (Fin n) K V) : AddSubgroup V where
  carrier := {x | ∀ q, C.v i (b.repr x q) ≤ 1}
  zero_mem' := fun q => by simp
  add_mem' := fun {x y} hx hy q => by
    rw [map_add, Finsupp.add_apply]; exact (C.v i).map_add_le (hx q) (hy q)
  neg_mem' := fun {x} hx q => by
    rw [map_neg, Finsupp.neg_apply, Valuation.map_neg]; exact hx q

theorem isLatOf_latOf (i : C.I) {n : ℕ} (b : Module.Basis (Fin n) K V) :
    IsLatOf C i b (latOf C i b) := fun _ => Iff.rfl

def scale (L : C.I → AddSubgroup V) (c : C.I → Kˣ) : C.I → AddSubgroup V :=
  fun i => (L i).comap (DistribSMul.toAddMonoidHom V (((c i)⁻¹ : Kˣ) : K))

theorem mem_scale (L : C.I → AddSubgroup V) (c : C.I → Kˣ) (i : C.I) (x : V) :
    x ∈ scale C L c i ↔ (((c i)⁻¹ : Kˣ) : K) • x ∈ L i := Iff.rfl

theorem isLatOf_scale {L : C.I → AddSubgroup V} (c : C.I → Kˣ) {i : C.I} {n : ℕ}
    {b : Module.Basis (Fin n) K V} (h : IsLatOf C i b (L i)) :
    IsLatOf C i (b.unitsSMul fun _ => c i) (scale C L c i) := by
  intro x
  rw [mem_scale, h]
  refine forall_congr' fun q => ?_
  rw [Module.Basis.repr_unitsSMul, map_smul, Finsupp.smul_apply]
  rfl

theorem isBun_scale {L : C.I → AddSubgroup V} (c : C.I → Kˣ) (hc : {i | c i ≠ 1}.Finite)
    (h : IsBun C L) : IsBun C (scale C L c) := by
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := h.1 i
    exact ⟨_, isLatOf_scale C c hb⟩
  · obtain ⟨b, hb⟩ := h.2
    refine ⟨b, (hb.union hc).subset fun i hi => ?_⟩
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn hi
    apply hi
    intro x
    rw [mem_scale, hn.2, inv_one, Units.val_one, one_smul]
    exact hn.1 x

theorem deg_scale [FiniteDimensional K V] {L : C.I → AddSubgroup V} (c : C.I → Kˣ)
    (hc : {i | c i ≠ 1}.Finite) (h : IsBun C L) :
    deg C (scale C L c) = deg C L +
      (Module.finrank K V : ℤ) * ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (c i)) := by
  choose b hb using h.1
  obtain ⟨hf, e⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L _ (Module.finBasis K V) b h hb
  obtain ⟨-, e'⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C V (scale C L c) _ (Module.finBasis K V)
    (fun i => (b i).unitsSMul fun _ => c i) (isBun_scale C c hc h)
    (fun i => isLatOf_scale C c (hb i))
  have hs1 : (Function.support fun i =>
      (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i)))).Finite := by
    refine hf.subset fun i hi => ?_
    intro h1
    exact hi (by simp [h1])
  have hs3 : (Function.support fun i => (Module.finrank K V : ℤ) *
      ((C.w i : ℤ) * WithZero.log (C.v i (c i)))).Finite := by
    refine hc.subset fun i hi => ?_
    intro h1
    exact hi (by simp [h1])
  rw [e, e', mul_finsum, ← finsum_add_distrib hs1 hs3]
  refine finsum_congr fun i => ?_
  have hd : (Module.finBasis K V).det ((b i).unitsSMul fun _ => c i) =
      (c i : K) ^ Module.finrank K V * (Module.finBasis K V).det (b i) := by
    have : ⇑((b i).unitsSMul fun _ => c i) = fun j => (c i : K) • b i j := by
      funext j; rw [Module.Basis.unitsSMul_apply]; rfl
    rw [this]
    have := (Module.finBasis K V).det.toMultilinearMap.map_smul_univ (fun _ => (c i : K)) (b i)
    simpa using this
  have h0 : C.v i ((Module.finBasis K V).det (b i)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact ((Module.finBasis K V).isUnit_det (b i)).ne_zero
  have h1 : C.v i (c i) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact (c i).ne_zero
  rw [hd, map_mul, map_pow, WithZero.log_mul (pow_ne_zero _ h1) h0, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

theorem exists_scale (i : C.I) {n m : ℕ} (b : Module.Basis (Fin n) K V)
    {b' : Module.Basis (Fin m) K V} {L : AddSubgroup V} (h : IsLatOf C i b' L) :
    ∃ c : Kˣ, 1 ≤ C.v i c ∧ ∀ x ∈ L, ((c⁻¹ : Kˣ) : K) • x ∈ latOf C i b := by
  classical
  obtain ⟨c, -, hc⟩ := Finset.exists_max_image
    (insert (1 : K) (Finset.univ.image fun p : Fin m × Fin n => b.repr (b' p.1) p.2))
    (C.v i) (Finset.insert_nonempty _ _)
  have h1 : 1 ≤ C.v i c := by simpa using hc 1 (Finset.mem_insert_self _ _)
  have hpos : 0 < C.v i c := lt_of_lt_of_le zero_lt_one h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hpos
  refine ⟨Units.mk0 c hc0, h1, fun x hx q => ?_⟩
  have hle : C.v i (b.repr x q) ≤ C.v i c := by
    have hx' : b.repr x q = ∑ j, b'.repr x j * b.repr (b' j) q := by
      conv_lhs => rw [← b'.sum_repr x]
      rw [map_sum, Finsupp.finset_sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [hx']
    refine (C.v i).map_sum_le fun j _ => ?_
    rw [map_mul]
    calc _ ≤ 1 * C.v i c := mul_le_mul' ((h x).1 hx j)
          (hc _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(j, q), Finset.mem_univ _, rfl⟩)))
      _ = _ := one_mul _
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, Units.val_mk0,
    map_inv₀, inv_mul_le_iff₀ hpos, mul_one]
  exact hle

theorem subDeg_bot [FiniteDimensional K V] (L : C.I → AddSubgroup V) : subDeg C L ⊥ = 0 := by
  unfold subDeg deg
  have : IsEmpty (Fin (Module.finrank K (⊥ : Submodule K V))) := by
    rw [finrank_bot]; infer_instance
  refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
  simp [Module.Basis.det_apply]

theorem subDeg_bdd [FiniteDimensional K V] (L : C.I → AddSubgroup V) (h : IsBun C L) :
    ∃ B : ℤ, ∀ W : Submodule K V, subDeg C L W ≤ B := by
  classical
  obtain ⟨b, hb⟩ := h.2
  have key : ∀ i, ∃ c : Kˣ, (IsLatOf C i b (L i) → c = 1) ∧ 1 ≤ C.v i c ∧
      ∀ x ∈ L i, ((c⁻¹ : Kˣ) : K) • x ∈ latOf C i b := by
    intro i
    by_cases hi : IsLatOf C i b (L i)
    · refine ⟨1, fun _ => rfl, by simp, fun x hx => ?_⟩
      rw [inv_one, Units.val_one, one_smul]
      exact (hi x).1 hx
    · obtain ⟨b', hb'⟩ := h.1 i
      obtain ⟨c, h1, h2⟩ := exists_scale C i b hb'
      exact ⟨c, fun h' => absurd h' hi, h1, h2⟩
  choose c hc1 hc2 hc3 using key
  have hc : {i | c i ≠ 1}.Finite := hb.subset fun i hi h' => hi (hc1 i h')
  have h0 : IsBun C (fun i => latOf C i b) :=
    ⟨fun i => ⟨b, isLatOf_latOf C i b⟩, b, by simp [isLatOf_latOf]⟩
  set S : ℤ := ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (c i)) with hS
  have hS0 : 0 ≤ S := by
    refine finsum_nonneg fun i => mul_nonneg (Int.natCast_nonneg _) ?_
    have h1 : C.v i (c i) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact (c i).ne_zero
    have := (WithZero.log_le_log one_ne_zero h1).2 (hc2 i)
    simpa using this
  refine ⟨(Module.finrank K V : ℤ) * S, fun W => ?_⟩
  have hW := (GlobalTheory.T.sub_and_quotient_bundles K C V _ W h0).1
  have e1 := GlobalTheory.T.degree_mono_lattice_le K C W (sub C L W) (scale C (sub C (fun i => latOf C i b) W) c)
    (GlobalTheory.T.sub_and_quotient_bundles K C V _ W h).1 (isBun_scale C c hc hW) (fun i x hx => hc3 i x hx)
  have e2 := deg_scale C c hc hW
  have e3 := GlobalTheory.T.sub_degree_nonpos_trivial_lattice K C V _ b (fun i => latOf C i b) W (fun i => isLatOf_latOf C i b)
  have e4 : (Module.finrank K W : ℤ) * S ≤ (Module.finrank K V : ℤ) * S :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast W.finrank_le) hS0
  unfold subDeg at e3 ⊢
  rw [← hS] at e2
  linarith

theorem subDeg_max : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (L : C.I → AddSubgroup V), IsBun C L →
    subDeg C L ⊥ = 0 ∧ ∃ W₀ : Submodule K V, ∀ W : Submodule K V, subDeg C L W ≤ subDeg C L W₀ := by
  intro K _ C V _ _ _ L h
  refine ⟨subDeg_bot C L, ?_⟩
  obtain ⟨B, hB⟩ := subDeg_bdd C L h
  obtain ⟨z, ⟨W₀, rfl⟩, hz⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ W : Submodule K V, subDeg C L W = z)
    ⟨B, by rintro _ ⟨W, rfl⟩; exact hB W⟩ ⟨_, ⊥, rfl⟩
  exact ⟨W₀, fun W => hz _ ⟨W, rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.Crv.SubdegMax
end
end

open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_degree_bot_and_max_exists : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V), IsBun C L → subDeg C L ⊥ = 0 ∧ ∃ W₀ : Submodule K V, ∀ W : Submodule K V, subDeg C L W ≤ subDeg C L W₀ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.SubdegMax.subDeg_max
end

section
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubDegSes

theorem subDeg_ses : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (X : Submodule K V'), IsBun C L' → ShortExact C L L' L'' f g → subDeg C L' X ≤ subDeg C L (X.comap f) + subDeg C L'' (X.map g) :=
  @PositivityTheory.HtPt.Ch.subdeg_ses

end GlobalTheory.CompanionTheory.Ar.Crv.SubDegSes
end

open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_exact_sub_degree_bound : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (X : Submodule K V'), IsBun C L' → ShortExact C L L' L'' f g → subDeg C L' X ≤ subDeg C L (X.comap f) + subDeg C L'' (X.map g) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.SubDegSes.subDeg_ses
end

section
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem subDeg_dotDual_orth : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W X : Submodule K (Fin d → K)), IsBun C L → (∀ u, u ∈ W ↔ ∀ φ ∈ X, u ⬝ᵥ φ = 0) → subDeg C (dotDual C L) X = deg C (dotDual C L) + subDeg C L W :=
  PositivityTheory.HtPt.Ch.subdeg_orth

end GlobalTheory.CompanionTheory.Ar.Crv
end

open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dot_dual_sub_degree_annihilator : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W X : Submodule K (Fin d → K)), IsBun C L → (∀ u, u ∈ W ↔ ∀ φ ∈ X, u ⬝ᵥ φ = 0) → subDeg C (dotDual C L) X = deg C (dotDual C L) + subDeg C L W := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.subDeg_dotDual_orth
end

section
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.FrobEst

def dotOrth {K : Type} [Field K] {d : ℕ} (X : Submodule K (Fin d → K)) :
    Submodule K (Fin d → K) where
  carrier := {u | ∀ φ ∈ X, u ⬝ᵥ φ = 0}
  add_mem' := fun {a b} ha hb φ hφ => by rw [add_dotProduct, ha φ hφ, hb φ hφ, add_zero]
  zero_mem' := fun φ _ => zero_dotProduct φ
  smul_mem' := fun c u hu φ hφ => by rw [smul_dotProduct, hu φ hφ, smul_zero]

theorem frob_estimate : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]
    (O : Type) [CommRing O] [StarRing O] (d : ℕ) (D : ConjData C p O d), 2 < p →
    0 ≤ deg C (dotDual C D.lie) ∧
      ∀ W : Submodule K (Fin d → K),
        ((p : ℤ) - 2) * subDeg C D.lie W ≤ deg C (dotDual C D.lie) := by
  intro K _ C p _ _ O _ _ d D hp
  obtain ⟨h0, W₀, hW₀⟩ := GlobalTheory.T.sub_degree_bot_and_max_exists K C (Fin d → K) D.lie D.lie_bun
  have hp2 : (0 : ℤ) < (p : ℤ) - 2 := by
    have : (2 : ℤ) < (p : ℤ) := by exact_mod_cast hp
    linarith
  have hf := GlobalTheory.CompanionTheory.Ar.Crv.SubFrob.subDeg_frob K C p d D.lie W₀ D.lie_bun
  have h1 := GlobalTheory.T.sub_degree_mono_injective_hom K C (Fin d → K) ((Fin d → K) × (Fin d → K))
    (frobLat C p D.lie) D.H D.α (frobSub p W₀)
    (GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat K C p d D.lie D.lie_bun).1 D.H_bun D.conj.1
    (fun i x hx => (D.conj.2.2.2.1 i x).1 hx)
  have h2 := GlobalTheory.T.short_exact_sub_degree_bound K C (Fin d → K) ((Fin d → K) × (Fin d → K)) (Fin d → K)
    (dotDual C D.lie) D.H D.lie (LinearMap.inr K (Fin d → K) (Fin d → K))
    (LinearMap.fst K (Fin d → K) (Fin d → K)) (Submodule.map D.α (frobSub p W₀)) D.H_bun D.hodge
  have h3 := GlobalTheory.T.dot_dual_sub_degree_annihilator K C d D.lie
    (dotOrth (Submodule.comap (LinearMap.inr K (Fin d → K) (Fin d → K))
      (Submodule.map D.α (frobSub p W₀))))
    (Submodule.comap (LinearMap.inr K (Fin d → K) (Fin d → K))
      (Submodule.map D.α (frobSub p W₀))) D.lie_bun (fun u => Iff.rfl)
  have h4 := hW₀ (Submodule.map (LinearMap.fst K (Fin d → K) (Fin d → K))
    (Submodule.map D.α (frobSub p W₀)))
  have h5 := hW₀ (dotOrth (Submodule.comap (LinearMap.inr K (Fin d → K) (Fin d → K))
    (Submodule.map D.α (frobSub p W₀))))
  have hr : ((p : ℤ) - 2) * subDeg C D.lie W₀ = (p : ℤ) * subDeg C D.lie W₀ - 2 * subDeg C D.lie W₀ := by
    ring
  have key : ((p : ℤ) - 2) * subDeg C D.lie W₀ ≤ deg C (dotDual C D.lie) := by
    linarith
  have hμ : 0 ≤ subDeg C D.lie W₀ := by
    have := hW₀ ⊥
    linarith
  refine ⟨?_, fun W => ?_⟩
  · have := mul_nonneg hp2.le hμ
    linarith
  · have := mul_le_mul_of_nonneg_left (hW₀ W) hp2.le
    linarith

end GlobalTheory.CompanionTheory.Ar.Crv.FrobEst
end

open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_sub_degree_bound_by_dual : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O : Type) [CommRing O] [StarRing O] (d : ℕ) (D : ConjData C p O d), 2 < p → 0 ≤ deg C (dotDual C D.lie) ∧ ∀ W : Submodule K (Fin d → K), ((p : ℤ) - 2) * subDeg C D.lie W ≤ deg C (dotDual C D.lie) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.FrobEst.frob_estimate
end

section
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem degree_eq_sum_eigen : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Module.End K V, IsBun C L → (∀ a, IsHom C L L (ρ a)) → deg C L = ∑ s, subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) :=
  @PositivityTheory.HtPt.Ch.split_deg

end GlobalTheory.CompanionTheory.Ar.Crv
end

open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_sum_eigen_sub_degrees : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Module.End K V, IsBun C L → (∀ a, IsHom C L L (ρ a)) → deg C L = ∑ s, subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.degree_eq_sum_eigen
end

section
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.LmuDeg

theorem dot_bijective (K : Type) [Field K] (d : ℕ) :
    Function.Bijective
      (dotProductBilin K K : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K) := by
  have hi : Function.Injective
      (dotProductBilin K K : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    funext r
    have := LinearMap.congr_fun hx (Pi.single r 1)
    simpa [dotProductBilin_apply_apply] using this
  refine ⟨hi, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    simp [Subspace.dual_finrank_eq])).1 hi

noncomputable def endAct {K : Type} [Field K] {O : Type} [CommRing O] {d : ℕ}
    (ρ : O →+* Matrix (Fin d) (Fin d) K) : O →+* Module.End K (Fin d → K) where
  toFun a := Matrix.toLin' (ρ a)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' a b := by simp [Matrix.toLin'_mul, Module.End.mul_eq_comp]
  map_zero' := by simp
  map_add' a b := by simp

theorem isHom_lie {K : Type} [Field K] {C : ACurve K} {p : ℕ} {O : Type} [CommRing O] [StarRing O]
    {d : ℕ} (D : ConjData C p O d) (a : O) : IsHom C D.lie D.lie (endAct D.ρ a) := by
  intro i x hx
  obtain ⟨y, hy, rfl⟩ := (D.hodge.2.2.2.2 i x).1 hx
  have h2 : (D.ρH a y).1 ∈ D.lie i :=
    (D.hodge.2.2.2.2 i _).2 ⟨_, D.ρH_hom a i y hy, rfl⟩
  rw [D.ρH_fst] at h2
  simpa [endAct] using h2

theorem lmuNum_nonneg_of_conjData : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O k S T : Type) [CommRing O] [StarRing O] [Field k] [Algebra k K] [Fintype S] [Fintype T] (χ : S → (O →+* k)) (d : ℕ) (D : ConjData C p O d) (ι κ : T → S) (j q : ℕ) (μ : T → ℕ → ℝ) (W L : T → ℕ → Submodule K (Fin d → K)), 2 < p → IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → Function.Bijective (Sum.elim ι κ) → (∀ τ a, χ (κ τ) a = χ (ι τ) (star a)) → 1 ≤ j → 1 ≤ q → (∀ τ, W τ 0 = ⊥) → (∀ τ, L τ 0 = ⊥) → (∀ τ, W τ j = (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ (ι τ) a)))) → (∀ τ, L τ q = (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ (κ τ) a)))) → GapCond p j q μ → 0 ≤ lmuNum j q μ (fun τ i => (subDeg C D.lie (W τ i) : ℝ)) (fun τ i => (subDeg C D.lie (L τ i) : ℝ)) := by
  intro K _ C p _ _ O k S T _ _ _ _ _ _ χ d D ι κ j q μ W L hp hs hc hbij hconj hj hq hW0 hL0 hWj hLq hgap
  classical
  obtain ⟨hbot, W₀, hW₀⟩ := GlobalTheory.T.sub_degree_bot_and_max_exists K C (Fin d → K) D.lie D.lie_bun
  obtain ⟨he0, hC2⟩ := GlobalTheory.T.lie_sub_degree_bound_by_dual K C p O d D hp
  have hsplit : deg C D.lie = ∑ s, subDeg C D.lie
      (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) :=
    GlobalTheory.T.degree_sum_eigen_sub_degrees K C (Fin d → K) D.lie O k S χ hs hc (endAct D.ρ) D.lie_bun (isHom_lie D)
  have hdual : deg C (dotDual C D.lie) = - deg C D.lie :=
    (GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual K C (Fin d → K) (Fin d → K) D.lie (dotProductBilin K K)
      D.lie_bun (dot_bijective K d)).2.1
  have hC1 : ∀ τ, subDeg C D.lie (W τ j) = subDeg C D.lie (L τ q) := by
    intro τ
    rw [hWj, hLq]
    exact GlobalTheory.T.conjugate_eigen_sub_degree_eq K C p O k S χ d D hs hc (ι τ) (κ τ) (hconj τ)
  have hsum : deg C D.lie = 2 * ∑ τ, subDeg C D.lie (W τ j) := by
    rw [hsplit, ← (Equiv.ofBijective _ hbij).sum_comp, Fintype.sum_sum_type, two_mul]
    simp only [Equiv.ofBijective_apply, Sum.elim_inl, Sum.elim_inr]
    congr 1
    · exact Finset.sum_congr rfl fun τ _ => by rw [hWj]
    · exact Finset.sum_congr rfl fun τ _ => by rw [hC1, hLq]
  refine GlobalTheory.CompanionTheory.Ar.Crv.Chain.lmuNum_nonneg T p j q μ _ _ (subDeg C D.lie W₀ : ℝ)
    (deg C (dotDual C D.lie) : ℝ) hp hj hq hgap ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro τ; simp [hW0, hbot]
  · intro τ; simp [hL0, hbot]
  · intro τ i _; exact_mod_cast hW₀ _
  · intro τ i _; exact_mod_cast hW₀ _
  · intro τ; exact_mod_cast hC1 τ
  · rw [hdual, hsum]; push_cast; ring
  · exact_mod_cast hC2 W₀
  · exact_mod_cast he0

end GlobalTheory.CompanionTheory.Ar.Crv.LmuDeg
end

open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_flag_slope_bound : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O k S T : Type) [CommRing O] [StarRing O] [Field k] [Algebra k K] [Fintype S] [Fintype T] (χ : S → (O →+* k)) (d : ℕ) (D : ConjData C p O d) (ι κ : T → S) (j q : ℕ) (μ : T → ℕ → ℝ) (W L : T → ℕ → Submodule K (Fin d → K)), 2 < p → IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → Function.Bijective (Sum.elim ι κ) → (∀ τ a, χ (κ τ) a = χ (ι τ) (star a)) → 1 ≤ j → 1 ≤ q → (∀ τ, W τ 0 = ⊥) → (∀ τ, L τ 0 = ⊥) → (∀ τ, W τ j = (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ (ι τ) a)))) → (∀ τ, L τ q = (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ (κ τ) a)))) → GapCond p j q μ → 0 ≤ lmuNum j q μ (fun τ i => (subDeg C D.lie (W τ i) : ℝ)) (fun τ i => (subDeg C D.lie (L τ i) : ℝ)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.LmuDeg.lmuNum_nonneg_of_conjData
end
