import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleFunctorExactOnLattices
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneWittTensorLatticeSurjectiveFixed
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingFreeOverFrobeniusImage
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInter

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleFunctor_exact_on_lattices : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) (O := ↥(OL LL)) ι π → Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧ ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x := by
  first | exact @GlobalTheory.LatExact.W_exact | exact GlobalTheory.LatExact.W_exact | (intros; apply GlobalTheory.LatExact.W_exact <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.FontaineFullyFaithful

theorem map_algHom_smul {O R M N : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (σ : R →ₐ[O] R) (g : M →ₗ[O] N) (r : R) (y : R ⊗[O] M) :
    TensorProduct.map σ.toLinearMap g (r • y) = σ r • TensorProduct.map σ.toLinearMap g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [TensorProduct.smul_tmul', map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem ext_span {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {O : Type} [CommRing O] [Module O M] [Module O N] {ι : Type} (v : ι → M)
    (hv : Submodule.span R (Set.range v) = ⊤) (P Q : M →ₗ[O] N) (hP : ∀ (r : R) y, P (r • y) = r • P y)
    (hQ : ∀ (r : R) y, Q (r • y) = r • Q y) (h : ∀ i, P (v i) = Q (v i)) (y : M) : P y = Q y := by
  have hy : y ∈ Submodule.span R (Set.range v) := by rw [hv]; trivial
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact h i
  | zero => simp
  | add y z _ _ hy hz => simp only [map_add, hy, hz]
  | smul r y _ hy => rw [hP, hQ, hy]

theorem exists_fixed_lift {O R M N : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup M]
    [Module O M] [AddCommGroup N] [Module O N] (g : M →ₗ[O] R ⊗[O] N)
    (hinj : Function.Injective (fun n : N => (1 : R) ⊗ₜ[O] n)) (hg : ∀ m, ∃ n, g m = (1 : R) ⊗ₜ[O] n) :
    ∃ F0 : M →ₗ[O] N, ∀ m, (1 : R) ⊗ₜ[O] F0 m = g m := by
  let ι : N →ₗ[O] R ⊗[O] N := TensorProduct.mk O R N 1
  have hι : Function.Injective ι := hinj
  have hg' : ∀ m, g m ∈ LinearMap.range ι := fun m => by
    obtain ⟨n, hn⟩ := hg m; exact ⟨n, hn.symm⟩
  refine ⟨(LinearEquiv.ofInjective ι hι).symm.toLinearMap.comp (g.codRestrict _ hg'), fun m => ?_⟩
  exact LinearEquiv.ofInjective_symm_apply (h := hι) ι (g.codRestrict _ hg' m)

theorem exists_fixed_lift' {O R M N : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup M]
    [Module O M] [AddCommGroup N] [Module O N] (ft : R ⊗[O] M →ₗ[R] R ⊗[O] N)
    (hinj : Function.Injective (fun n : N => (1 : R) ⊗ₜ[O] n))
    (hg : ∀ m : M, ∃ n, ft ((1 : R) ⊗ₜ[O] m) = (1 : R) ⊗ₜ[O] n) :
    ∃ F0 : M →ₗ[O] N, ∀ m, (1 : R) ⊗ₜ[O] F0 m = ft ((1 : R) ⊗ₜ[O] m) :=
  exists_fixed_lift ((ft.restrictScalars O).comp (TensorProduct.mk O R M 1)) hinj hg

theorem tensor_map_eq {O R M N : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup M]
    [Module O M] [AddCommGroup N] [Module O N] (g F0 : M →ₗ[O] N) (ft : R ⊗[O] M →ₗ[R] R ⊗[O] N)
    (hF0 : ∀ m, (1 : R) ⊗ₜ[O] F0 m = ft ((1 : R) ⊗ₜ[O] m)) (hg : ∀ m, g m = F0 m) (y : R ⊗[O] M) :
    TensorProduct.map (LinearMap.id : R →ₗ[O] R) g y = ft y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply, hg]
    have e1 : a ⊗ₜ[O] (F0 m) = a • ((1 : R) ⊗ₜ[O] (F0 m)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have e2 : a ⊗ₜ[O] m = a • ((1 : R) ⊗ₜ[O] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e1, e2, hF0, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem uniq_of_span {O R M N ι : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup M]
    [Module O M] [AddCommGroup N] [Module O N] (v : ι → R ⊗[O] M)
    (hv : Submodule.span R (Set.range v) = ⊤) (g g' : M →ₗ[O] N)
    (hinj : Function.Injective (fun n : N => (1 : R) ⊗ₜ[O] n))
    (h : ∀ i, TensorProduct.map (LinearMap.id : R →ₗ[O] R) g (v i) =
      TensorProduct.map (LinearMap.id : R →ₗ[O] R) g' (v i)) (m : M) : g m = g' m := by
  have hsm : ∀ (k : M →ₗ[O] N) (r : R) (y : R ⊗[O] M), TensorProduct.map (LinearMap.id : R →ₗ[O] R) k (r • y) =
      r • TensorProduct.map (LinearMap.id : R →ₗ[O] R) k y := fun k r y => by
    simpa using map_algHom_smul (AlgHom.id O R) k r y
  have := ext_span v hv _ _ (hsm g) (hsm g') h ((1 : R) ⊗ₜ[O] m)
  simp only [TensorProduct.map_tmul, LinearMap.id_apply] at this
  exact hinj this

end GlobalTheory.FontaineFullyFaithful

theorem GlobalTheory.FontaineFullyFaithful.exists_latHom {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsFractionRing O LL]
    (T T' : LocLat G Qp LL O) (F0 : ↥T.L.T →ₗ[O] ↥T'.L.T)
    (hF0 : ∀ g t, F0 (T.actT g t) = T'.actT g (F0 t)) :
    ∃ F : LatHom T.L T'.L, ∀ t : ↥T.L.T, F.f (t : T.V) = ((F0 t : ↥T'.L.T) : T'.V) := by
  haveI := T.L.free
  let bT := Module.Free.chooseBasis O ↥T.L.T
  let v : Module.Free.ChooseBasisIndex O ↥T.L.T → T.V := fun i => (bT i : T.V)
  have hliO : LinearIndependent O v :=
    bT.linearIndependent.map' T.L.T.subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent LL v := (LinearIndependent.iff_fractionRing (R := O) (K := LL)).mp hliO
  have hO : Submodule.span O (Set.range v) = T.L.T := by
    rw [show Set.range v = T.L.T.subtype '' Set.range bT from Set.range_comp _ _, Submodule.span_image,
      bT.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hsp : ⊤ ≤ Submodule.span LL (Set.range v) := by
    rw [← T.L.span, Submodule.span_le]
    intro x hx
    have hx1 : x ∈ Submodule.span O (Set.range v) := by rw [hO]; exact hx
    exact Submodule.span_le_restrictScalars O LL (Set.range v) hx1
  obtain ⟨Ff, hFv⟩ : ∃ Ff : T.V →ₗ[LL] T'.V, ∀ i, Ff (v i) = ((F0 (bT i) : ↥T'.L.T) : T'.V) := by
    refine ⟨(Basis.mk hli hsp).constr LL (fun i => ((F0 (bT i) : ↥T'.L.T) : T'.V)), fun i => ?_⟩
    rw [show v i = Basis.mk hli hsp i from (Basis.mk_apply hli hsp i).symm]
    exact (Basis.mk hli hsp).constr_basis LL _ i
  have hFT : ∀ t : ↥T.L.T, Ff (t : T.V) = ((F0 t : ↥T'.L.T) : T'.V) := by
    have : (Ff.restrictScalars O).comp T.L.T.subtype = T'.L.T.subtype.comp F0 :=
      bT.ext (fun i => hFv i)
    intro t
    exact LinearMap.congr_fun this t
  have hequiv : ∀ g x, Ff (T.ρ g x) = T'.ρ g (Ff x) := by
    intro g
    have : Ff.comp (T.ρ g) = (T'.ρ g).comp Ff := LinearMap.ext_on T.L.span (fun x hx => by
      have h1 := hFT (T.actT g ⟨x, hx⟩)
      rw [hF0] at h1
      have h2 : Ff x = _ := hFT ⟨x, hx⟩
      show Ff (T.ρ g x) = T'.ρ g (Ff x)
      rw [h2]
      exact h1)
    intro x
    exact LinearMap.congr_fun this x
  haveI : ContinuousSMul LL T'.V := IsModuleTopology.toContinuousSMul LL T'.V
  refine ⟨LatHom.mk Ff hequiv (IsModuleTopology.continuous_of_linearMap Ff) (fun x hx => ?_), hFT⟩
  have h2 : Ff x = _ := hFT ⟨x, hx⟩
  rw [h2]
  exact (F0 ⟨x, hx⟩).2

theorem GlobalTheory.FontaineFullyFaithful.isFractionRing_OL (l : ℕ) [Fact l.Prime] (LL : FinExt l) : IsFractionRing ↥(OL LL) ↥LL.1 :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1

theorem GlobalTheory.FontaineFullyFaithful.exists_extension {O E R D D' M P : Type} [CommRing O] [Nontrivial O] [CommRing E] [CommRing R]
    [Algebra O R] [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M]
    [AddCommGroup D] [Module E D] [Module.Free E D] [AddCommGroup D'] [Module E D'] [AddCommGroup P] [Module R P]
    (hr : Module.finrank E D = Module.finrank O M) (io : E →+* R) (j : D →+ R ⊗[O] M) (j' : D' →+ P)
    (hj : ∀ (e : E) x, j (e • x) = io e • j x) (hj' : ∀ (e : E) x, j' (e • x) = io e • j' x)
    (hinj : Function.Injective j) (hsp : Submodule.span R (Set.range j) = ⊤) (f : D →ₗ[E] D') :
    ∃ ft : R ⊗[O] M →ₗ[R] P, ∀ x, ft (j x) = j' (f x) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI := Module.subsingleton R P
    exact ⟨0, fun x => Subsingleton.elim _ _⟩
  haveI : Nontrivial E := io.domain_nontrivial
  haveI : Module.Finite E D := by
    rcases Nat.eq_zero_or_pos (Module.finrank O M) with h0 | hp
    · haveI : Subsingleton M := (Module.finBasisOfFinrankEq O M h0).repr.injective.subsingleton
      haveI : Subsingleton D := hinj.subsingleton
      infer_instance
    · exact Module.finite_of_finrank_pos (hr ▸ hp)
  let b := Module.finBasisOfFinrankEq E D hr
  have hexp : ∀ {D₁ P₁ : Type} [AddCommGroup D₁] [Module E D₁] [AddCommGroup P₁] [Module R P₁] (k : D₁ →+ P₁)
      (_ : ∀ (e : E) x, k (e • x) = io e • k x) (g : D →ₗ[E] D₁) (x : D),
      k (g x) = ∑ i, io (b.repr x i) • k (g (b i)) := by
    intro D₁ P₁ _ _ _ _ k hk g x
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, hk]
  have hsp' : ⊤ ≤ Submodule.span R (Set.range fun i => j (b i)) := by
    rw [← hsp, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have := hexp j hj LinearMap.id x
    simp only [LinearMap.id_apply] at this
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent R fun i => j (b i) := by
    let c := Algebra.TensorProduct.basis R (Module.finBasis O M)
    have hs : Function.Surjective (Finsupp.linearCombination R fun i => j (b i)) := by
      rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
      exact top_le_iff.mp hsp'
    exact OrzechProperty.injective_of_surjective_of_injective c.repr.symm.toLinearMap _ c.repr.symm.injective hs
  refine ⟨(Basis.mk hli hsp').constr R fun i => j' (f (b i)), fun x => ?_⟩
  have h1 := hexp j hj LinearMap.id x
  simp only [LinearMap.id_apply] at h1
  rw [h1, hexp j' hj' f x, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, show j (b i) = Basis.mk hli hsp' i from (Basis.mk_apply hli hsp' i).symm, Basis.constr_basis]

theorem GlobalTheory.FontaineFullyFaithful.exists_extension_tie {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA R : Type} [CommRing RA] [CommRing R] [Algebra O RA]
    [Algebra O R] {inclR : RA →ₐ[O] R} {φR : R →ₐ[O] R} {gR : G → (R →ₐ[O] R)} {πA : RA}
    (E : EtTie W RA R inclR φR gR πA) (T T' : LocLat G Qp LL O) (f : W.DD T →ₗ[W.EE] W.DD T') :
    ∃ ft : TW R T →ₗ[R] TW R T', ∀ x, ft (E.jD T x) = E.jD T' (f x) := by
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  haveI := T.L.free
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  haveI := (W.DD_free T).1
  exact GlobalTheory.FontaineFullyFaithful.exists_extension (W.DD_free T).2 E.ioE.toRingHom (E.jD T).toAddMonoidHom
    (E.jD T').toAddMonoidHom (E.jD_smul T) (E.jD_smul T') (E.jD_inj T) (E.jD_span T) f

set_option maxHeartbeats 1000000 in
private theorem GlobalTheory.FontaineFullyFaithful.main_tie {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA R : Type} [CommRing RA] [CommRing R] [Algebra O RA]
    [Algebra O R] {inclR : RA →ₐ[O] R} {φR : R →ₐ[O] R} {gR : G → (R →ₐ[O] R)} {πA : RA}
    (E : EtTie W RA R inclR φR gR πA) (T T' : LocLat G Qp LL O) (f : W.DD T →ₗ[W.EE] W.DD T')
    [IsFractionRing O LL]
    (hφ : ∀ x, f (W.φD T x) = W.φD T' (f x)) (hγ : ∀ g x, f (W.γD T g x) = W.γD T' g (f x))
    (hfix : ∀ y : TW R T', TWmap φR T' y = y → ∃ t' : ↥T'.L.T, y = (1 : R) ⊗ₜ[O] t')
    (hinj' : Function.Injective (fun n : ↥T'.L.T => (1 : R) ⊗ₜ[O] n)) :
    ∃! F : LatHom T.L T'.L, ∀ x, W.map F x = f x := by
  obtain ⟨ft, hft'⟩ := GlobalTheory.FontaineFullyFaithful.exists_extension_tie E T T' f
  have comm : ∀ (σ : R →ₐ[O] R) (A : TW R T →ₗ[O] TW R T)
      (A' : TW R T' →ₗ[O] TW R T'), (∀ (r : R) (y : TW R T), A (r • y) = σ r • A y) →
      (∀ (r : R) (y : TW R T'), A' (r • y) = σ r • A' y) → (∀ x, ft (A (E.jD T x)) = A' (ft (E.jD T x))) →
      ∀ y, ft (A y) = A' (ft y) := by
    intro σ A A' hA hA' hx y
    have hy : y ∈ Submodule.span R (Set.range (E.jD T)) := by rw [E.jD_span T]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨x, rfl⟩ := hy; exact hx x
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, hy, hz]
    | smul r y _ hy => rw [hA, map_smul, hy, map_smul, hA']
  have hφt : ∀ y, ft (TWmap φR T y) = TWmap φR T' (ft y) :=
    comm φR (TWmap φR T) (TWmap φR T')
      (fun r y => GlobalTheory.FontaineFullyFaithful.map_algHom_smul φR LinearMap.id r y)
      (fun r y => GlobalTheory.FontaineFullyFaithful.map_algHom_smul φR LinearMap.id r y)
      (fun x => (congrArg ft (E.jD_φ T x)).symm.trans ((hft' _).trans ((congrArg (E.jD T') (hφ x)).trans
        ((E.jD_φ T' (f x)).trans (congrArg (TWmap φR T') (hft' x).symm)))))
  have hgt : ∀ (g : G) y, ft (TWact (gR g) T g y) =
      TWact (gR g) T' g (ft y) := fun g =>
    comm (gR g) (TWact (gR g) T g)
      (TWact (gR g) T' g)
      (fun r y => GlobalTheory.FontaineFullyFaithful.map_algHom_smul (gR g) (T.actT g) r y)
      (fun r y => GlobalTheory.FontaineFullyFaithful.map_algHom_smul (gR g) (T'.actT g) r y)
      (fun x => by
        have h1 := E.jD_act T g x
        have h2 := E.jD_act T' g (f x)
        exact (congrArg ft h1).symm.trans ((hft' _).trans ((congrArg (E.jD T') (hγ _ x)).trans
          (h2.trans (congrArg (TWact (gR g) T' g) (hft' x).symm)))))
  have hφ1 : ∀ (T₀ : LocLat G Qp LL O) (t₀ : ↥T₀.L.T),
      TWmap φR T₀ ((1 : R) ⊗ₜ[O] t₀) = (1 : R) ⊗ₜ[O] t₀ := by
    intro T₀ t₀
    simp only [TWmap, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one, LinearMap.id_apply]
  have hg0 : ∀ t : ↥T.L.T, ∃ t' : ↥T'.L.T, ft ((1 : R) ⊗ₜ[O] t) = (1 : R) ⊗ₜ[O] t' := by
    intro t
    have hb : TWmap φR T' (ft ((1 : R) ⊗ₜ[O] t)) = ft ((1 : R) ⊗ₜ[O] t) := by
      rw [← hφt, hφ1]
    exact hfix _ hb
  obtain ⟨F0, hF0⟩ := GlobalTheory.FontaineFullyFaithful.exists_fixed_lift' ft hinj' hg0
  have hact1 : ∀ (T₀ : LocLat G Qp LL O) (g : G) (t₀ : ↥T₀.L.T),
      TWact (gR g) T₀ g ((1 : R) ⊗ₜ[O] t₀) =
        (1 : R) ⊗ₜ[O] (T₀.actT g t₀) := by
    intro T₀ g t₀
    simp only [TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]
  have heq : ∀ g t, F0 (T.actT g t) = T'.actT g (F0 t) := by
    intro g t
    exact hinj' ((hF0 _).trans ((congrArg ft (hact1 T g t).symm).trans ((hgt g _).trans
      ((congrArg (TWact (gR g) T' g) (hF0 t).symm).trans (hact1 T' g (F0 t))))))
  obtain ⟨Fl, hFl⟩ := GlobalTheory.FontaineFullyFaithful.exists_latHom T T' F0 heq
  have hFlmap : ∀ x, W.map Fl x = f x := by
    intro x
    apply E.jD_inj T'
    refine (E.jD_map Fl x).trans ?_
    refine (GlobalTheory.FontaineFullyFaithful.tensor_map_eq _ F0 ft hF0 (fun t => ?_) _).trans (hft' x)
    exact Subtype.ext (hFl t)
  refine ⟨Fl, hFlmap, ?_⟩
  intro F' hF'
  have hgg := GlobalTheory.FontaineFullyFaithful.uniq_of_span (E.jD T) (E.jD_span T) _ _ hinj' (fun x =>
    (E.jD_map F' x).symm.trans ((congrArg (E.jD T') ((hF' x).trans (hFlmap x).symm)).trans (E.jD_map Fl x)))
  have hv : ∀ t : ↥T.L.T, F'.f (t : T.V) = Fl.f (t : T.V) := fun t => congrArg Subtype.val (hgg t)
  have hff : F'.f = Fl.f := LinearMap.ext_on T.L.span (fun v hv' => hv ⟨v, hv'⟩)
  cases F'; cases Fl
  simp only at hff
  subst hff
  rfl

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.FontaineFullyFaithful.main : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (f : W.DD T →ₗ[W.EE] W.DD T'), (∀ x, f (W.φD T x) = W.φD T' (f x)) → (∀ g x, f (W.γD T g x) = W.γD T' g (f x)) → ∃! F : LatHom T.L T'.L, ∀ x, W.map F x = f x := by
  intro D HW F l _ K s LL h W T T' f hφ hγ
  haveI := GlobalTheory.FontaineFullyFaithful.isFractionRing_OL l LL
  exact GlobalTheory.FontaineFullyFaithful.main_tie ((F l).E K s LL h).tie T T' f hφ hγ
    (fun y hy => ((GlobalTheory.WittTensorFixed.main l K LL T').2.1 y).1 hy) (GlobalTheory.WittTensorFixed.main l K LL T').2.2
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachFunctor_fullyFaithful : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (f : W.DD T →ₗ[W.EE] W.DD T'), (∀ x, f (W.φD T x) = W.φD T' (f x)) → (∀ g x, f (W.γD T g x) = W.γD T' g (f x)) → ∃! F : LatHom T.L T'.L, ∀ x, W.map F x = f x := by
  atlas_forward_decl GlobalTheory.FontaineFullyFaithful.main
end

section
section
noncomputable section

namespace GlobalTheory.EtaleFrob

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem linearIndependent_of_span {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {r : ℕ}
    (d : Basis (Fin r) R M) (v : Fin r → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    LinearIndependent R v := by
  let f : (Fin r → R) →ₗ[R] M := Fintype.linearCombination R v
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]; exact hv
  let g : (Fin r → R) →ₗ[R] (Fin r → R) := d.equivFun.toLinearMap ∘ₗ f
  have hg : Function.Surjective g := d.equivFun.surjective.comp hf
  have hgi : Function.Injective g := OrzechProperty.injective_of_surjective_endomorphism g hg
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have h1 : g a = g 0 := by
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, map_zero, f, Fintype.linearCombination_apply, ha]
  exact fun i => congrFun (hgi h1) i

theorem twmap_smul {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {R : Type} [CommRing R] [Algebra O R]
    (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (a : R) (z : TW R T) :
    TWmap f T (a • z) = f a • TWmap f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x t => simp [TWmap, TensorProduct.smul_tmul', map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem twmap_surjective {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {R : Type} [CommRing R] [Algebra O R]
    (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (hf : Function.Surjective f) :
    Function.Surjective (TWmap f T) :=
  TensorProduct.map_surjective (g := f.toLinearMap) hf (g' := LinearMap.id) (fun x => ⟨x, rfl⟩)

end GlobalTheory.EtaleFrob

namespace GlobalTheory.EtaleFrob

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

set_option maxHeartbeats 1000000 in

theorem phi_basis_of_tie {W : LocWach PD LL O v n} (E : EtTie W RA RW inclR φR gR πA) [Nontrivial W.EE] [Nontrivial O]
    (hφ : Function.Surjective φR) (hunits : ∀ x : W.EE, IsUnit (E.ioE x) → IsUnit x)
    (T : LocLat G Qp LL O) (hTfree : Module.Free O ↥T.L.T) (hTfin : Module.Finite O ↥T.L.T) :
    ∃ (r : ℕ) (b b' : Module.Basis (Fin r) W.EE (W.DD T)), ∀ j, b' j = W.φD T (b j) := by
  haveI hfreeD : Module.Free W.EE (W.DD T) := (W.DD_free T).1
  have hrk : finrank W.EE (W.DD T) = finrank O ↥T.L.T := (W.DD_free T).2
  obtain ⟨d0⟩ : Nonempty (Basis (Fin (finrank O ↥T.L.T)) RW (TW RW T)) :=
    ⟨Algebra.TensorProduct.basis RW (Module.finBasis O ↥T.L.T)⟩
  haveI hfin : Module.Finite W.EE (W.DD T) := by
    rcases Nat.eq_zero_or_pos (finrank W.EE (W.DD T)) with h0 | h0
    · haveI : IsEmpty (Fin (finrank O ↥T.L.T)) := by rw [← hrk, h0]; infer_instance
      have hz : ∀ x : W.DD T, x = 0 := fun x => E.jD_inj T (by
        rw [map_zero, ← d0.sum_repr (E.jD T x)]; simp)
      haveI : Subsingleton (W.DD T) := ⟨fun x y => by rw [hz x, hz y]⟩
      infer_instance
    · exact Module.finite_of_finrank_pos h0
  obtain ⟨r, hr⟩ : ∃ r, r = finrank W.EE (W.DD T) := ⟨_, rfl⟩
  obtain ⟨b⟩ : Nonempty (Basis (Fin r) W.EE (W.DD T)) :=
    ⟨(Module.finBasis W.EE (W.DD T)).reindex (finCongr hr.symm)⟩
  obtain ⟨d⟩ : Nonempty (Basis (Fin r) RW (TW RW T)) := ⟨d0.reindex (finCongr (hr.trans hrk).symm)⟩

  obtain ⟨c, hcdef⟩ : ∃ c : Fin r → TW RW T, ∀ j, c j = E.jD T (b j) := ⟨_, fun _ => rfl⟩
  have hjD : ∀ x : W.DD T, E.jD T x = ∑ i, E.ioE (b.repr x i) • c i := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [E.jD_smul, hcdef]
  have hc : Submodule.span RW (Set.range c) = ⊤ := by
    rw [eq_top_iff, ← E.jD_span T, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hjD x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  obtain ⟨cb, hcb⟩ : ∃ cb : Basis (Fin r) RW (TW RW T), ∀ i, cb i = c i :=
    ⟨Basis.mk (linearIndependent_of_span d c hc) hc.ge, fun i => Basis.mk_apply _ _ i⟩

  obtain ⟨c', hc'def⟩ : ∃ c' : Fin r → TW RW T, ∀ j, c' j = TWmap φR T (c j) := ⟨_, fun _ => rfl⟩
  have hTW : ∀ y : TW RW T, ∃ x, TWmap φR T x = y := fun y => twmap_surjective φR T hφ y
  have himg : ∀ x : TW RW T, TWmap φR T x ∈ Submodule.span RW (Set.range c') := by
    intro x
    have hx : x ∈ Submodule.span RW (Set.range c) := by rw [hc]; exact Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun RW).1 hx
    rw [← ha, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [twmap_smul, ← hc'def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have hc' : Submodule.span RW (Set.range c') = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, hxy⟩ := hTW y
    rw [← hxy]
    exact himg x
  have hdet : IsUnit (cb.det c') := cb.is_basis_iff_det.1 ⟨linearIndependent_of_span d c' hc', hc'⟩

  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin r) (Fin r) W.EE, M = b.toMatrix (fun j => W.φD T (b j)) :=
    ⟨_, rfl⟩
  have hM : cb.toMatrix c' = M.map E.ioE := by
    ext i j
    rw [Basis.toMatrix_apply, Matrix.map_apply]
    have e1 : c' j = ∑ k, E.ioE (M k j) • cb k := by
      rw [hc'def, hcdef, ← E.jD_φ, hjD]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hcb, hMdef, Basis.toMatrix_apply]
    rw [e1, ← Basis.equivFun_symm_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hdetM : IsUnit (E.ioE M.det) := by
    rw [AlgHom.map_det]
    rw [Basis.det_apply, hM] at hdet
    exact hdet
  have hbas := (b.is_basis_iff_det (v := fun j => W.φD T (b j))).2
    (by rw [Basis.det_apply, ← hMdef]; exact hunits _ hdetM)
  exact ⟨r, b, Basis.mk hbas.1 hbas.2.ge, fun j => Basis.mk_apply _ _ j⟩

end Generic

theorem φRW_onto {l : ℕ} [Fact l.Prime] (LL : FinExt l) : Function.Surjective (φRW LL) := by
  haveI := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  have h : Function.Surjective (frobW l) :=
    WittVector.map_surjective (frobenius (Cb l) l) fun x =>
      IsAlgClosed.exists_pow_nat_eq x (Fact.out : l.Prime).pos
  exact LinearMap.lTensor_surjective ↥(OL LL) (g := (frobW l).toLinearMap) h

set_option maxHeartbeats 1000000 in

theorem phi_basis : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), ∃ (r : ℕ) (b b' : Module.Basis (Fin r) W.EE (W.DD T)), ∀ j, b' j = W.φD T (b j) := by
  intro D HW F l _ K s LL h W T
  haveI : Nontrivial W.EE := W.EE_inj.nontrivial
  exact phi_basis_of_tie ((F l).E K s LL h).tie (φRW_onto LL)
    (GlobalTheory.IoInj.ioE_injective_saturated_inter l (D.loc l) (D.locA l) K s LL h _ _ _
      (GlobalTheory.NL.ioW (HW l) (F l) h (GlobalTheory.NL.Holds.laws (HW l) (F l) h))).2.1
    T T.L.free (Module.Finite.iff_fg.mpr T.L.fg)

end GlobalTheory.EtaleFrob
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachEtaleModule_frobenius_basis : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), ∃ (r : ℕ) (b b' : Module.Basis (Fin r) W.EE (W.DD T)), ∀ j, b' j = W.φD T (b j) := by
  atlas_forward_decl GlobalTheory.EtaleFrob.phi_basis
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.PsiOp

def Tw {R : Type} [CommRing R] (_φ : R →+* R) : Type := R

instance {R : Type} [CommRing R] (φ : R →+* R) : CommRing (Tw φ) := inferInstanceAs (CommRing R)

instance {R : Type} [CommRing R] (φ : R →+* R) : Algebra R (Tw φ) :=
  @RingHom.toAlgebra R (Tw φ) _ _ φ

variable {R : Type} [CommRing R] (φ : R →+* R) (u : R) (l : ℕ)

def expL : (Fin l → R) →ₗ[R] Tw φ where
  toFun c := (∑ j : Fin l, u ^ (j : ℕ) * φ (c j) : R)
  map_add' c d := by
    show (∑ j : Fin l, u ^ (j : ℕ) * φ (c j + d j) : R) = (∑ j : Fin l, u ^ (j : ℕ) * φ (c j) : R) + ∑ j : Fin l, u ^ (j : ℕ) * φ (d j)
    rw [← Finset.sum_add_distrib]; simp [mul_add]
  map_smul' a c := by
    show (∑ j : Fin l, u ^ (j : ℕ) * φ (a * c j) : R) = φ a * ∑ j : Fin l, u ^ (j : ℕ) * φ (c j)
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]; ring

theorem expL_apply (c : Fin l → R) : (expL φ u l c : R) = ∑ j : Fin l, u ^ (j : ℕ) * φ (c j) := rfl

section Main

variable {φ u l}

theorem expL_bij (hex : ∀ x : R, ∃! c : Fin l → R, x = ∑ j : Fin l, u ^ (j : ℕ) * φ (c j)) :
    Function.Bijective (expL φ u l) := by
  rw [Function.bijective_iff_existsUnique]
  intro x
  obtain ⟨c, hc, hu⟩ := hex x
  exact ⟨c, hc.symm, fun d hd => hu d hd.symm⟩

def bas (hex : ∀ x : R, ∃! c : Fin l → R, x = ∑ j : Fin l, u ^ (j : ℕ) * φ (c j)) :
    Module.Basis (Fin l) R (Tw φ) :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ (expL_bij hex)).symm

variable (hex : ∀ x : R, ∃! c : Fin l → R, x = ∑ j : Fin l, u ^ (j : ℕ) * φ (c j))

theorem repr_expL (c : Fin l → R) (i : Fin l) : (bas hex).repr (expL φ u l c) i = c i := by
  rw [bas, Module.Basis.ofEquivFun_repr_apply, LinearEquiv.ofBijective_symm_apply_apply]

theorem expL_repr (x : Tw φ) : expL φ u l ((bas hex).repr x) = x := by
  have h := (LinearEquiv.ofBijective (expL φ u l) (expL_bij hex)).apply_symm_apply x
  rw [LinearEquiv.ofBijective_apply] at h
  convert h using 2
  funext i
  rw [bas, Module.Basis.ofEquivFun_repr_apply]

theorem bas_apply (i : Fin l) : (bas hex i : R) = u ^ (i : ℕ) := by
  rw [bas, Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm]
  change (∑ j : Fin l, u ^ (j : ℕ) * φ ((Pi.single i (1 : R) : Fin l → R) j) : R) = u ^ (i : ℕ)
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

end Main

section Main2

variable {φ u l}
variable (hex : ∀ x : R, ∃! c : Fin l → R, x = ∑ j : Fin l, u ^ (j : ℕ) * φ (c j))

theorem repr_mul_pow [NeZero l] (hu : u ^ l = φ u) (y : Tw φ) (i : Fin l) :
    (bas hex).repr (y * bas hex i) i = (bas hex).repr y 0 := by
  set d : Fin l → R := fun k => (bas hex).repr y k with hd
  have hy : (y : R) = ∑ k : Fin l, u ^ (k : ℕ) * φ (d k) := by
    have := expL_repr hex y; rw [expL_apply] at this; exact this.symm
  have key : (y * bas hex i : Tw φ) = expL φ u l (fun m => (if (i : ℕ) ≤ m then 1 else u) * d (m - i)) := by
    have key' : ∀ Y : R, Y = ∑ k : Fin l, u ^ (k : ℕ) * φ (d k) →
        Y * u ^ (i : ℕ) = ∑ m : Fin l, u ^ (m : ℕ) * φ ((if (i : ℕ) ≤ m then 1 else u) * d (m - i)) := by
      intro Y hY
      rw [hY, Finset.sum_mul]
      refine Fintype.sum_equiv (Equiv.addRight i) _ _ (fun k => ?_)
      generalize hm : Equiv.addRight i k = m
      have hmk : m - i = k := by rw [← hm]; exact add_sub_cancel_right k i
      have hmv : (m : ℕ) = ((k : ℕ) + i) % l := by rw [← hm]; exact Fin.val_add k i
      have hk := k.2
      have hi := i.2
      have hcase : ((k : ℕ) + i < l ∧ (m : ℕ) = k + i) ∨ (l ≤ (k : ℕ) + i ∧ (m : ℕ) = k + i - l) := by
        rcases lt_or_ge ((k : ℕ) + i) l with h | h
        · exact Or.inl ⟨h, by rw [hmv, Nat.mod_eq_of_lt h]⟩
        · exact Or.inr ⟨h, by rw [hmv, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]⟩
      rw [hmk]
      split_ifs with hle
      · have hmv2 : (m : ℕ) = k + i := by rcases hcase with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
        rw [hmv2, one_mul, pow_add]; ring
      · have hmv2 : (m : ℕ) = k + i - l := by rcases hcase with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
        have hl2 : l ≤ (k : ℕ) + i := by rcases hcase with ⟨_, h⟩ | ⟨h, _⟩ <;> omega
        rw [hmv2, map_mul, ← hu]
        have e : u ^ (k : ℕ) * u ^ (i : ℕ) = u ^ ((k : ℕ) + i - l) * u ^ l := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        linear_combination (φ (d k)) * e
    rw [bas_apply]
    exact key' y hy
  rw [key, repr_expL]
  simp [hd]

theorem trace_eq [NeZero l] (hu : u ^ l = φ u) (y : Tw φ) :
    Algebra.trace R (Tw φ) y = (l : R) * (bas hex).repr y 0 := by
  classical
  rw [Algebra.trace_eq_matrix_trace (bas hex), Matrix.trace]
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, repr_mul_pow hex hu]
  simp

end Main2

section Main3

variable {φ u l}

theorem hex_gam (γ γi : R →+* R) (h1 : ∀ a, γ (γi a) = a) (h2 : ∀ a, γi (γ a) = a)
    (hφγ : ∀ a, φ (γ a) = γ (φ a))
    (hex : ∀ x : R, ∃! c : Fin l → R, x = ∑ j : Fin l, u ^ (j : ℕ) * φ (c j)) :
    ∀ x : R, ∃! c : Fin l → R, x = ∑ j : Fin l, γ u ^ (j : ℕ) * φ (c j) := by
  have hφγi : ∀ a, φ (γi a) = γi (φ a) := fun a => by
    rw [← h2 (φ (γi a)), ← hφγ, h1]
  intro x
  obtain ⟨c, hc, hu⟩ := hex (γi x)
  refine ⟨fun j => γ (c j), ?_, ?_⟩
  · have := congrArg γ hc
    rw [h1] at this
    rw [this, map_sum]
    simp [map_mul, map_pow, hφγ]
  · intro d hd
    have : c = fun j => γi (d j) :=
      (hu _ (by rw [hd, map_sum]; simp [map_mul, map_pow, h2, hφγi])).symm
    funext j
    rw [this, h1]

theorem repr_gam (γ γi : R →+* R) (h1 : ∀ a, γ (γi a) = a) (h2 : ∀ a, γi (γ a) = a)
    (hφγ : ∀ a, φ (γ a) = γ (φ a))
    (hex : ∀ x : R, ∃! c : Fin l → R, x = ∑ j : Fin l, u ^ (j : ℕ) * φ (c j)) (z : Tw φ) (i : Fin l) :
    (bas (hex_gam γ γi h1 h2 hφγ hex)).repr (γ z) i = γ ((bas hex).repr z i) := by
  have hz := expL_repr hex z
  have key : (γ z : R) = ∑ j : Fin l, γ u ^ (j : ℕ) * φ (γ ((bas hex).repr z j)) := by
    conv_lhs => rw [← hz]
    rw [expL_apply, map_sum]
    simp [map_mul, map_pow, hφγ]
  have key2 : (γ z : R) = expL φ (γ u) l (fun j => γ ((bas hex).repr z j)) := key
  rw [key2, repr_expL]

theorem coef_gam [NeZero l] (hu : u ^ l = φ u) (γ γi : R →+* R) (h1 : ∀ a, γ (γi a) = a)
    (h2 : ∀ a, γi (γ a) = a) (hφγ : ∀ a, φ (γ a) = γ (φ a))
    (htf : ∀ x : R, (l : R) * x = 0 → x = 0)
    (hex : ∀ x : R, ∃! c : Fin l → R, x = ∑ j : Fin l, u ^ (j : ℕ) * φ (c j)) (x : R) :
    (bas hex).repr (γ x) 0 = γ ((bas hex).repr x 0) := by
  have hu' : γ u ^ l = φ (γ u) := by rw [← map_pow, hu, hφγ]
  have t1 := trace_eq hex hu (γ x)
  have t2 := trace_eq (hex_gam γ γi h1 h2 hφγ hex) hu' (γ x)
  have t3 : (Algebra.trace R (Tw φ)) (γ x) = (l : R) * γ ((bas hex).repr x 0) :=
    t2.trans (congrArg _ (repr_gam γ γi h1 h2 hφγ hex x 0))
  rw [← sub_eq_zero]
  apply htf
  rw [mul_sub, ← t1, ← t3, sub_self]

end Main3

section Psi

variable {φ u l}
variable (hex : ∀ x : R, ∃! c : Fin l → R, x = ∑ j : Fin l, u ^ (j : ℕ) * φ (c j))

def psi [NeZero l] (x : R) : R := (bas hex).repr x 0

theorem psi_add [NeZero l] (x y : R) : psi hex (x + y) = psi hex x + psi hex y :=
  congrArg (fun f => f 0) ((bas hex).repr.map_add x y)

theorem psi_φmul [NeZero l] (a x : R) : psi hex (φ a * x) = a * psi hex x :=
  congrArg (fun f => f 0) ((bas hex).repr.map_smul a x)

theorem psi_single [NeZero l] (j : ℕ) (hj : j < l) (a : R) :
    psi hex (u ^ j * φ a) = if j = 0 then a else 0 := by
  have e1 : (u ^ j * φ a : R) = expL φ u l (Pi.single (⟨j, hj⟩ : Fin l) a) := by
    rw [expL_apply, Finset.sum_eq_single (⟨j, hj⟩ : Fin l)]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  unfold psi
  rw [e1, repr_expL]
  by_cases hj0 : j = 0
  · subst hj0; simp
  · simp [Pi.single_apply, Fin.ext_iff, hj0, Ne.symm hj0]

theorem psi_gam [NeZero l] (hu : u ^ l = φ u) (γ γi : R →+* R) (h1 : ∀ a, γ (γi a) = a)
    (h2 : ∀ a, γi (γ a) = a) (hφγ : ∀ a, φ (γ a) = γ (φ a))
    (htf : ∀ x : R, (l : R) * x = 0 → x = 0) (x : R) : psi hex (γ x) = γ (psi hex x) :=
  coef_gam hu γ γi h1 h2 hφγ htf hex x

end Psi

end GlobalTheory.PsiOp

namespace GlobalTheory.PsiOp

open Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem eq_zero_of_mem_pow (x : W.EE) (hx : ∀ k : ℕ, ∃ e : W.EE, x = ((PD.p : ℕ) : W.EE) ^ k * e) : x = 0 := by
  have hH : IsHausdorff (Ideal.span {((PD.p : ℕ) : W.EE)}) W.EE := W.EE_complete.toIsHausdorff
  refine hH.haus x fun k => ?_
  obtain ⟨e, he⟩ := hx k
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  exact ⟨e, he⟩

theorem isUnit_πpow (m : ℕ) : IsUnit (algebraMap (LetA O n) W.EE (letπ ^ m)) := by
  rw [map_pow]; exact W.EE_π.pow m

theorem hom_ext (f g : W.EE →+* W.EE) (h : ∀ a, f (algebraMap (LetA O n) W.EE a) = g (algebraMap (LetA O n) W.EE a)) :
    f = g := by
  ext x
  rw [← sub_eq_zero]
  refine eq_zero_of_mem_pow W _ fun k => ?_
  obtain ⟨a, m, hm⟩ := W.EE_dense x k
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.1 hm
  obtain ⟨w, hw⟩ := (isUnit_πpow W m).map f
  have hgt : g (algebraMap (LetA O n) W.EE (letπ ^ m)) = f (algebraMap (LetA O n) W.EE (letπ ^ m)) :=
    (h _).symm
  set t := algebraMap (LetA O n) W.EE (letπ ^ m) with ht
  have hf := congrArg f he
  have hg := congrArg g he
  simp only [map_mul, map_sub, map_pow, map_natCast] at hf hg
  rw [h a] at hf
  rw [hgt] at hg
  rw [← hw] at hf hg
  refine ⟨(f e - g e) * ↑w⁻¹, ?_⟩
  have hw' : (w : W.EE) * ↑w⁻¹ = 1 := w.mul_inv
  linear_combination (↑w⁻¹ : W.EE) * (hf - hg) - (f x - g x) * hw'

theorem letφ_letγ (g : W.Gam) (a : LetA O n) :
    letφ W.φ₀ (letγ (W.γ₀ g) a) = letγ (W.γ₀ g) (letφ W.φ₀ a) := by
  funext i
  simp [letφ, letγ, W.γ₀_comm]

theorem φE_γE (g : W.Gam) (x : W.EE) : W.φE (W.γE g x) = W.γE g (W.φE x) := by
  have := hom_ext W ((W.φE : W.EE →+* W.EE).comp (W.γE g : W.EE →+* W.EE))
    ((W.γE g : W.EE →+* W.EE).comp (W.φE : W.EE →+* W.EE)) (fun a => by
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [W.γE_ext, W.φE_ext, W.φE_ext, W.γE_ext, letφ_letγ])
  exact RingHom.congr_fun this x

theorem tf (hO : ∀ c : PowerSeries O, ((PD.p : ℕ) : PowerSeries O) * c = 0 → c = 0)
    (x : W.EE) (hx : ((PD.p : ℕ) : W.EE) * x = 0) : x = 0 := by
  refine eq_zero_of_mem_pow W x fun k => ?_
  obtain ⟨a, m, hm⟩ := W.EE_dense x k
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.1 hm
  have h1 : algebraMap (LetA O n) W.EE (((PD.p : ℕ) : LetA O n) * a) ∈
      Ideal.span {((PD.p : ℕ) : W.EE) ^ (k + 1)} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨-e, ?_⟩
    rw [map_mul, map_natCast]
    linear_combination (algebraMap (LetA O n) W.EE (letπ ^ m)) * hx - ((PD.p : ℕ) : W.EE) * he
  obtain ⟨b, hb⟩ := W.EE_sat _ _ h1
  have hab : a = ((PD.p : ℕ) : LetA O n) ^ k * b := by
    have h2 : ((PD.p : ℕ) : LetA O n) * (a - ((PD.p : ℕ) : LetA O n) ^ k * b) = 0 := by
      rw [mul_sub, hb]; ring
    funext i
    have hi : ((PD.p : ℕ) : PowerSeries O) * (a i - ((PD.p : ℕ) : PowerSeries O) ^ k * b i) = 0 := by
      simpa using congrFun h2 i
    have := hO _ hi
    rw [sub_eq_zero] at this
    simpa using this
  obtain ⟨w, hw⟩ := isUnit_πpow W m
  refine ⟨(algebraMap (LetA O n) W.EE b + e) * ↑w⁻¹, ?_⟩
  have hw' : (w : W.EE) * ↑w⁻¹ = 1 := w.mul_inv
  rw [← hw, hab, map_mul, map_pow, map_natCast] at he
  linear_combination (↑w⁻¹ : W.EE) * he - x * hw'

theorem φE_u {l : ℕ} (hp : PD.p = l) :
    W.φE (algebraMap (LetA O n) W.EE (1 + letπ)) = (algebraMap (LetA O n) W.EE (1 + letπ)) ^ l := by
  rw [W.φE_ext, ← map_pow]
  congr 1
  funext i
  simp [letφ, letπ, W.φ₀_X, W.q₀_def, hp]

theorem psi_exists {l : ℕ} [NeZero l] (hp : PD.p = l)
    (hO : ∀ c : PowerSeries O, ((PD.p : ℕ) : PowerSeries O) * c = 0 → c = 0)
    (hex : ∀ x : W.EE, ∃! c : Fin l → W.EE, x = ∑ j : Fin l,
      (algebraMap (LetA O n) W.EE (1 + letπ)) ^ (j : ℕ) * (W.φE : W.EE →+* W.EE) (c j)) :
    ∃ ψ : W.EE →ₗ[O] W.EE, (∀ a x, ψ (W.φE a * x) = a * ψ x) ∧
      (∀ g x, ψ (W.γE g x) = W.γE g (ψ x)) ∧
      ∀ j < l, ∀ a, ψ (algebraMap (LetA O n) W.EE (1 + letπ) ^ j * W.φE a) = if j = 0 then a else 0 := by
  have hu : (algebraMap (LetA O n) W.EE (1 + letπ)) ^ l =
      (W.φE : W.EE →+* W.EE) (algebraMap (LetA O n) W.EE (1 + letπ)) := (φE_u W hp).symm
  have htf : ∀ x : W.EE, (l : W.EE) * x = 0 → x = 0 := by
    intro x hx
    refine tf W hO x ?_
    rw [hp]; exact hx
  refine ⟨{ toFun := psi hex, map_add' := psi_add hex, map_smul' := fun o x => ?_ }, ?_, ?_, ?_⟩
  · simp only [RingHom.id_apply, Algebra.smul_def]
    have := psi_φmul hex (algebraMap O W.EE o) x
    rwa [show (W.φE : W.EE →+* W.EE) (algebraMap O W.EE o) = algebraMap O W.EE o from
      W.φE.commutes o] at this
  · exact fun a x => psi_φmul hex a x
  · intro g x
    have h1 : ∀ a, W.γE g (W.γE g⁻¹ a) = a := fun a => by
      rw [← AlgHom.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgHom.one_apply]
    have h2 : ∀ a, W.γE g⁻¹ (W.γE g a) = a := fun a => by
      rw [← AlgHom.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgHom.one_apply]
    exact psi_gam hex hu (W.γE g : W.EE →+* W.EE) (W.γE g⁻¹ : W.EE →+* W.EE) h1 h2
      (fun a => φE_γE W g a) htf x
  · exact fun j hj a => psi_single hex j hj a

end GlobalTheory.PsiOp

namespace GlobalTheory

theorem psiE_exists : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∃ ψ : W.EE →ₗ[↥(OL LL)] W.EE, (∀ a x, ψ (W.φE a * x) = a * ψ x) ∧ (∀ g x, ψ (W.γE g x) = W.γE g (ψ x)) ∧ ∀ j < l, ∀ a, ψ (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE ((1 : (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))) + (letπ : (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))))) ^ j * W.φE a) = if j = 0 then a else 0 := by
  intro D HW F l _ K s LL h
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine GlobalTheory.PsiOp.psi_exists ((HW l).W K s LL h) hp ?_ (fun x => GlobalTheory.T.etaleRing_free_over_frobenius_image D HW F l K s LL h x)
  intro c hc
  rcases mul_eq_zero.1 hc with h0 | h0
  · exfalso
    rw [hp] at h0
    have h1 : ((l : ℕ) : ↥(OL LL)) = 0 := by
      have := congrArg PowerSeries.constantCoeff h0
      simpa using this
    have h2 : ((l : ℕ) : ↥LL.1) = 0 := by
      have := congrArg Subtype.val h1
      simpa using this
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2
  · exact h0

end GlobalTheory
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachFunctorRing_psiOperator_exists_of_good : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∃ ψ : W.EE →ₗ[↥(OL LL)] W.EE, (∀ a x, ψ (W.φE a * x) = a * ψ x) ∧ (∀ g x, ψ (W.γE g x) = W.γE g (ψ x)) ∧ ∀ j < l, ∀ a, ψ (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE ((1 : (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))) + (letπ : (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))))) ^ j * W.φE a) = if j = 0 then a else 0 := by
  atlas_forward_decl GlobalTheory.psiE_exists
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem psi_of_etale_basis {R E M Γ : Type*} [CommRing R] [CommRing E] [Algebra R E]
    [AddCommGroup M] [Module E M] [Module R M] [IsScalarTower R E M]
    (φE : E →+* E) (φD : M →ₗ[R] M) (hφD : ∀ (e : E) (x : M), φD (e • x) = φE e • φD x)
    (γE : Γ → E →+* E) (γD : Γ → M →ₗ[R] M)
    (hγD : ∀ g (e : E) (x : M), γD g (e • x) = γE g e • γD g x)
    (hφγ : ∀ g x, φD (γD g x) = γD g (φD x)) {r : ℕ} (b b' : Module.Basis (Fin r) E M)
    (hb : ∀ j, b' j = φD (b j)) (ψE : E →ₗ[R] E)
    (hψφ : ∀ a x, ψE (φE a * x) = a * ψE x) (hψγ : ∀ g x, ψE (γE g x) = γE g (ψE x))
    (hψone : ψE 1 = 1) :
    ∃ ψ : M →ₗ[R] M, (∀ x, ψ (φD x) = x) ∧
      (∀ (a : E) x, ψ (φE a • x) = a • ψ x) ∧ ∀ g x, ψ (γD g x) = γD g (ψ x) := by
  let ψ : M →ₗ[R] M :=
    { toFun := fun z => ∑ j, ψE (b'.repr z j) • b j
      map_add' := fun z w => by
        simp only [map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c z => by
        simp only [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← algebraMap_smul E c z, map_smul, Finsupp.smul_apply, smul_eq_mul,
          ← Algebra.smul_def, map_smul, smul_assoc] }
  have hψ : ∀ z, ψ z = ∑ j, ψE (b'.repr z j) • b j := fun z => rfl
  have hdec : ∀ z : M, z = ∑ j, b'.repr z j • φD (b j) := by
    intro z
    conv_lhs => rw [← b'.sum_repr z]
    simp only [hb]
  have hkey : ∀ (x : E) (y : M), ψ (x • φD y) = ψE x • y := by
    intro x y
    have hy : φD y = ∑ j, φE (b.repr y j) • b' j := by
      conv_lhs => rw [← b.sum_repr y]
      rw [map_sum]
      simp only [hφD, hb]
    rw [hψ, hy, Finset.smul_sum]
    simp only [smul_smul]
    rw [b'.repr_sum_self]
    conv_rhs => rw [← b.sum_repr y, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, hψφ, smul_smul, mul_comm]
  refine ⟨ψ, fun x => ?_, fun a z => ?_, fun g z => ?_⟩
  · have := hkey 1 x
    rwa [one_smul, hψone, one_smul] at this
  · rw [hψ, hψ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hψφ, mul_smul]
  · rw [hψ z, map_sum]
    conv_lhs => rw [hdec z, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hγD, ← hφγ, hkey, hψγ, hγD]

set_option maxHeartbeats 2000000 in

theorem psiD_exists : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), ∃ ψ : W.DD T →ₗ[↥(OL LL)] W.DD T, (∀ x, ψ (W.φD T x) = x) ∧ (∀ (a : W.EE) x, ψ (W.φE a • x) = a • ψ x) ∧ ∀ g x, ψ (W.γD T g x) = W.γD T g (ψ x) := by
  intro D HW F l _ K s LL h W T
  obtain ⟨r, b, b', hb⟩ := GlobalTheory.T.wachEtaleModule_frobenius_basis D HW F l K s LL h T
  obtain ⟨ψE, hψφ, hψγ, hψ1⟩ := GlobalTheory.T.wachFunctorRing_psiOperator_exists_of_good D HW F l K s LL h
  have hψone : ψE 1 = 1 := by
    have := hψ1 0 (Fact.out : l.Prime).pos 1
    simpa using this
  exact psi_of_etale_basis (W.φE : W.EE →+* W.EE) (W.φD T) (W.φD_smul T)
    (fun g => (W.γE g : W.EE →+* W.EE)) (W.γD T) (W.γD_smul T) (W.φγ_comm T) b b' hb ψE hψφ hψγ hψone

end GlobalTheory
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_psi_operator_etale_phiGamma_module : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), ∃ ψ : W.DD T →ₗ[↥(OL LL)] W.DD T, (∀ x, ψ (W.φD T x) = x) ∧ (∀ (a : W.EE) x, ψ (W.φE a • x) = a • ψ x) ∧ ∀ g x, ψ (W.γD T g x) = W.γD T g (ψ x) := by
  atlas_forward_decl GlobalTheory.psiD_exists
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem fontaine_litFont_assembled :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.InvariantsGenerators.LitFont D HW F := by
  intro D HW F
  unfold Formalism.MainNotions.InvariantsGenerators.LitFont
  intro l _ K LL hA
  unfold Formalism.MainNotions.InvariantsGenerators.FontCore
  have hff := GlobalTheory.T.wachFunctor_fullyFaithful D HW F l K 1 LL hA.2.2
  have hex := GlobalTheory.T.etaleFunctor_exact_on_lattices D HW F l K 1 LL hA.2.2
  have hpd := GlobalTheory.T.exists_psi_operator_etale_phiGamma_module D HW F l K 1 LL hA.2.2
  have hpe := GlobalTheory.T.wachFunctorRing_psiOperator_exists_of_good D HW F l K 1 LL hA.2.2
  have hfr := GlobalTheory.T.etaleRing_free_over_frobenius_image D HW F l K 1 LL hA.2.2
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨hff, hex, ?_, hpd⟩
  obtain ⟨ψ, h1, h2, h3⟩ := hpe
  refine ⟨ψ, h1, h2, ?_, ?_⟩
  · rw [hp]; exact h3
  · intro x
    obtain ⟨c, hc, -⟩ := hfr x
    rw [hp]
    exact ⟨c, hc⟩

end GlobalTheory
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaine_fullFaithful_exact_psi : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.InvariantsGenerators.LitFont D HW F := by
  atlas_forward_decl GlobalTheory.fontaine_litFont_assembled
end
