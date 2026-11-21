import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
import BuildAid.ForwardExisting

section
open TensorProduct

namespace GlobalTheory.LocalCoord

theorem exists_frobenius (k A : Type) [Field k] [Finite k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (m : Ideal A) (hm : m.IsMaximal) :
    ∃ F : A →ₐ[k] A, (∀ a, a - F a ∈ m) ∧ ∀ a, ∃ c, F a = a * a * c := by
  letI := Fintype.ofFinite k
  letI := Ideal.Quotient.field m
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  haveI : Finite (A ⧸ m) := Module.finite_of_finite k
  letI := Fintype.ofFinite (A ⧸ m)
  have hpow : ∀ (n : ℕ) (a : A),
      (FiniteField.frobeniusAlgHom k A ^ n) a = a ^ (Fintype.card k ^ n) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [pow_succ', AlgHom.mul_apply, ih, FiniteField.coe_frobeniusAlgHom, pow_succ, pow_mul]
  have hc : Fintype.card (A ⧸ m) = Fintype.card k ^ Module.finrank k (A ⧸ m) :=
    Module.card_eq_pow_finrank
  refine ⟨FiniteField.frobeniusAlgHom k A ^ Module.finrank k (A ⧸ m), fun a => ?_, fun a => ?_⟩
  · rw [hpow, ← hc, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, FiniteField.pow_card,
      sub_self]
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Fintype.one_lt_card (α := A ⧸ m))
    exact ⟨a ^ d, by rw [hpow, ← hc, hd]; ring⟩

theorem span_of_derivation {k A K B W : Type} [Field k] [PerfectField k] [CommRing A]
    [Algebra k A] [Field K] [Algebra k K] [CommRing B] [Algebra K B] [AddCommGroup W]
    [Module K W] [Module k W] [IsScalarTower k K W]
    (φ : K ⊗[k] A →ₐ[K] B) (χ : B →ₐ[K] K) {g : ℕ}
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ ≤ nilradical _)
    (t : Fin g → B) (s : B) (hs : χ s ≠ 0) (ht : ∀ i, χ (t i) = 0)
    (hb : ∀ b, χ b = 0 → s * b ∈ Ideal.span (Set.range t))
    (D : A →ₗ[k] W)
    (hD : ∀ a b, D (a * b) = χ (φ (1 ⊗ₜ a)) • D b + χ (φ (1 ⊗ₜ b)) • D a)
    (hN : ∀ a ∈ nilradical A, D a = 0) :
    ∃ w : Fin g → W, ∀ a, χ (φ (1 ⊗ₜ a)) = 0 → D a ∈ Submodule.span K (Set.range w) := by
  classical
  let E : K ⊗[k] A →ₗ[K] W := D.liftBaseChange K
  have hψ : ∀ (c : K) (a : A), χ (φ (c ⊗ₜ a)) = c * χ (φ (1 ⊗ₜ a)) := by
    intro c a
    rw [← smul_eq_mul, ← map_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hE : ∀ x y, E (x * y) = χ (φ x) • E y + χ (φ y) • E x := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' h h' => simp only [add_mul, map_add, h, h', add_smul, smul_add]; abel
    | tmul c a =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' h h' => simp only [mul_add, map_add, h, h', add_smul, smul_add]; abel
      | tmul d b =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hψ c, hψ d]
        simp only [E, LinearMap.liftBaseChange_tmul, hD, smul_add, smul_smul]
        congr 2 <;> ring
  have hEN : ∀ x ∈ nilradical (K ⊗[k] A), E x = 0 := by
    intro x hx
    haveI : IsReduced (A ⧸ nilradical A) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
    haveI := GlobalTheory.ReducedAlg.isReduced_field_tensor (k := k) K (A ⧸ nilradical A)
    let π := Algebra.TensorProduct.map (AlgHom.id k K) (Ideal.Quotient.mkₐ k (nilradical A))
    have h0 : π x = 0 := ((mem_nilradical.mp hx).map π).eq_zero
    let D' : (A ⧸ nilradical A) →ₗ[k] W :=
      (((nilradical A).restrictScalars k).liftQ D (fun a ha => hN a ha)).comp
        (Submodule.Quotient.restrictScalarsEquiv k (nilradical A)).symm.toLinearMap
    have key : ∀ y, E y = D'.liftBaseChange K (π y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' h h' => simp only [map_add, h, h']
      | tmul d b => rfl
    rw [key, h0, map_zero]
  choose l hl using hφ
  refine ⟨fun i => E (l (t i)), fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hb _ ha)
  have h1 : E (l s * 1 ⊗ₜ a - ∑ i, l (c i) * l (t i)) = 0 := by
    refine hEN _ (hker ?_)
    rw [RingHom.mem_ker, map_sub, map_mul, map_sum]
    simp only [map_mul, hl, hc, sub_self]
  rw [map_sub, map_sum, sub_eq_zero] at h1
  simp only [hE, hl, ha, ht, zero_smul, add_zero] at h1
  have h2 : E (1 ⊗ₜ a) = D a := by simp [E]
  rw [h2] at h1
  rw [← Submodule.smul_mem_iff _ hs, h1]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_local_coordinates :
    ∀ (k A K B : Type) [Field k] [Finite k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [Field K] [Algebra k K] [CommRing B] [Algebra K B] (φ : TensorProduct k K A →ₐ[K] B) (χ : B →ₐ[K] K) (g : ℕ) (m : Ideal A), Function.Surjective φ → RingHom.ker φ ≤ nilradical _ → (∀ a : A, a ∈ m ↔ χ (φ (1 ⊗ₜ a)) = 0) → m.IsMaximal → (∃ (t : Fin g → B) (s : B), χ s ≠ 0 ∧ (∀ i, χ (t i) = 0) ∧ ∀ b, χ b = 0 → s * b ∈ Ideal.span (Set.range t)) → IsReduced B → ∃ (u : Fin g → A) (s : A), s ∉ m ∧ (∀ i, u i ∈ m) ∧ ∀ a ∈ m, s * a ∈ Ideal.span (Set.range u) ⊔ nilradical A := by
  intro k A K B _ _ _ _ _ _ _ _ _ φ χ g m hφ hker hm hmax ⟨t, s, hs, ht, hb⟩ _
  classical
  letI := Ideal.Quotient.field m
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨F, hF, hF2⟩ := exists_frobenius k A m hmax
  let ι : A →ₐ[k] K := ((χ.comp φ).restrictScalars k).comp Algebra.TensorProduct.includeRight
  have hι : ∀ a, ι a = χ (φ (1 ⊗ₜ a)) := fun a => rfl
  let ι' : (A ⧸ m) →+* K := Ideal.Quotient.lift m ι fun a ha => (hm a).mp ha
  let N' : Submodule (A ⧸ m) m.Cotangent :=
    Submodule.span _ {y | ∃ x : m, (x : A) ∈ nilradical A ∧ m.toCotangent x = y}
  haveI : Module.Finite A m.Cotangent :=
    Module.Finite.of_surjective m.toCotangent m.toCotangent_surjective
  haveI : Module.Finite (A ⧸ m) m.Cotangent := Module.Finite.of_restrictScalars_finite A _ _
  let r := Module.finrank (A ⧸ m) (m.Cotangent ⧸ N')
  let b := Module.finBasis (A ⧸ m) (m.Cotangent ⧸ N')
  let p : m → m.Cotangent ⧸ N' := fun x => N'.mkQ (m.toCotangent x)
  have hpadd : ∀ x y, p (x + y) = p x + p y := fun x y => by simp only [p, map_add]
  have hpsmul : ∀ (a : A) x, p (a • x) = Ideal.Quotient.mk m a • p x := fun a x => by
    simp only [p, map_smul]; rfl
  have hpsurj : Function.Surjective p := N'.mkQ_surjective.comp m.toCotangent_surjective
  let L : m → Fin r → K := fun x j => ι' (b.repr (p x) j)
  have hLadd : ∀ x y, L (x + y) = L x + L y := fun x y => by
    ext j; simp only [L, hpadd, map_add, Finsupp.add_apply, Pi.add_apply]
  have hLsmul : ∀ (a : A) x, L (a • x) = ι a • L x := fun a x => by
    ext j
    simp only [L, hpsmul, map_smul, Finsupp.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]
    rfl
  let D : A →ₗ[k] Fin r → K :=
    { toFun := fun a => L ⟨a - F a, hF a⟩
      map_add' := fun a a' => by
        rw [← hLadd]; congr 1; ext; simp only [map_add, Submodule.coe_add]; ring
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← algebraMap_smul K c (L _), ← ι.commutes, ← hLsmul]
        congr 1; ext
        change c • a - F (c • a) = algebraMap k A c * (a - F a)
        rw [map_smul, ← Algebra.smul_def, smul_sub] }
  have hιF : ∀ a, ι (F a) = ι a := fun a => by
    have := (hm _).mp (hF a)
    rw [← hι, map_sub, sub_eq_zero] at this
    exact this.symm
  obtain ⟨w, hw⟩ := span_of_derivation φ χ hφ hker t s hs ht hb D (fun a a' => by
      change L _ = ι a • L _ + ι a' • L _
      rw [← hιF a', ← hLsmul, ← hLsmul, ← hLadd]
      congr 1; ext
      simp only [map_mul, Submodule.coe_add, SetLike.val_smul, smul_eq_mul]
      ring) (fun a ha => by
      have : p ⟨a - F a, hF a⟩ = 0 := by
        refine (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨_, ?_, rfl⟩)
        exact sub_mem ha ((mem_nilradical.mp ha).map F)
      change L _ = 0
      ext j
      simp [L, this])
  choose v hv using hpsurj
  have hDL : ∀ x : m, D x = L x := fun x => by
    obtain ⟨c, hc⟩ := hF2 x
    have h1 : L x = L ⟨x - F x, hF x⟩ + L ((x * c : A) • x) := by
      rw [← hLadd]; congr 1; ext
      simp only [hc, Submodule.coe_add, SetLike.val_smul, smul_eq_mul]
      ring
    rw [h1, hLsmul, map_mul, hι, (hm _).mp x.2, zero_mul, zero_smul, add_zero]
    rfl
  have hrg : r ≤ g := by
    have htop : Submodule.span K (Set.range w) = ⊤ := by
      rw [eq_top_iff, ← (Pi.basisFun K (Fin r)).span_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have : Pi.basisFun K (Fin r) j = D (v (b j)) := by
        rw [hDL]
        ext i
        simp only [L, hv, Module.Basis.repr_self, Pi.basisFun_apply, Finsupp.single_apply,
          Pi.single_apply]
        by_cases h : j = i
        · simp [h]
        · simp [h, Ne.symm h]
      rw [this]
      exact hw _ ((hm _).mp (v (b j)).2)
    have := finrank_range_le_card (R := K) w
    rwa [Set.finrank, htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at this
  let u : Fin g → A := fun i => if h : i.1 < r then (v (b ⟨i.1, h⟩) : A) else 0
  have hu : ∀ j : Fin r, (v (b j) : A) ∈ Ideal.span (Set.range u) := fun j =>
    Ideal.subset_span ⟨⟨j.1, lt_of_lt_of_le j.2 hrg⟩, by simp [u]⟩
  have hle : m ≤ (Ideal.span (Set.range u) ⊔ nilradical A) ⊔ m • m := by
    set J := (Ideal.span (Set.range u) ⊔ nilradical A) ⊔ m • m with hJ
    have hk : ∀ y ∈ N', ∀ x : m, m.toCotangent x = y → (x : A) ∈ J := by
      intro y hy
      have : ∃ z : m, (z : A) ∈ nilradical A ∧ m.toCotangent z = y := by
        induction hy using Submodule.span_induction with
        | mem y h => exact h
        | zero => exact ⟨0, zero_mem _, map_zero _⟩
        | add y y' _ _ h h' =>
          obtain ⟨z, hz, rfl⟩ := h
          obtain ⟨z', hz', rfl⟩ := h'
          exact ⟨z + z', add_mem hz hz', map_add _ _ _⟩
        | smul c y _ h =>
          obtain ⟨z, hz, rfl⟩ := h
          obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
          exact ⟨c • z, Ideal.mul_mem_left _ _ hz, by rw [map_smul]; rfl⟩
      obtain ⟨z, hz, rfl⟩ := this
      intro x hx
      have h2 := m.toCotangent_eq.mp hx
      have : (x : A) = z + (x - z) := by ring
      rw [this]
      refine add_mem (Ideal.mem_sup_left (Ideal.mem_sup_right hz)) (Ideal.mem_sup_right ?_)
      rwa [pow_two] at h2
    have hall : ∀ y : m.Cotangent ⧸ N', ∃ z : m, (z : A) ∈ J ∧ p z = y := by
      intro y
      have hy : y ∈ Submodule.span (A ⧸ m) (Set.range b) := by rw [b.span_eq]; trivial
      induction hy using Submodule.span_induction with
      | mem y h =>
        obtain ⟨j, rfl⟩ := h
        exact ⟨v (b j), Ideal.mem_sup_left (Ideal.mem_sup_left (hu j)), hv _⟩
      | zero => exact ⟨0, zero_mem _, by simp [p]⟩
      | add y y' _ _ h h' =>
        obtain ⟨z, hz, rfl⟩ := h
        obtain ⟨z', hz', rfl⟩ := h'
        exact ⟨z + z', add_mem hz hz', hpadd _ _⟩
      | smul c y _ h =>
        obtain ⟨z, hz, rfl⟩ := h
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
        exact ⟨c • z, Ideal.mul_mem_left _ _ hz, hpsmul _ _⟩
    intro a ha
    obtain ⟨z, hz, hp⟩ := hall (p ⟨a, ha⟩)
    have h3 := hk _ ((Submodule.Quotient.eq N').mp hp.symm) (⟨a, ha⟩ - z) (map_sub _ _ _)
    have : a = (a - z) + z := by ring
    rw [this]
    exact add_mem h3 hz
  obtain ⟨c, hc, hcle⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (IsNoetherian.noetherian m) le_rfl hle
  refine ⟨u, c, fun h => hmax.ne_top ?_, fun i => ?_, fun a ha => ?_⟩
  · rw [Ideal.eq_top_iff_one]
    have := sub_mem h hc
    rwa [sub_sub_cancel] at this
  · simp only [u]
    split_ifs
    · exact Subtype.prop _
    · exact zero_mem _
  · exact hcle (Submodule.smul_mem_pointwise_smul a c m ha)

end GlobalTheory.LocalCoord
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
namespace GlobalTheory.ZJ.FibreCoord

theorem exists_local_generators {K B : Type} [Field K] [CommRing B] [Algebra K B] {g : ℕ}
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap K B)) (χ : B →ₐ[K] K) :
    ∃ (t : Fin g → B) (s : B), χ s ≠ 0 ∧ (∀ i, χ (t i) = 0) ∧
      ∀ b, χ b = 0 → s * b ∈ Ideal.span (Set.range t) := by
  haveI := AugCot.smooth_of_locally h
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  obtain ⟨e⟩ := AugCot.nonempty_basis_of_locally χ h
  choose t ht using fun i => (RingHom.ker χ).toCotangent_surjective (e i)
  let m := RingHom.ker χ
  let J : Ideal B := Ideal.span (Set.range fun i => (t i : B))
  have hle : m ≤ J ⊔ m • m := by
    intro b hb
    have h1 : AugCot.d χ (b - ∑ i, e.repr (AugCot.d χ b) i • (t i : B)) = 0 := by
      rw [map_sub, map_sum]
      simp only [map_smul, AugCot.d_coe]
      have := e.sum_repr (AugCot.d χ b)
      rw [sub_eq_zero]
      conv_lhs => rw [← this]
      exact Finset.sum_congr rfl fun i _ => by rw [← ht i]
    rw [AugCot.d_eq_zero_iff] at h1
    have h2 : χ (b - ∑ i, e.repr (AugCot.d χ b) i • (t i : B)) = 0 := by
      have hb' : χ b = 0 := hb
      have ht' : ∀ i, χ (t i) = 0 := fun i => (t i).2
      simp [map_sum, hb', ht']
    rw [h2, map_zero, sub_zero, pow_two] at h1
    have h3 : ∑ i, e.repr (AugCot.d χ b) i • (t i : B) ∈ J :=
      Ideal.sum_mem _ fun i _ => by
        rw [Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    have := Ideal.add_mem _ (Ideal.mem_sup_left (T := m • m) h3) (Ideal.mem_sup_right (S := J) h1)
    simpa using this
  obtain ⟨r, hr, hr'⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m
    (Submodule.map (Submodule.mkQ J) m) (Submodule.FG.map _ (IsNoetherian.noetherian m)) (by
      rw [← Submodule.map_smul'', Submodule.map_le_iff_le_comap, Submodule.comap_map_mkQ]
      exact hle)
  refine ⟨fun i => t i, r, ?_, fun i => (t i).2, fun b hb => ?_⟩
  · have : χ (r - 1) = 0 := hr
    rw [map_sub, map_one, sub_eq_zero] at this
    simp [this]
  · have := hr' (Submodule.mkQ J b) (Submodule.mem_map_of_mem hb)
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact this

theorem mem_nilradical_of_forall_algHom {K T : Type} [Field K] [IsAlgClosed K] [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] (a : T) (h : ∀ χ : T →ₐ[K] K, χ a = 0) : a ∈ nilradical T := by
  haveI : IsJacobsonRing T := isJacobsonRing_of_finiteType (A := K)
  have h1 : nilradical T = Ideal.jacobson (nilradical T) :=
    (IsJacobsonRing.out inferInstance (Ideal.radical_isRadical ⊥)).symm
  rw [h1, Ideal.jacobson, Ideal.mem_sInf]
  rintro M ⟨-, hM⟩
  letI := Ideal.Quotient.field M
  haveI : Module.Finite K (T ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (T ⧸ M)
  let e : T ⧸ M →ₐ[K] K := IsAlgClosed.lift
  have := h (e.comp (Ideal.Quotient.mkₐ K M))
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact (map_eq_zero_iff e e.toRingHom.injective).mp this

open TensorProduct in

theorem exists_coords_ring {R S K B : Type} [CommRing R] [CommRing S] [Field K] [IsAlgClosed K] [CommRing B]
    [Algebra K B] {g : ℕ} (α : R →+* S) (hα : α.FiniteType) (ψ : S →+* K) [Finite (S ⧸ RingHom.ker ψ)]
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap K B))
    (β : S →+* B) (hβ : β.comp α = (algebraMap K B).comp (ψ.comp α))
    (hgen : Algebra.adjoin K (Set.range β) = ⊤)
    (hpt : ∀ ψ' : S →+* K, ψ'.comp α = ψ.comp α → ∃ χ : B →ₐ[K] K, (χ : B →+* K).comp β = ψ') :
    ∃ (u : Fin g → S) (s : S), s ∉ RingHom.ker ψ ∧ (∀ i, u i ∈ RingHom.ker ψ) ∧
      ∀ a ∈ RingHom.ker ψ, s * a ∈ Ideal.span (Set.range u) ⊔ ((RingHom.ker (ψ.comp α)).map α).radical := by
  letI := α.toAlgebra
  haveI : Algebra.FiniteType R S := hα
  set P : Ideal R := RingHom.ker (ψ.comp α) with hP
  haveI : P.IsPrime := RingHom.ker_isPrime _
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime _
  haveI : Finite (R ⧸ P) := Finite.of_injective _ (Ideal.quotientMap_injective (I := RingHom.ker ψ) (f := α))
  haveI hPm : P.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
  have hmm : (RingHom.ker ψ).IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
  letI := Ideal.Quotient.field P
  let Q : Ideal S := P.map (algebraMap R S)
  letI : Algebra (R ⧸ P) K := (RingHom.kerLift (ψ.comp α)).toAlgebra
  haveI : Algebra.FiniteType (R ⧸ P) (S ⧸ Q) := Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  letI : Algebra (R ⧸ P) B := ((algebraMap K B).comp (algebraMap (R ⧸ P) K)).toAlgebra
  haveI : IsScalarTower (R ⧸ P) K B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hβ' : ∀ r, β (α r) = algebraMap K B (ψ (α r)) := fun r => congr($hβ r)
  have hQβ : ∀ a ∈ Q, β a = 0 := by
    intro a ha
    refine (show Q ≤ RingHom.ker β from Ideal.map_le_iff_le_comap.mpr fun r hr => ?_) ha
    have hr' : ψ (α r) = 0 := hr
    change β (α r) = 0
    rw [hβ', hr', map_zero]
  have hQψ : Q ≤ RingHom.ker ψ := Ideal.map_le_iff_le_comap.mpr fun r hr => hr
  let β' : S ⧸ Q →ₐ[R ⧸ P] B :=
    { Ideal.Quotient.lift Q β hQβ with
      commutes' := fun r => by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        exact hβ' r }
  let φ : K ⊗[R ⧸ P] (S ⧸ Q) →ₐ[K] B := Algebra.TensorProduct.lift (Algebra.ofId K B) β' fun _ _ => Commute.all _ _
  have hφ : ∀ a : S, φ (1 ⊗ₜ Ideal.Quotient.mk Q a) = β a := fun a => by
    simp [φ, β']
  have hsurj : Function.Surjective φ := by
    rw [← AlgHom.range_eq_top, eq_top_iff, ← hgen]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨_, hφ a⟩
  have hker : RingHom.ker φ ≤ nilradical _ := by
    intro a ha
    refine mem_nilradical_of_forall_algHom (K := K) a fun χ' => ?_
    let ψ' : S →+* K := χ'.toRingHom.comp
      ((Algebra.TensorProduct.includeRight (R := R ⧸ P) (A := K) (B := S ⧸ Q)).toRingHom.comp (Ideal.Quotient.mk Q))
    obtain ⟨χ, hχ⟩ := hpt ψ' (by
      ext r
      have : (1 : K) ⊗ₜ[R ⧸ P] (Ideal.Quotient.mk Q (α r)) = algebraMap K _ (ψ (α r)) := by
        change (1 : K) ⊗ₜ[R ⧸ P] (algebraMap (R ⧸ P) (S ⧸ Q) (Ideal.Quotient.mk P r)) =
          (algebraMap (R ⧸ P) K (Ideal.Quotient.mk P r)) ⊗ₜ 1
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      change χ' ((1 : K) ⊗ₜ[R ⧸ P] (Ideal.Quotient.mk Q (α r))) = ψ (α r)
      rw [this, AlgHom.commutes]
      rfl)
    have e : χ.comp φ = χ' := by
      ext b
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      change χ (φ (1 ⊗ₜ Ideal.Quotient.mk Q b)) = χ' (1 ⊗ₜ Ideal.Quotient.mk Q b)
      rw [hφ]
      exact congr($hχ b)
    have ha' : φ a = 0 := ha
    rw [← e, AlgHom.comp_apply, ha', map_zero]
  obtain ⟨χ, hχ⟩ := hpt ψ rfl
  have hχ' : ∀ a, χ (β a) = ψ a := fun a => congr($hχ a)
  haveI := AugCot.smooth_of_locally h
  have hmem : ∀ a : S, Ideal.Quotient.mk Q a ∈ (RingHom.ker ψ).map (Ideal.Quotient.mk Q) ↔ a ∈ RingHom.ker ψ :=
    fun a => by
      rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hQψ]
  obtain ⟨u, s, hs, hu, hus⟩ := GlobalTheory.LocalCoord.exists_local_coordinates (R ⧸ P) (S ⧸ Q) K B φ χ g ((RingHom.ker ψ).map (Ideal.Quotient.mk Q))
    hsurj hker (fun a => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [hmem, hφ, hχ', RingHom.mem_ker])
    ((Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hmm).resolve_left fun ht =>
      hmm.ne_top (Ideal.eq_top_iff_one _ |>.mpr ((hmem 1).mp (ht ▸ trivial))))
    (exists_local_generators h χ) (isReduced_of_smooth_of_isIntegrallyClosed K B)
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  choose v hv using fun i => Ideal.Quotient.mk_surjective (u i)
  refine ⟨v, s, fun h => hs ((hmem s).mpr h), fun i => (hmem _).mp (hv i ▸ hu i), fun a ha => ?_⟩
  have h1 := hus _ ((hmem a).mpr ha)
  have h2 : Ideal.span (Set.range u) ⊔ nilradical (S ⧸ Q) =
      (Ideal.span (Set.range v) ⊔ Q.radical).map (Ideal.Quotient.mk Q) := by
    rw [Ideal.map_sup, Ideal.map_span, ← Set.range_comp, Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]), Ideal.map_quotient_self]
    congr 3
    exact funext fun i => (hv i).symm
  rw [h2, ← map_mul, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_assoc, sup_eq_left.mpr (Ideal.le_radical (I := Q))] at h1
  exact h1

open TensorProduct in

theorem exists_chart_ring {G Z H : Scheme.{0}} (f : G ⟶ Z) {R S K : Type} [CommRing R] [CommRing S] [Field K]
    {g : ℕ} (α : R →+* S) (ρ : R →+* K) (iW : Sp S ⟶ G) (iV : Sp R ⟶ Z) [IsOpenImmersion iW] [IsOpenImmersion iV]
    (hsq : iW ≫ f = spMap α ≫ iV) (ζ : Sp K ⟶ Z) (hζ : ζ = spMap ρ ≫ iV) (h : H ⟶ pullback f ζ)
    [IsClosedImmersion h] [SmoothOfRelativeDimension g (h ≫ pullback.snd f ζ)]
    (hpt : ∀ x : Sp K ⟶ pullback f ζ, x ≫ pullback.snd f ζ = 𝟙 _ → ∃ c : Sp K ⟶ H, c ≫ h = x) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra K B) (β : S →+* B),
      RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap K B) ∧
      β.comp α = (algebraMap K B).comp ρ ∧ Algebra.adjoin K (Set.range β) = ⊤ ∧
      ∀ ψ' : S →+* K, ψ'.comp α = ρ → ∃ χ : B →ₐ[K] K, (χ : B →+* K).comp β = ψ' := by
  letI := α.toAlgebra
  letI := ρ.toAlgebra
  let T := K ⊗[R] S
  let j : Sp T ⟶ pullback f ζ := (pullbackSpecIso R K S).inv ≫ (pullbackSymmetry _ _).hom ≫
    pullback.map (spMap α) (spMap ρ) f ζ iW (𝟙 _) iV hsq.symm (by rw [hζ, Category.id_comp])
  haveI : IsOpenImmersion j := by
    dsimp only [j]
    infer_instance
  let iL : K →+* T := Algebra.TensorProduct.includeLeftRingHom
  let iR : S →+* T := (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := S) : S →+* T)
  have hj1 : j ≫ pullback.fst f ζ = spMap iR ≫ iW := by
    simp only [j, Category.assoc, pullback.lift_fst]
    rw [pullbackSymmetry_hom_comp_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  have hj2 : j ≫ pullback.snd f ζ = spMap iL := by
    simp only [j, Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst]
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.mp (inferInstance : IsClosedImmersion (pullback.snd h j))
  let I' : Ideal T := I
  have hmk : e.inv ≫ pullback.snd h j = spMap (Ideal.Quotient.mk I') := by
    rw [he, Iso.inv_hom_id_assoc]
  refine ⟨T ⧸ I', inferInstance, inferInstance, (Ideal.Quotient.mk I').comp iR, ?_, ?_, ?_, ?_⟩
  · rw [AugCot.locally_iff_smoothOfRelativeDimension]
    have : Spec.map (CommRingCat.ofHom (algebraMap K (T ⧸ I'))) =
        (e.inv ≫ pullback.fst h j) ≫ h ≫ pullback.snd f ζ := by
      rw [Category.assoc, pullback.condition_assoc, hj2, ← Category.assoc, hmk, ← Spec.map_comp]
      rfl
    rw [this]
    have := smoothOfRelativeDimension_comp 0 g (e.inv ≫ pullback.fst h j) (h ≫ pullback.snd f ζ)
    rwa [zero_add] at this
  · ext r
    change Ideal.Quotient.mk I' (1 ⊗ₜ algebraMap R S r) = Ideal.Quotient.mk I' (algebraMap R K r ⊗ₜ 1)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  · rw [eq_top_iff]
    rintro b -
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    induction b using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | tmul a s =>
      have : Ideal.Quotient.mk I' (a ⊗ₜ s) = a • Ideal.Quotient.mk I' (1 ⊗ₜ s) := by
        rw [← Ideal.Quotient.mkₐ_eq_mk K, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [this]
      exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self (f := (Ideal.Quotient.mk I').comp iR) s)) _
  · intro ψ' hψ'
    let ψa : S →ₐ[R] K := { ψ' with commutes' := fun r => congr($hψ' r) }
    let θ : T →ₐ[K] K := Algebra.TensorProduct.lift (AlgHom.id K K) ψa fun _ _ => Commute.all _ _
    have hθ : spMap (θ : T →+* K) ≫ spMap iL = 𝟙 _ := by
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext a
      exact θ.commutes a
    obtain ⟨c, hc⟩ := hpt (spMap (θ : T →+* K) ≫ j) (by rw [Category.assoc, hj2, hθ])
    let χ₀ : T ⧸ I' →+* K := (Spec.preimage (pullback.lift c _ hc ≫ e.hom)).hom
    have hχ : χ₀.comp (Ideal.Quotient.mk I') = θ := by
      have : spMap (χ₀.comp (Ideal.Quotient.mk I')) = spMap (θ : T →+* K) := by
        have h1 : spMap χ₀ = pullback.lift c _ hc ≫ e.hom := Spec.map_preimage _
        change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I') ≫ CommRingCat.ofHom χ₀) = _
        rw [Spec.map_comp]
        change spMap χ₀ ≫ spMap (Ideal.Quotient.mk I') = _
        rw [h1, ← hmk, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_snd]
      exact congr($(Spec.map_injective this).hom)
    refine ⟨{ χ₀ with commutes' := fun a => ?_ }, ?_⟩
    · exact (congr($hχ (algebraMap K T a)) :).trans (θ.commutes a)
    · ext s
      have h3 : θ (1 ⊗ₜ s) = ψ' s := by
        simp only [θ, T, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
        rfl
      exact (congr($hχ (1 ⊗ₜ s)) :).trans h3

theorem maximalIdeal_stalk_eq {G Z : Scheme.{0}} (f : G ⟶ Z) {V : Z.Opens} {W : G.Opens} (hW : IsAffineOpen W)
    (hle : W ≤ f ⁻¹ᵁ V) (w : G) (hw : w ∈ W) {g : ℕ} (u : Fin g → Γ(G, W)) (s : Γ(G, W)) (m : Ideal Γ(G, W))
    (hm : m = (hW.primeIdealOf ⟨w, hw⟩).asIdeal) (hs : s ∉ m) (hu : ∀ i, u i ∈ m)
    (H : ∀ a ∈ m, s * a ∈ Ideal.span (Set.range u) ⊔
      ((m.comap (f.appLE V W hle).hom).map (f.appLE V W hle).hom).radical) :
    IsLocalRing.maximalIdeal (G.presheaf.stalk w) =
      Ideal.span (Set.range fun i => (G.presheaf.germ W w hw).hom (u i)) ⊔
        ((IsLocalRing.maximalIdeal (Z.presheaf.stalk (f w))).map (f.stalkMap w).hom).radical := by
  subst hm
  letI := G.presheaf.algebra_section_stalk (⟨w, hw⟩ : W)
  haveI := hW.isLocalization_stalk ⟨w, hw⟩
  have hmem : ∀ a : Γ(G, W), (G.presheaf.germ W w hw).hom a ∈ IsLocalRing.maximalIdeal (G.presheaf.stalk w) ↔
      a ∈ (hW.primeIdealOf ⟨w, hw⟩).asIdeal := fun a =>
    IsLocalization.AtPrime.to_map_mem_maximal_iff (G.presheaf.stalk w) (hW.primeIdealOf ⟨w, hw⟩).asIdeal a
  apply le_antisymm
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (hW.primeIdealOf ⟨w, hw⟩).asIdeal (G.presheaf.stalk w),
      Ideal.map_le_iff_le_comap]
    intro a ha
    have h1 := Ideal.mem_map_of_mem (G.presheaf.germ W w hw).hom (H a ha)
    have hsu : IsUnit ((G.presheaf.germ W w hw).hom s) := by
      by_contra hn
      exact hs ((hmem s).mp hn)
    rw [map_mul, Ideal.unit_mul_mem_iff_mem _ hsu, Ideal.map_sup, Ideal.map_span, ← Set.range_comp] at h1
    refine SetLike.le_def.mp (sup_le_sup_left (le_trans (Ideal.map_radical_le _) (Ideal.radical_mono ?_)) _) h1
    rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro r hr
    have e : (G.presheaf.germ W w hw).hom ((f.appLE V W hle).hom r) =
        (f.stalkMap w).hom ((Z.presheaf.germ V (f w) (hle hw)).hom r) := by
      have e' : f.appLE V W hle ≫ G.presheaf.germ W w hw = Z.presheaf.germ V (f w) (hle hw) ≫ f.stalkMap w := by
        refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap f V w (hle hw)).symm
        rw [Scheme.Hom.appLE, Category.assoc, G.presheaf.germ_res]
      exact congr($(e').hom r)
    have h2 := (hmem _).mpr hr
    rw [Ideal.mem_comap, RingHom.comp_apply]
    rw [e] at h2 ⊢
    exact Ideal.mem_map_of_mem _ fun hn => h2 (hn.map _)
  · refine sup_le (Ideal.span_le.mpr ?_) ?_
    · rintro _ ⟨i, rfl⟩
      exact (hmem _).mpr (hu i)
    · rw [Ideal.IsPrime.radical_le_iff inferInstance]
      exact IsLocalRing.map_maximalIdeal_le _

end FibreCoord
open FibreCoord

theorem Core.exists_coord : ∀ C : Core, C.HasTests → C.Fib → ∀ w : C.G.toScheme, IsClosed ({w} : Set C.G.toScheme) → ∃ (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), IsAffineOpen W ∧ C.Coord w W hw u := by
  intro C hT hF w hwc
  obtain ⟨-, hlft, -, hint, hflat, -, -, -, -, -, -, hdom, -⟩ := GlobalTheory.ZJ.core_basic C
  haveI := C.lft
  obtain ⟨p, _, b, hb, hbU⟩ := padicAlgCl_integral_points.1 C.G.toScheme (C.GG.hom ≫ C.π) w hwc
    (C.GG.hom ⁻¹ᵁ C.U) (by
      obtain ⟨z, hz, x, rfl⟩ := C.GG.hom.denseRange.inter_open_nonempty _ C.U.isOpen C.ne
      exact ⟨x, hz⟩)
  haveI := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  obtain ⟨τ⟩ := hT p (b ≫ C.GG.hom) (by
    rintro _ ⟨t, rfl⟩
    have := hbU ⟨t, rfl⟩
    rw [← Category.assoc, Scheme.Hom.comp_apply]
    exact this)
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (X := C.Z) (x := C.GG.hom w) (U := ⊤) trivial
  obtain ⟨W, hW, hw, hle⟩ := exists_isAffineOpen_mem_and_subset (X := C.G.toScheme) (x := w)
    (U := C.GG.hom ⁻¹ᵁ V) hzV
  have hle' : W ≤ C.GG.hom ⁻¹ᵁ V := hle
  have hxw : ∀ t, (rPt p ≫ b) t = w := fun t => by
    rw [Scheme.Hom.comp_apply, ← hb]
    congr 1
    rw [Subsingleton.elim t (IsLocalRing.closedPoint (kb p))]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
  have hr : Set.range (rPt p ≫ b) ⊆ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    rintro _ ⟨t, rfl⟩
    rw [hxw]
    exact hw
  let ψ : Γ(C.G.toScheme, W) →+* kb p := (Spec.preimage (IsOpenImmersion.lift hW.fromSpec (rPt p ≫ b) hr)).hom
  have hψ : spMap ψ ≫ hW.fromSpec = rPt p ≫ b := by
    have h1 : spMap ψ = IsOpenImmersion.lift hW.fromSpec (rPt p ≫ b) hr := Spec.map_preimage _
    rw [h1, IsOpenImmersion.lift_fac]
  have hm : RingHom.ker ψ = (hW.primeIdealOf ⟨w, hw⟩).asIdeal := by
    have h1 : spMap ψ (IsLocalRing.closedPoint (kb p)) = hW.primeIdealOf ⟨w, hw⟩ := by
      apply hW.fromSpec.isOpenEmbedding.injective
      rw [hW.fromSpec_primeIdealOf]
      refine (Scheme.Hom.comp_apply _ _ _).symm.trans ?_
      rw [hψ]
      exact hxw _
    rw [← h1, RingHom.ker_eq_comap_bot, ← IsLocalRing.maximalIdeal_eq_bot]
    rfl
  let α : Γ(C.Z, V) →+* Γ(C.G.toScheme, W) := (C.GG.hom.appLE V W hle').hom
  have hsq : hW.fromSpec ≫ C.GG.hom = spMap α ≫ hV.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec C.GG.hom hV hW hle').symm
  let h : pullback τ.H.hom (rPt p ≫ spMap τ.j) ⟶ pullback C.GG.hom (rPt p ≫ b ≫ C.GG.hom) :=
    pullback.lift (pullback.fst _ _ ≫ τ.f) (pullback.snd _ _) (by
      rw [Category.assoc, τ.f_over, pullback.condition_assoc, Category.assoc, τ.fac])
  have h1 : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f := pullback.lift_fst _ _ _
  have h2 : h ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  haveI := τ.imm h h1 h2
  haveI : SmoothOfRelativeDimension C.g (h ≫ pullback.snd _ _) := by
    rw [h2]
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := C.g)).of_isPullback
      (IsPullback.of_hasPullback _ _) τ.smooth
  obtain ⟨B, _, _, β, hB, hβ, hgen, hpt⟩ := exists_chart_ring (g := C.g) C.GG.hom α (ψ.comp α) hW.fromSpec
    hV.fromSpec hsq (rPt p ≫ b ≫ C.GG.hom) (by
      rw [← Category.assoc, ← hψ, Category.assoc, hsq, ← Category.assoc, ← Spec.map_comp]
      rfl) h (fun x hx => by
      obtain ⟨c, hc, hc'⟩ := hF p _ τ (x ≫ pullback.fst _ _) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hx, Category.id_comp])
      refine ⟨pullback.lift c (𝟙 _) (by rw [hc, Category.id_comp]), ?_⟩
      apply pullback.hom_ext
      · rw [Category.assoc, h1, pullback.lift_fst_assoc, hc']
      · rw [Category.assoc, h2, pullback.lift_snd, hx])
  haveI : Finite (Γ(C.G.toScheme, W) ⧸ RingHom.ker ψ) := by
    haveI := (jacobson_closedPoints_tools_int _ (C.GG.hom ≫ C.π)).2.1 w hwc
    letI := C.G.toScheme.presheaf.algebra_section_stalk (⟨w, hw⟩ : W)
    haveI := hW.isLocalization_stalk ⟨w, hw⟩
    haveI : Finite (C.G.toScheme.presheaf.stalk w ⧸ IsLocalRing.maximalIdeal (C.G.toScheme.presheaf.stalk w)) :=
      ‹Finite (C.G.toScheme.residueField w)›
    rw [hm, ← IsLocalization.AtPrime.comap_maximalIdeal (C.G.toScheme.presheaf.stalk w)
      (hW.primeIdealOf ⟨w, hw⟩).asIdeal]
    exact Finite.of_injective _ Ideal.quotientMap_injective
  obtain ⟨u, s, hs, hu, H⟩ := exists_coords_ring α
    (HasRingHomProperty.appLE @LocallyOfFiniteType C.GG.hom hlft ⟨V, hV⟩ ⟨W, hW⟩ hle') ψ hB β hβ hgen hpt
  exact ⟨W, hw, u, hW, maximalIdeal_stalk_eq C.GG.hom hW hle' w hw u s _ hm hs hu H⟩

end GlobalTheory.ZJ
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.exists_coord_reducedFibre_closedPoint : ∀ C : Core, C.HasTests → C.Fib → ∀ w : C.G.toScheme, IsClosed ({w} : Set C.G.toScheme) → ∃ (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), IsAffineOpen W ∧ C.Coord w W hw u := by
  atlas_forward_decl GlobalTheory.ZJ.Core.exists_coord
end
