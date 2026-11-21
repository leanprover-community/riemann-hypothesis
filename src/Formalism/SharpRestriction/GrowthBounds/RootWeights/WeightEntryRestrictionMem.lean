import Formalism.SharpRestriction.GrowthBounds.RootWeights.TwistSubEqMatrixSubst
import Formalism.SharpRestriction.GrowthBounds.RootWeights.GenericMatrixEvaluationDet

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def genericMatrixRootWeights (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord R n) :=
  (genMat R n).map fun x => algebraMap _ (GLCoord R n) x

def genericMatrixInverse (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord R n) :=
  ((genMat R n).adjugate).map fun x =>
    IsLocalization.Away.invSelf (genMat R n).det * algebraMap _ (GLCoord R n) x

def coefficientMap (R : Type*) [CommRing R] (n : ℕ) : R →+* GLCoord R n :=
  (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)).comp MvPolynomial.C

def genericTranslate {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) (GLCoord R n) :=
  matrixSubst LL S (coefficientMap R n) (genericMatrixInverse R n) (genericMatrixRootWeights R n) G

open Classical in

def weightComponent {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (nu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ m ∈ F.support.filter (fun m => wtS LL S m = nu), monomial m (F.coeff m)

def TorusActsThroughWeight : Prop :=
  ∀ (R B : Type) [CommRing R] [CommRing B] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (φ : R →+* B) (D : Fin n → Bˣ) (m : ι × Fin n →₀ ℕ) (c : R),
      matrixSubst LL S φ (Matrix.diagonal fun a => ((D a : Bˣ) : B)) (Matrix.diagonal fun a => (((D a)⁻¹ : Bˣ) : B))
        (monomial m c) = monomial m (φ c * ((∏ a, D a ^ (wtS LL S m a) : Bˣ) : B))

def BinomialStableContainsComponents : Prop :=
  ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (W : Submodule R (MvPolynomial (ι × Fin n) R)), (∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) →
    ∀ x ∈ W, ∀ nu, weightComponent LL S nu x ∈ W

def TwistExponentsAreWeightEntries : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι) (j : Fin n)
    (G : MvPolynomial (ι × Fin n) R),
      sDegs LL S j G = (genericTranslate LL S G).support.image (fun m => wtS LL S m j)

def GenericMonomialsSpecialise : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (k1 : Type) [CommRing k1] (φ : R →+* k1) (g0 g0inv : Matrix (Fin n) (Fin n) k1), g0 * g0inv = 1 →
    ∀ G : MvPolynomial (ι × Fin n) R, (matrixSubst LL S φ g0inv g0 G).support ⊆ (genericTranslate LL S G).support

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def laurentUnit (B : Type*) [CommRing B] : (LaurentPolynomial B)ˣ :=
  ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1), by rw [← LaurentPolynomial.T_add]; simp,
    by rw [← LaurentPolynomial.T_add]; simp⟩

theorem laurentUnit_zpow (B : Type*) [CommRing B] (w : ℤ) :
    (((laurentUnit B) ^ w : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) = LaurentPolynomial.T w := by
  have hinv : (((laurentUnit B)⁻¹ : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) = LaurentPolynomial.T (-1) := rfl
  have hval : (((laurentUnit B) : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) = LaurentPolynomial.T 1 := rfl
  induction w using Int.induction_on with
  | zero => simp [LaurentPolynomial.T_zero]
  | succ i ih => rw [zpow_add_one, Units.val_mul, ih, hval, ← LaurentPolynomial.T_add]
  | pred i ih => rw [zpow_sub_one, Units.val_mul, ih, hinv, ← LaurentPolynomial.T_add]; rfl

theorem binomialOperator_monomial {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) (c : R) :
    binomPol R LL S a k (monomial m c) = monomial m (c * ((Ring.choose (wtS LL S m a) k : ℤ) : R)) := by
  have hm : (monomial m c : MvPolynomial (ι × Fin n) R) = c • (MvPolynomial.basisMonomials (ι × Fin n) R) m := by
    rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hm, LinearMap.map_smul]
  simp only [binomPol]
  rw [Module.Basis.constr_basis, MvPolynomial.smul_monomial, smul_eq_mul]

section fwd

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι) (j : Fin n)
  (Pr : ℤ → Prop)

def weightEntryPropertySubmodule : Submodule R (MvPolynomial (ι × Fin n) R) where
  carrier := {y | ∀ (k1 : Type) [CommRing k1] (φ : R →+* k1) (g0 g0inv : Matrix (Fin n) (Fin n) k1),
    g0 * g0inv = 1 → ∀ m ∈ (matrixSubst LL S φ g0inv g0 y).support, Pr (wtS LL S m j)}
  zero_mem' := by
    intro k1 _ φ g0 g0inv _ m hm
    simp at hm
  add_mem' := by
    classical
    intro x y hx hy k1 _ φ g0 g0inv h m hm
    rw [map_add] at hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h1 | h1
    · exact hx k1 φ g0 g0inv h m h1
    · exact hy k1 φ g0 g0inv h m h1
  smul_mem' := by
    intro c y hy k1 _ φ g0 g0inv h m hm
    rw [MvPolynomial.smul_eq_C_mul, map_mul, matrixSubst_C, ← MvPolynomial.smul_eq_C_mul] at hm
    exact hy k1 φ g0 g0inv h m (MvPolynomial.support_smul hm)

theorem laurent_coefficients_mem_property (y : MvPolynomial (ι × Fin n) R) (K : Finset ℤ) (yk : ℤ → MvPolynomial (ι × Fin n) R)
    (hh : ∀ (k1 : Type) [CommRing k1] (φ : R →+* k1), ∃ h h' : Matrix (Fin n) (Fin n) (LaurentPolynomial k1),
      h' * h = 1 ∧ matrixSubst LL S (LaurentPolynomial.C.comp φ) h h' y =
        ∑ k ∈ K, C (LaurentPolynomial.T k) * MvPolynomial.map (LaurentPolynomial.C.comp φ) (yk k))
    (hy : y ∈ weightEntryPropertySubmodule LL S j Pr) : ∀ k ∈ K, yk k ∈ weightEntryPropertySubmodule LL S j Pr := by
  classical
  intro k hk k1 _ φ g0 g0inv hg m hm
  obtain ⟨h, h', hh1, hE⟩ := hh k1 φ
  set ψ : k1 →+* LaurentPolynomial k1 := LaurentPolynomial.C with hψ
  have h2 : g0.map ψ * g0inv.map ψ = 1 := by
    rw [← Matrix.map_mul, hg, Matrix.map_one ψ (map_zero ψ) (map_one ψ)]
  have hinv : (h' * g0.map ψ) * (g0inv.map ψ * h) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (g0.map ψ), h2, Matrix.one_mul, hh1]
  apply hy (LaurentPolynomial k1) (ψ.comp φ) (h' * g0.map ψ) (g0inv.map ψ * h) hinv m
  rw [← matrixSubst_comp, hE, map_sum]
  have hA : ∀ k', matrixSubst LL S (RingHom.id _) (g0inv.map ψ) (g0.map ψ)
      (C (LaurentPolynomial.T k') * MvPolynomial.map (ψ.comp φ) (yk k')) =
      C (LaurentPolynomial.T k') * MvPolynomial.map ψ (matrixSubst LL S φ g0inv g0 (yk k')) := by
    intro k'
    rw [map_mul, matrixSubst_C, RingHom.id_apply, matrixSubst_map, map_matrixSubst]
  simp_rw [hA]
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  intro hz
  apply hm
  rw [MvPolynomial.coeff_sum] at hz
  simp_rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map] at hz
  have hz2 := congrArg (fun p : LaurentPolynomial k1 => p.coeff k) hz
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply] at hz2
  have hT : ∀ k' (c : k1), (LaurentPolynomial.T k' * ψ c).coeff k = if k' = k then c else 0 := by
    intro k' c
    rw [hψ, mul_comm, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp_rw [hT, Finset.sum_ite_eq' K k] at hz2
  simpa [hk] using hz2

end fwd

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section fwd

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι) (j : Fin n)
  (Pr : ℤ → Prop)

theorem propertySubmodule_dividedPower_stable (hT : TransvectionExpansion) (a b : Fin n) (hab : a ≠ b) (k : ℕ) (y : MvPolynomial (ι × Fin n) R)
    (hy : y ∈ weightEntryPropertySubmodule LL S j Pr) : divPow R LL S a b k y ∈ weightEntryPropertySubmodule LL S j Pr := by
  classical
  have key := laurent_coefficients_mem_property (LL := LL) (S := S) (j := j) (Pr := Pr) y
    ((Finset.range (y.totalDegree + k + 1)).image (fun i : ℕ => (i : ℤ)))
    (fun z => divPow R LL S a b z.toNat y) ?_ hy
  · have hk := key (k : ℤ) (Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), rfl⟩)
    simpa using hk
  intro k1 _ φ
  refine ⟨Matrix.transvection a b (LaurentPolynomial.T 1), Matrix.transvection a b (-LaurentPolynomial.T 1),
    ?_, ?_⟩
  · rw [Matrix.transvection_mul_transvection_same (h := hab), neg_add_cancel, Matrix.transvection_zero]
  · rw [hT R (LaurentPolynomial k1) ι LL n S (LaurentPolynomial.C.comp φ) a b hab (LaurentPolynomial.T 1) y
      (y.totalDegree + k + 1) (by omega)]
    rw [Finset.sum_image (fun x _ z _ h => by exact_mod_cast h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [LaurentPolynomial.T_pow]

open Classical in

def weightEntryComponent (a : Fin n) (w : ℤ) (y : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ m ∈ y.support.filter (fun m => wtS LL S m a = w), monomial m (y.coeff m)

private theorem laurent_T_unit_zpow_eq_T {k1 : Type} [CommRing k1] (z : ℤ) :
    (((⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1), by rw [← LaurentPolynomial.T_add]; simp,
      by rw [← LaurentPolynomial.T_add]; simp⟩ : (LaurentPolynomial k1)ˣ) ^ z :
        (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1) = LaurentPolynomial.T z := by
  induction z using Int.induction_on with
  | zero => simp
  | succ i ih => rw [zpow_add_one, Units.val_mul, ih, ← LaurentPolynomial.T_add]
  | pred i ih =>
    rw [zpow_sub_one, Units.val_mul, ih, Units.inv_mk, ← LaurentPolynomial.T_add]
    rfl

theorem propertySubmodule_weightEntryComponent (hTo : TorusActsThroughWeight) (a : Fin n) (w : ℤ) (y : MvPolynomial (ι × Fin n) R)
    (hy : y ∈ weightEntryPropertySubmodule LL S j Pr) : weightEntryComponent LL S a w y ∈ weightEntryPropertySubmodule LL S j Pr := by
  classical
  set K : Finset ℤ := y.support.image (fun m => wtS LL S m a) with hK
  by_cases hw : w ∈ K
  swap
  · have h0 : weightEntryComponent LL S a w y = 0 := by
      unfold weightEntryComponent
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [Finset.mem_filter] at hm
      exact absurd (Finset.mem_image.2 ⟨m, hm.1, hm.2⟩) hw
    rw [h0]
    exact Submodule.zero_mem _
  refine laurent_coefficients_mem_property (LL := LL) (S := S) (j := j) (Pr := Pr) y K (fun w => weightEntryComponent LL S a w y) ?_ hy w hw
  intro k1 _ φ
  let u : (LaurentPolynomial k1)ˣ := ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1),
    by rw [← LaurentPolynomial.T_add]; simp, by rw [← LaurentPolynomial.T_add]; simp⟩
  let D : Fin n → (LaurentPolynomial k1)ˣ := fun b => if b = a then u else 1
  refine ⟨Matrix.diagonal fun b => ((D b : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1),
    Matrix.diagonal fun b => (((D b)⁻¹ : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1), ?_, ?_⟩
  · rw [Matrix.diagonal_mul_diagonal]
    simp
  ·
    have hmono : ∀ m : ι × Fin n →₀ ℕ, ∀ c : R,
        matrixSubst LL S (LaurentPolynomial.C.comp φ)
          (Matrix.diagonal fun b => ((D b : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1))
          (Matrix.diagonal fun b => (((D b)⁻¹ : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1))
          (monomial m c) = C (LaurentPolynomial.T (wtS LL S m a)) *
            monomial m (LaurentPolynomial.C (φ c)) := by
      intro m c
      rw [hTo R (LaurentPolynomial k1) ι LL n S (LaurentPolynomial.C.comp φ) D m c, C_mul_monomial]
      congr 1
      have hp : (∏ b, D b ^ (wtS LL S m b) : (LaurentPolynomial k1)ˣ) = u ^ (wtS LL S m a) := by
        rw [Finset.prod_eq_single a (fun b _ hb => by simp [D, hb]) (fun h => absurd (Finset.mem_univ a) h)]
        simp [D]
      rw [hp, laurent_T_unit_zpow_eq_T, mul_comm]
      rfl
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff y]
    rw [map_sum]
    simp_rw [hmono]
    unfold weightEntryComponent
    simp_rw [map_sum, MvPolynomial.map_monomial, Finset.mul_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (s := y.support) (t := K) (g := fun m => wtS LL S m a)
      (fun m hm => Finset.mem_image.2 ⟨m, hm, rfl⟩)]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_filter] at hm
    rw [hm.2]
    rfl

theorem propertySubmodule_binomial_stable (hTo : TorusActsThroughWeight) (a : Fin n) (k : ℕ) (y : MvPolynomial (ι × Fin n) R)
    (hy : y ∈ weightEntryPropertySubmodule LL S j Pr) : binomPol R LL S a k y ∈ weightEntryPropertySubmodule LL S j Pr := by
  classical

  have hdec : binomPol R LL S a k y = ∑ w ∈ y.support.image (fun m => wtS LL S m a),
      (((Ring.choose w k : ℤ) : R)) • weightEntryComponent LL S a w y := by
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff y]
    rw [map_sum]
    unfold weightEntryComponent
    simp_rw [Finset.smul_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (s := y.support) (t := y.support.image (fun m => wtS LL S m a))
      (g := fun m => wtS LL S m a) (fun m hm => Finset.mem_image.2 ⟨m, hm, rfl⟩)]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_filter] at hm
    have h1 : monomial m (y.coeff m) = (y.coeff m) • (MvPolynomial.basisMonomials (ι × Fin n) R) m := by
      rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [h1, map_smul, binomPol, Module.Basis.constr_basis, MvPolynomial.coe_basisMonomials,
      MvPolynomial.smul_monomial, MvPolynomial.smul_monomial, MvPolynomial.smul_monomial, hm.2]
    congr 1
    simp only [smul_eq_mul]
    ring
  rw [hdec]
  exact Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (propertySubmodule_weightEntryComponent LL S j Pr hTo a w y hy)

theorem weights_property_of_generic_translate (hT : TransvectionExpansion) (hTo : TorusActsThroughWeight) (hSp : GenericMonomialsSpecialise) (G : MvPolynomial (ι × Fin n) R)
    (hG : ∀ m ∈ (genericTranslate LL S G).support, Pr (wtS LL S m j)) :
    ∀ mu ∈ polWts LL S (polGenSub R LL S G), Pr (mu j) := by
  classical

  have hG0 : G ∈ weightEntryPropertySubmodule LL S j Pr := by
    intro k1 _ φ g0 g0inv h m hm
    exact hG m (hSp R ι LL n S k1 φ g0 g0inv h G hm)

  have hclos : ∀ u ∈ Submonoid.closure (polUZgens R LL S),
      ∀ x ∈ weightEntryPropertySubmodule LL S j Pr, u x ∈ weightEntryPropertySubmodule LL S j Pr := by
    intro u hu
    induction hu using Submonoid.closure_induction with
    | mem u hu =>
      rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
      · exact fun x hx => propertySubmodule_dividedPower_stable LL S j Pr hT a b hab k x hx
      · exact fun x hx => propertySubmodule_binomial_stable LL S j Pr hTo a k x hx
    | one => exact fun x hx => hx
    | mul u v _ _ hu hv => exact fun x hx => hu _ (hv x hx)
  have hsub : polGenSub R LL S G ≤ weightEntryPropertySubmodule LL S j Pr := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨u, hu, rfl⟩
    exact hclos u hu G hG0
  rintro mu ⟨x, hx, hx0, hxw⟩
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hx0
  rw [← MvPolynomial.mem_support_iff] at hm
  have h1 := hsub hx R (RingHom.id R) 1 1 (mul_one 1) m
  rw [matrixSubst_one, MvPolynomial.map_id] at h1
  rw [← hxw m hm]
  exact h1 hm

end fwd

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem coeff_weightComponent {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (nu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    coeff m (weightComponent LL S nu F) = if wtS LL S m = nu then coeff m F else 0 := by
  classical
  unfold weightComponent
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, MvPolynomial.mem_support_iff]
  by_cases h1 : wtS LL S m = nu <;> by_cases h2 : coeff m F = 0 <;> simp [h1, h2]


section bwd

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι)
  {L : Type} [Field L] (φ : R →+* L) (W : Submodule R (MvPolynomial (ι × Fin n) R))

def scalarExtension : Submodule L (MvPolynomial (ι × Fin n) L) :=
  Submodule.span L ((MvPolynomial.map φ) '' (W : Set (MvPolynomial (ι × Fin n) R)))

def SubstitutionPreservesExtension (h h' : Matrix (Fin n) (Fin n) L) : Prop :=
  ∀ x ∈ scalarExtension φ W, matrixSubst LL S (RingHom.id L) h h' x ∈ scalarExtension φ W







theorem scalarExtension_monomial_weights (hGr : BinomialStableContainsComponents) (hW2 : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) :
    ∀ z ∈ scalarExtension φ W, ∀ m ∈ z.support, wtS LL S m ∈ polWts LL S W := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    intro m hm
    have hm' : m ∈ w.support := MvPolynomial.support_map_subset φ w hm
    simp only [polWts, Set.mem_setOf_eq]
    refine ⟨weightComponent LL S (wtS LL S m) w, hGr R ι LL n S W hW2 w hw _, ?_, ?_⟩
    · intro h0
      have e := congrArg (MvPolynomial.coeff m) h0
      rw [coeff_weightComponent, if_pos rfl, MvPolynomial.coeff_zero] at e
      exact (MvPolynomial.mem_support_iff.1 hm') e
    · intro m' hm''
      rw [MvPolynomial.mem_support_iff, coeff_weightComponent] at hm''
      by_contra hne
      exact hm'' (if_neg hne)
  | zero => intro m hm; simp at hm
  | add x y _ _ hx hy =>
    classical
    intro m hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (MvPolynomial.support_smul hm)

end bwd

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem genericMatrixInverse_eq_adjugate (R : Type*) [CommRing R] (n : ℕ) :
    genericMatrixInverse R n = (IsLocalization.Away.invSelf (S := GLCoord R n) (genMat R n).det) •
      ((genMat R n).adjugate.map (algebraMap _ (GLCoord R n))) := by
  ext i j
  simp [genericMatrixInverse, Matrix.smul_apply]

theorem genericMatrixInverse_mul (R : Type*) [CommRing R] (n : ℕ) : genericMatrixInverse R n * genericMatrixRootWeights R n = 1 := by
  rw [genericMatrixInverse_eq_adjugate, genericMatrixRootWeights, Matrix.smul_mul, ← Matrix.map_mul, Matrix.adjugate_mul]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · rw [mul_one, mul_comm]
    exact IsLocalization.Away.mul_invSelf _
  · simp

theorem genericMatrix_mul_inverse (R : Type*) [CommRing R] (n : ℕ) : genericMatrixRootWeights R n * genericMatrixInverse R n = 1 := by
  rw [genericMatrixInverse_eq_adjugate, genericMatrixRootWeights, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_adjugate]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · rw [mul_one, mul_comm]
    exact IsLocalization.Away.mul_invSelf _
  · simp

section asm

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι)

theorem generated_submodule_stable (G : MvPolynomial (ι × Fin n) R) (g : MvPolynomial (ι × Fin n) R →ₗ[R] MvPolynomial (ι × Fin n) R)
    (hg : g ∈ polUZgens R LL S) : ∀ x ∈ polGenSub R LL S G, g x ∈ polGenSub R LL S G := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, rfl⟩ := hy
    exact Submodule.subset_span ⟨g * u, Submonoid.mul_mem _ (Submonoid.subset_closure hg) hu, rfl⟩
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hy

theorem self_mem_generated_submodule (G : MvPolynomial (ι × Fin n) R) : G ∈ polGenSub R LL S G := Submodule.subset_span ⟨1, Submonoid.one_mem _, rfl⟩

theorem generic_translate_weights_mem (hT : TransvectionExpansion) (hTo : TorusActsThroughWeight) (hGr : BinomialStableContainsComponents) (G : MvPolynomial (ι × Fin n) R) :
    ∀ m ∈ (genericTranslate LL S G).support, wtS LL S m ∈ polWts LL S (polGenSub R LL S G) := by
  classical
  set W := polGenSub R LL S G with hWdef
  have hW2 : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W := fun a k x hx =>
    generated_submodule_stable LL S G (binomPol R LL S a k) (Or.inr ⟨a, k, rfl⟩) x hx
  have hWd : ∀ a b k, a ≠ b → ∀ x ∈ W, divPow R LL S a b k x ∈ W := fun a b k hab x hx =>
    generated_submodule_stable LL S G (divPow R LL S a b k) (Or.inl ⟨a, b, k, hab, rfl⟩) x hx
  haveI hdom : IsDomain (GLCoord R n) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors
      (Matrix.det_mvPolynomialX_ne_zero (Fin n) R : (genMat R n).det ≠ 0))
  let K := FractionRing (GLCoord R n)
  let ψ : GLCoord R n →+* K := algebraMap (GLCoord R n) K
  have hψ : Function.Injective ψ := IsFractionRing.injective (GLCoord R n) K
  let φ : R →+* K := ψ.comp (coefficientMap R n)
  have good_of : ∀ h h' : Matrix (Fin n) (Fin n) K,
      (∀ w ∈ W, matrixSubst LL S φ h h' w ∈ scalarExtension φ W) → SubstitutionPreservesExtension LL S φ W h h' := by
    intro h h' hw
    unfold SubstitutionPreservesExtension
    intro x hx
    rw [scalarExtension] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hwW, rfl⟩ := hy
      rw [matrixSubst_map]
      exact hw w hwW
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [MvPolynomial.smul_eq_C_mul, map_mul, matrixSubst_C, RingHom.id_apply, ← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ c hy
  have good_mul : ∀ h1 h1' h2 h2' : Matrix (Fin n) (Fin n) K, SubstitutionPreservesExtension LL S φ W h1 h1' →
      SubstitutionPreservesExtension LL S φ W h2 h2' → SubstitutionPreservesExtension LL S φ W (h1 * h2) (h2' * h1') := by
    intro h1 h1' h2 h2' g1 g2
    unfold SubstitutionPreservesExtension at g1 g2 ⊢
    intro x hx
    rw [← matrixSubst_comp]
    exact g1 _ (g2 x hx)
  have good_tr : ∀ (a b : Fin n), a ≠ b → ∀ t : K,
      SubstitutionPreservesExtension LL S φ W (Matrix.transvection a b t) (Matrix.transvection a b (-t)) := by
    intro a b hab t
    apply good_of
    intro w hw
    rw [hT R K ι LL n S φ a b hab t w (w.totalDegree + 1) (Nat.lt_succ_self _)]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hWd a b k hab w hw, rfl⟩)
  have good_diag : ∀ u : Fin n → Kˣ, SubstitutionPreservesExtension LL S φ W (Matrix.diagonal fun a => ((u a : Kˣ) : K))
      (Matrix.diagonal fun a => (((u a)⁻¹ : Kˣ) : K)) := by
    intro u
    apply good_of
    intro w hw
    rw [MvPolynomial.as_sum w, map_sum]
    have hmono : ∀ m ∈ w.support, matrixSubst LL S φ (Matrix.diagonal fun a => ((u a : Kˣ) : K))
        (Matrix.diagonal fun a => (((u a)⁻¹ : Kˣ) : K)) (MvPolynomial.monomial m (w.coeff m)) =
        (((∏ a, u a ^ (wtS LL S m a) : Kˣ) : K)) • MvPolynomial.map φ (MvPolynomial.monomial m (w.coeff m)) := by
      intro m _
      rw [hTo R K ι LL n S φ u m (w.coeff m), MvPolynomial.map_monomial, MvPolynomial.smul_monomial,
        smul_eq_mul]
      congr 1
      exact mul_comm _ _
    rw [Finset.sum_congr rfl hmono,
      ← Finset.sum_fiberwise_of_maps_to (g := fun m => wtS LL S m) (t := w.support.image (fun m => wtS LL S m))
        (fun m hm => Finset.mem_image_of_mem _ hm)]
    refine Submodule.sum_mem _ fun ν _ => ?_
    convert Submodule.smul_mem _ (((∏ a, u a ^ (ν a) : Kˣ) : K))
      (show MvPolynomial.map φ (weightComponent LL S ν w) ∈ scalarExtension φ W by
        rw [scalarExtension]
        exact Submodule.subset_span ⟨_, hGr R ι LL n S W hW2 w hw ν, rfl⟩) using 1
    unfold weightComponent
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr ?_ fun m hm => ?_
    · ext m
      simp
    · rw [(Finset.mem_filter.mp hm).2]
  have good_list : ∀ l : List (Matrix.TransvectionStruct (Fin n) K),
      SubstitutionPreservesExtension LL S φ W (l.map Matrix.TransvectionStruct.toMatrix).prod
        (l.reverse.map fun t => Matrix.transvection t.i t.j (-t.c)).prod ∧
      (l.map Matrix.TransvectionStruct.toMatrix).prod *
        (l.reverse.map fun t => Matrix.transvection t.i t.j (-t.c)).prod = 1 ∧
      (l.reverse.map fun t => Matrix.transvection t.i t.j (-t.c)).prod *
        (l.map Matrix.TransvectionStruct.toMatrix).prod = 1 := by
    intro l
    induction l with
    | nil =>
      simp only [List.map_nil, List.prod_nil, List.reverse_nil]
      refine ⟨?_, mul_one 1, mul_one 1⟩
      unfold SubstitutionPreservesExtension
      intro x hx
      rw [matrixSubst_one, MvPolynomial.map_id]
      exact hx
    | cons t l ih =>
      obtain ⟨hg, h1, h2⟩ := ih
      have ht1 : t.toMatrix * Matrix.transvection t.i t.j (-t.c) = 1 := by
        exact t.mul_inv
      have ht2 : Matrix.transvection t.i t.j (-t.c) * t.toMatrix = 1 := by
        exact t.inv_mul
      simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append, List.prod_append,
        List.map_nil, List.prod_nil, mul_one]
      generalize (l.map Matrix.TransvectionStruct.toMatrix).prod = P at hg h1 h2 ⊢
      generalize (l.reverse.map fun t => Matrix.transvection t.i t.j (-t.c)).prod = P' at hg h1 h2 ⊢
      refine ⟨good_mul _ _ _ _ (good_tr t.i t.j t.hij t.c) hg, ?_, ?_⟩
      · rw [mul_assoc, ← mul_assoc P, h1, one_mul, ht1]
      · rw [mul_assoc, ← mul_assoc (Matrix.transvection t.i t.j (-t.c)), ht2, one_mul, h2]
  set A : Matrix (Fin n) (Fin n) K := (genericMatrixInverse R n).map ψ with hAdef
  set A' : Matrix (Fin n) (Fin n) K := (genericMatrixRootWeights R n).map ψ with hA'def
  have hAA' : A * A' = 1 := by
    rw [hAdef, hA'def, ← Matrix.map_mul, genericMatrixInverse_mul, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  have hA'A : A' * A = 1 := by
    rw [hAdef, hA'def, ← Matrix.map_mul, genericMatrix_mul_inverse, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  obtain ⟨l1, l2, D, hAdec⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec A
  obtain ⟨g1, e1, f1⟩ := good_list l1
  obtain ⟨g2, e2, f2⟩ := good_list l2
  generalize (l1.map Matrix.TransvectionStruct.toMatrix).prod = P1 at hAdec g1 e1 f1
  generalize (l1.reverse.map fun t => Matrix.transvection t.i t.j (-t.c)).prod = P1' at g1 e1 f1
  generalize (l2.map Matrix.TransvectionStruct.toMatrix).prod = P2 at hAdec g2 e2 f2
  generalize (l2.reverse.map fun t => Matrix.transvection t.i t.j (-t.c)).prod = P2' at g2 e2 f2
  have hdiag : Matrix.diagonal D = P1' * A * P2' := by
    rw [hAdec, ← mul_assoc, ← mul_assoc, f1, one_mul, mul_assoc, e2, mul_one]
  have hDinv : Matrix.diagonal D * (P2 * A' * P1) = 1 := by
    rw [hdiag]
    simp only [mul_assoc]
    rw [← mul_assoc P2' P2, f2, one_mul, ← mul_assoc A A', hAA', one_mul, f1]
  have hD0 : ∀ a, D a ≠ 0 := by
    intro a h0
    have h3 := congrFun (congrFun hDinv a) a
    rw [Matrix.diagonal_mul, h0, zero_mul, Matrix.one_apply_eq] at h3
    exact zero_ne_one h3
  let u : Fin n → Kˣ := fun a => Units.mk0 (D a) (hD0 a)
  have gd := good_diag u
  have hu1 : (Matrix.diagonal fun a => ((u a : Kˣ) : K)) = Matrix.diagonal D := by
    ext i j
    simp [u, Matrix.diagonal_apply]
  have hu2 : (Matrix.diagonal fun a => (((u a)⁻¹ : Kˣ) : K)) = Matrix.diagonal fun a => (D a)⁻¹ := by
    ext i j
    simp [u, Matrix.diagonal_apply]
  rw [hu1, hu2] at gd
  have gA := good_mul _ _ _ _ (good_mul _ _ _ _ g1 gd) g2
  have hX : P2' * ((Matrix.diagonal fun a => (D a)⁻¹) * P1') = A' := by
    have hdd : Matrix.diagonal D * Matrix.diagonal (fun a => (D a)⁻¹) = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      exact mul_inv_cancel₀ (hD0 a)
    have hAX : A * (P2' * ((Matrix.diagonal fun a => (D a)⁻¹) * P1')) = 1 := by
      rw [hAdec]
      simp only [mul_assoc]
      rw [← mul_assoc P2 P2', e2, one_mul, ← mul_assoc (Matrix.diagonal D), hdd, one_mul, e1]
    calc P2' * ((Matrix.diagonal fun a => (D a)⁻¹) * P1')
        = (A' * A) * (P2' * ((Matrix.diagonal fun a => (D a)⁻¹) * P1')) := by rw [hA'A, one_mul]
      _ = A' := by rw [mul_assoc, hAX, mul_one]
  rw [← hAdec, hX] at gA
  have hGW : MvPolynomial.map φ G ∈ scalarExtension φ W := Submodule.subset_span ⟨G, self_mem_generated_submodule LL S G, rfl⟩
  have hHK : MvPolynomial.map ψ (genericTranslate LL S G) ∈ scalarExtension φ W := by
    rw [genericTranslate, map_matrixSubst, ← hAdef, ← hA'def, ← matrixSubst_map]
    exact gA _ hGW
  intro m hm
  have hsupp : m ∈ (MvPolynomial.map ψ (genericTranslate LL S G)).support := by
    rwa [MvPolynomial.support_map_of_injective _ hψ]
  exact scalarExtension_monomial_weights (LL := LL) (S := S) (φ := φ) (W := W) hGr hW2 _ hHK m hsupp

end asm

theorem generated_module_weight_lemma_of_interfaces (hT : TransvectionExpansion) (hTo : TorusActsThroughWeight) (hGr : BinomialStableContainsComponents) (hSt : TwistExponentsAreWeightEntries) (hSp : GenericMonomialsSpecialise) :
    GeneratedModuleWeightDescription := by
  intro R _ ι _ LL n _ S
  refine ⟨fun G θ => ?_, fun G M => ?_⟩
  · rw [valS, hSt R ι LL n S (lastIdx n) G, Finset.le_inf_iff]
    constructor
    · intro h
      exact weights_property_of_generic_translate (LL := LL) (S := S) (j := lastIdx n) (Pr := fun z => θ ≤ z) hT hTo hSp G
        (fun m hm => by
          have := h _ (Finset.mem_image_of_mem _ hm)
          simpa using this)
    · intro h k hk
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
      have := h _ (generic_translate_weights_mem LL S hT hTo hGr G m hm)
      simpa using this
  · rw [lam1S, hSt R ι LL n S 0 G, Finset.sup_le_iff]
    constructor
    · intro h
      exact weights_property_of_generic_translate (LL := LL) (S := S) (j := 0) (Pr := fun z => z ≤ M) hT hTo hSp G
        (fun m hm => by
          have := h _ (Finset.mem_image_of_mem _ hm)
          simpa using this)
    · intro h k hk
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
      have := h _ (generic_translate_weights_mem LL S hT hTo hGr G m hm)
      simpa using this

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem zpow_finset_sum_root_weights {G α : Type*} [CommGroup G] (u : G) (s : Finset α) (f : α → ℤ) :
    u ^ (∑ i ∈ s, f i) = ∏ i ∈ s, u ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

theorem torus_acts_through_weight : TorusActsThroughWeight := by
  intro R B _ _ ι _ LL n S φ D m c
  classical
  have hu : (∏ v : ι × Fin n, (if v.1 ∈ S then (if LL.vec v.1 then D v.2 else (D v.2)⁻¹) else 1 : Bˣ) ^ (m v)) = ∏ a, D a ^ (wtS LL S m a) := by
    simp only [wtS, zpow_finset_sum_root_weights]
    rw [Fintype.prod_prod_type_right]
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun l _ => ?_
    split_ifs <;> simp [zpow_neg, zpow_natCast, inv_pow]
  have hU : (∏ v : ι × Fin n, (((if v.1 ∈ S then (if LL.vec v.1 then D v.2 else (D v.2)⁻¹) else 1 : Bˣ) : Bˣ) : B) ^ (m v)) = ((∏ a, D a ^ (wtS LL S m a) : Bˣ) : B) := by
    rw [← hu, Units.coe_prod]
    simp only [Units.val_pow_eq_pow_val]
  simp only [matrixSubst, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, RingHom.coe_comp,
    Function.comp_apply]
  rw [Finsupp.prod_congr (g2 := fun v e => (MvPolynomial.C (((if v.1 ∈ S then (if LL.vec v.1 then D v.2 else (D v.2)⁻¹) else 1 : Bˣ) : Bˣ) : B) * X v) ^ e) ?_]
  · rw [Finsupp.prod_fintype _ _ (fun _ => by simp),
      Finset.prod_congr rfl (fun v _ => mul_pow _ _ _), Finset.prod_mul_distrib,
      MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => by simp), ← hU]
    simp only [map_mul, map_prod, map_pow]
    ring
  · intro v _
    congr 1
    split_ifs with h1 h2
    · rw [Finset.sum_eq_single v.2 (fun b _ hb => by simp [Matrix.diagonal_apply, hb, Ne.symm hb])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp [Matrix.diagonal_apply]
    · rw [Finset.sum_eq_single v.2 (fun b _ hb => by simp [Matrix.diagonal_apply, hb, Ne.symm hb])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp [Matrix.diagonal_apply]
    · simp

theorem specialise_coefficientMap {R : Type*} [CommRing R] {n : ℕ} {K : Type*} [CommRing K] (φ : R →+* K)
    {g0 g0inv : Matrix (Fin n) (Fin n) K} (h : g0 * g0inv = 1) :
    (mul_sp φ g0 g0inv h).comp (coefficientMap R n) = φ := by
  ext r
  simp only [coefficientMap, RingHom.comp_apply, mul_sp_alg, genericMatrixEvaluation, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_C]

theorem specialise_genericMatrix {R : Type*} [CommRing R] {n : ℕ} {K : Type*} [CommRing K] (φ : R →+* K)
    {g0 g0inv : Matrix (Fin n) (Fin n) K} (h : g0 * g0inv = 1) :
    (genericMatrixRootWeights R n).map (mul_sp φ g0 g0inv h) = g0 := by
  ext i k
  have hg := congrFun (congrFun (generic_matrix_evaluation_eq (j := φ) (g0 := g0)) i) k
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hg
  simp only [genericMatrixRootWeights, Matrix.map_apply, mul_sp_alg]
  exact hg

theorem specialise_genericMatrixInverse {R : Type*} [CommRing R] {n : ℕ} {K : Type*} [CommRing K] (φ : R →+* K)
    {g0 g0inv : Matrix (Fin n) (Fin n) K} (h : g0 * g0inv = 1) :
    (genericMatrixInverse R n).map (mul_sp φ g0 g0inv h) = g0inv := by
  have hadj : g0.adjugate = g0.det • g0inv := by
    calc g0.adjugate = g0.adjugate * (g0 * g0inv) := by rw [h, Matrix.mul_one]
      _ = (g0.adjugate * g0) * g0inv := (Matrix.mul_assoc _ _ _).symm
      _ = g0.det • g0inv := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hu := mul_sp_inv (j := φ) (g0 := g0) (g0inv := g0inv) h
  ext i k
  have hA := congrFun (congrFun (RingHom.map_adjugate (genericMatrixEvaluation φ g0) (genMat R n)) i) k
  rw [generic_matrix_evaluation_eq] at hA
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hA
  simp only [genericMatrixInverse, Matrix.map_apply, map_mul, mul_sp_alg, hA, hadj, Matrix.smul_apply, smul_eq_mul]
  linear_combination (g0inv i k) * hu

theorem generic_monomials_specialise : GenericMonomialsSpecialise := by
  intro R _ ι _ LL n S k1 _ φ g0 g0inv h G
  have hAi : ∀ a b, mul_sp φ g0 g0inv h (genericMatrixInverse R n a b) = g0inv a b := fun a b => by
    have e := congrFun (congrFun (specialise_genericMatrixInverse φ h) a) b
    simpa only [Matrix.map_apply] using e
  have hAg : ∀ a b, mul_sp φ g0 g0inv h (genericMatrixRootWeights R n a b) = g0 a b := fun a b => by
    have e := congrFun (congrFun (specialise_genericMatrix φ h) a) b
    simpa only [Matrix.map_apply] using e
  have hAc : ∀ r, mul_sp φ g0 g0inv h (coefficientMap R n r) = φ r := fun r =>
    RingHom.congr_fun (specialise_coefficientMap φ h) r
  have e : (MvPolynomial.map (mul_sp φ g0 g0inv h)).comp
      (matrixSubst LL S (coefficientMap R n) (genericMatrixInverse R n) (genericMatrixRootWeights R n)) = matrixSubst LL S φ g0inv g0 := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, matrixSubst, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
        MvPolynomial.map_C, hAc]
    · intro w
      simp only [RingHom.comp_apply, matrixSubst, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      split_ifs <;> simp [map_sum, hAi, hAg]
  have key : matrixSubst LL S φ g0inv g0 G = MvPolynomial.map (mul_sp φ g0 g0inv h) (genericTranslate LL S G) := by
    rw [← e]
    rfl
  rw [key]
  exact MvPolynomial.support_map_subset _ _

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section inv

variable {A : Type*} [CommRing A] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)

theorem laurentExpand_C (σ : Type*) (b : LaurentPolynomial A) :
    mul_Phi σ A (C b) = AddMonoidAlgebra.mapRingHom ℤ (C : A →+* MvPolynomial σ A) b := by
  simp [mul_Phi]

theorem laurentExpand_X (σ : Type*) (v : σ) :
    mul_Phi σ A (X v) = LaurentPolynomial.C (X v) := by
  simp [mul_Phi]

theorem mapRingHom_laurent_C {A' : Type*} [CommRing A'] (f : A →+* A') (a : A) :
    AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a) := by
  ext k
  rw [AddMonoidAlgebra.coeff_mapRingHom, LaurentPolynomial.C_apply, LaurentPolynomial.C_apply]
  split_ifs <;> simp

private theorem mapRingHom_laurent_comp {A₁ B₁ D₁ : Type*} [CommRing A₁] [CommRing B₁] [CommRing D₁]
    (f : B₁ →+* D₁) (g : A₁ →+* B₁) (x : LaurentPolynomial A₁) :
    AddMonoidAlgebra.mapRingHom ℤ f (AddMonoidAlgebra.mapRingHom ℤ g x) =
      AddMonoidAlgebra.mapRingHom ℤ (f.comp g) x := by
  ext k
  simp only [AddMonoidAlgebra.coeff_mapRingHom, RingHom.comp_apply]

theorem laurentExpand_substitution (M M' : Matrix (Fin n) (Fin n) A) (Q : MvPolynomial (ι × Fin n) (LaurentPolynomial A)) :
    mul_Phi (ι × Fin n) A (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C) Q) =
      AddMonoidAlgebra.mapRingHom ℤ (matrixSubst LL S (RingHom.id A) M M') (mul_Phi (ι × Fin n) A Q) := by
  have key : (mul_Phi (ι × Fin n) A).comp
      (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C)) =
      (AddMonoidAlgebra.mapRingHom ℤ (matrixSubst LL S (RingHom.id A) M M')).comp (mul_Phi (ι × Fin n) A) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      have hC : (matrixSubst LL S (RingHom.id A) M M').comp (C : A →+* MvPolynomial (ι × Fin n) A) = C :=
        RingHom.ext fun a => by simp only [RingHom.comp_apply, matrixSubst_C, RingHom.id_apply]
      simp only [RingHom.comp_apply, matrixSubst_C, RingHom.id_apply, laurentExpand_C, mapRingHom_laurent_comp, hC]
    · intro v
      simp only [RingHom.comp_apply, matrixSubst_X, laurentExpand_X, mapRingHom_laurent_C]
      split_ifs <;> simp [map_sum, laurentExpand_C, laurentExpand_X, mapRingHom_laurent_C, Matrix.map_apply]
  exact congrArg (fun f => f Q) key

theorem laurent_degrees_substitution_subset (M M' : Matrix (Fin n) (Fin n) A) (Q : MvPolynomial (ι × Fin n) (LaurentPolynomial A)) :
    mul_degs (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C) Q) ⊆
      mul_degs Q := by
  rw [mul_degs_eq (matrixSubst LL S (RingHom.id _) _ _ Q), laurentExpand_substitution]
  have key : (AddMonoidAlgebra.mapRingHom ℤ (matrixSubst LL S (RingHom.id A) M M')).comp (mul_Phi (ι × Fin n) A) =
      eval₂Hom (AddMonoidAlgebra.mapRingHom ℤ ((matrixSubst LL S (RingHom.id A) M M').comp C))
        (fun v => LaurentPolynomial.C (matrixSubst LL S (RingHom.id A) M M' (X v))) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp only [RingHom.comp_apply, laurentExpand_C, mapRingHom_laurent_comp, MvPolynomial.eval₂Hom_C]
    · intro v
      simp only [RingHom.comp_apply, laurentExpand_X, mapRingHom_laurent_C, MvPolynomial.eval₂Hom_X']
  have e := congrArg (fun f => f Q) key
  simp only [RingHom.comp_apply] at e
  rw [e]
  exact mul_Psi_support _ _ Q

theorem laurent_degrees_substitution_eq (M M' : Matrix (Fin n) (Fin n) A) (h : M * M' = 1)
    (Q : MvPolynomial (ι × Fin n) (LaurentPolynomial A)) :
    mul_degs (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C) Q) =
      mul_degs Q := by
  apply Finset.Subset.antisymm (laurent_degrees_substitution_subset LL S M M' Q)
  have h' : M' * M = 1 := by
    first
    | exact Matrix.mul_eq_one_comm.1 h
    | exact mul_eq_one_comm.1 h
    | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) h
    | exact Matrix.nonsing_inv_mul_cancel_of_mul_eq_one h
  have hQ : matrixSubst LL S (RingHom.id _) (M'.map LaurentPolynomial.C) (M.map LaurentPolynomial.C)
      (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C) Q) = Q := by
    rw [matrixSubst_comp, ← Matrix.map_mul, h', Matrix.map_one _ (map_zero _) (map_one _), matrixSubst_one,
      MvPolynomial.map_id]
  conv_lhs => rw [← hQ]
  exact laurent_degrees_substitution_subset LL S M' M _

end inv

private theorem genericMatrixBis_mul_genericMatrixInverse (R : Type) [Field R] (n : ℕ) : genericMatrixRootWeights R n * genericMatrixInverse R n = 1 := by
  have e : genericMatrixInverse R n = IsLocalization.Away.invSelf (S := GLCoord R n) (genMat R n).det •
      (genMat R n).adjugate.map (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)) := by
    ext a b
    simp [genericMatrixInverse, Matrix.smul_apply]
  rw [e, genericMatrixRootWeights, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_adjugate]
  ext a b
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    rw [mul_comm]
    exact IsLocalization.Away.mul_invSelf _
  · simp [Matrix.smul_apply, Matrix.one_apply, hab]

private theorem map_C_genericMatrixBis_and_inverse_eq_gL_gLinv (R : Type) [Field R] (n : ℕ) :
    (genericMatrixRootWeights R n).map LaurentPolynomial.C = gL R n ∧ (genericMatrixInverse R n).map LaurentPolynomial.C = gLinv R n := by
  constructor <;> (ext a b; simp [genericMatrixRootWeights, genericMatrixInverse, gL, gLinv])

private theorem support_laurent_C_mul_T_of_ne_zero {B : Type*} [CommRing B] (h : B) (hh : h ≠ 0) (w : ℤ) :
    (LaurentPolynomial.C h * LaurentPolynomial.T w).coeff.support = {w} := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single]
  exact Finsupp.support_single_ne_zero _ hh

private theorem laurent_C_mul_T_eq_zero_iff {B : Type*} [CommRing B] (h : B) (w : ℤ) :
    LaurentPolynomial.C h * LaurentPolynomial.T w = 0 ↔ h = 0 := by
  constructor
  · intro e
    have := congrArg (fun p : LaurentPolynomial B => p.coeff w) e
    rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single] at this
    simpa using this
  · rintro rfl
    simp

theorem twist_exponents_are_weight_entries : TwistExponentsAreWeightEntries := by
  intro R _ ι _ LL n S j G
  classical
  let u : (GLLaurent R n)ˣ := ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1),
    by rw [← LaurentPolynomial.T_add]; simp, by rw [← LaurentPolynomial.T_add]; simp⟩
  let D : Fin n → (GLLaurent R n)ˣ := fun a => if a = j then u else 1
  have hD : (Matrix.diagonal fun a => ((D a : (GLLaurent R n)ˣ) : GLLaurent R n)) =
      Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T 1 else 1) := by
    congr 1; funext a; by_cases h : a = j <;> simp [D, h, u]
  have hD' : (Matrix.diagonal fun a => (((D a)⁻¹ : (GLLaurent R n)ˣ) : GLLaurent R n)) =
      Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T (-1) else 1) := by
    congr 1; funext a; by_cases h : a = j <;> simp [D, h, u]
  obtain ⟨hgL, hgLinv⟩ := map_C_genericMatrixBis_and_inverse_eq_gL_gLinv R n
  have hcoefL : (LaurentPolynomial.C).comp (coefficientMap R n) = coefL R n := rfl
  have hH : MvPolynomial.map LaurentPolynomial.C (genericTranslate LL S G) =
      matrixSubst LL S (coefL R n) (gLinv R n) (gL R n) G := by
    rw [genericTranslate, map_matrixSubst, hgL, hgLinv, hcoefL]
  have hT : twistSub LL S j G = matrixSubst LL S (RingHom.id _) (gL R n) (gLinv R n)
      (matrixSubst LL S (RingHom.id _) (Matrix.diagonal fun a => ((D a : (GLLaurent R n)ˣ) : GLLaurent R n))
        (Matrix.diagonal fun a => (((D a)⁻¹ : (GLLaurent R n)ˣ) : GLLaurent R n))
        (MvPolynomial.map LaurentPolynomial.C (genericTranslate LL S G))) := by
    rw [hH, hD, hD', matrixSubst_comp, matrixSubst_comp, twistSub_eq_matrixSubst]
    simp only [twistMat, Matrix.mul_assoc]
  have hprod : ∀ w : Fin n → ℤ, (((∏ a, D a ^ w a) : (GLLaurent R n)ˣ) : GLLaurent R n) =
      LaurentPolynomial.T (w j) := by
    intro w
    rw [Finset.prod_eq_single j (fun a _ ha => by simp [D, ha]) (fun h => absurd (Finset.mem_univ j) h)]
    simp only [D, if_pos rfl]
    rcases w j with k | k
    · rw [Int.ofNat_eq_coe, zpow_natCast, Units.val_pow_eq_pow_val]
      simp only [u, LaurentPolynomial.T_pow, mul_one]
    · rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
      simp only [u, Units.inv_mk, LaurentPolynomial.T_pow]
      congr 1
      rw [Int.negSucc_eq]
      push_cast
      ring
  set H := genericTranslate LL S G with hHdef
  set P := matrixSubst LL S (RingHom.id _) (Matrix.diagonal fun a => ((D a : (GLLaurent R n)ˣ) : GLLaurent R n))
        (Matrix.diagonal fun a => (((D a)⁻¹ : (GLLaurent R n)ˣ) : GLLaurent R n))
        (MvPolynomial.map LaurentPolynomial.C H) with hPdef
  have hcoef : ∀ m, P.coeff m = LaurentPolynomial.C (H.coeff m) * LaurentPolynomial.T (wtS LL S m j) := by
    intro m
    rw [hPdef]
    conv_lhs => rw [H.as_sum]
    simp only [map_sum, MvPolynomial.map_monomial,
      torus_acts_through_weight (GLLaurent R n) (GLLaurent R n) ι LL n S (RingHom.id _) D, RingHom.id_apply, hprod,
      MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hm
    · rfl
    · rw [MvPolynomial.notMem_support_iff.mp hm]
      simp
  have hsupp : P.support = H.support := by
    ext m
    rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, hcoef, Ne, laurent_C_mul_T_eq_zero_iff]
  show mul_degs (twistSub LL S j G) = _
  rw [hT, ← hgL, ← hgLinv, laurent_degrees_substitution_eq LL S (genericMatrixRootWeights R n) (genericMatrixInverse R n) (genericMatrixBis_mul_genericMatrixInverse R n)]
  rw [mul_degs, hsupp, ← Finset.biUnion_singleton]
  apply Finset.biUnion_congr rfl
  intro m hm
  rw [hcoef]
  exact support_laurent_C_mul_T_of_ne_zero _ (MvPolynomial.mem_support_iff.mp hm) _

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def binomialFunctions : AddSubgroup (ℤ → ℤ) := AddSubgroup.closure (Set.range fun k : ℕ => fun w : ℤ => Ring.choose w k)

theorem binomialFunctions_shift_mem (s : ℤ) (k : ℕ) : (fun w : ℤ => Ring.choose (w + s) k) ∈ binomialFunctions := by
  have h : (fun w : ℤ => Ring.choose (w + s) k) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, Ring.choose s ij.2 • (fun w : ℤ => Ring.choose w ij.1) := by
    funext w
    rw [Ring.add_choose_eq (h := Commute.all w s), Finset.sum_apply]
    refine Finset.sum_congr rfl fun ij _ => ?_
    simp [mul_comm]
  rw [h]
  exact AddSubgroup.sum_mem _ fun ij _ =>
    AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self ij.1)) _

private theorem ring_choose_eq_zero_of_nonneg_of_lt (x : ℤ) (k : ℕ) (h0 : 0 ≤ x) (hk : x < k) : Ring.choose x k = 0 := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
  simp

private theorem ring_choose_self_of_eq (x : ℤ) (k : ℕ) (h : x = k) : Ring.choose x k = 1 := by
  subst h
  rw [Ring.choose_natCast, Nat.choose_self]
  simp

private theorem ring_choose_neg_one (k : ℕ) : Ring.choose (-1 : ℤ) k = (-1) ^ k := by
  induction k with
  | zero => simp [Ring.choose_zero_right]
  | succ k ih =>
    have h := Ring.choose_succ_succ (-1 : ℤ) k
    rw [neg_add_cancel, Ring.choose_zero_succ, ih] at h
    rw [pow_succ]
    linarith

theorem binomialFunctions_window_indicator (w0 : ℤ) (B : ℕ) : ∃ f ∈ binomialFunctions, ∀ w : ℤ, -(B : ℤ) ≤ w → w ≤ B →
    f w = if w = w0 then 1 else 0 := by
  induction B with
  | zero =>
    refine ⟨(if (0 : ℤ) = w0 then 1 else 0) • (fun w : ℤ => Ring.choose w 0),
      AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self 0)) _, ?_⟩
    intro w h1 h2
    have hw : w = 0 := by omega
    subst hw
    simp [Ring.choose_zero_right]
  | succ B ih =>
    obtain ⟨f, hf, hfw⟩ := ih
    have hg1 : (fun w : ℤ => Ring.choose (w + B) (2 * B + 1)) ∈ binomialFunctions := binomialFunctions_shift_mem _ _
    have hg2 : (fun w : ℤ => Ring.choose (w + ((B : ℤ) + 1)) (2 * B + 2)) ∈ binomialFunctions := binomialFunctions_shift_mem _ _
    set g1 : ℤ → ℤ := fun w : ℤ => Ring.choose (w + B) (2 * B + 1) with hg1d
    set g2 : ℤ → ℤ := fun w : ℤ => Ring.choose (w + ((B : ℤ) + 1)) (2 * B + 2) with hg2d
    set c1 : ℤ := (if (B : ℤ) + 1 = w0 then 1 else 0) - f ((B : ℤ) + 1) with hc1
    set c2 : ℤ := (if -((B : ℤ) + 1) = w0 then 1 else 0) - f (-((B : ℤ) + 1)) with hc2
    refine ⟨f + c1 • g2 + c2 • (g2 - g1),
      add_mem (add_mem hf (AddSubgroup.zsmul_mem _ hg2 _)) (AddSubgroup.zsmul_mem _ (sub_mem hg2 hg1) _), ?_⟩
    intro w h1 h2
    push_cast at h1 h2
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rcases (by omega : (-(B : ℤ) ≤ w ∧ w ≤ B) ∨ w = B + 1 ∨ w = -((B : ℤ) + 1)) with h | h | h
    · have e1 : g1 w = 0 := ring_choose_eq_zero_of_nonneg_of_lt _ _ (by omega) (by push_cast; omega)
      have e2 : g2 w = 0 := ring_choose_eq_zero_of_nonneg_of_lt _ _ (by omega) (by push_cast; omega)
      rw [e1, e2, hfw w h.1 h.2]
      ring
    · subst h
      have e1 : g1 ((B : ℤ) + 1) = 1 := ring_choose_self_of_eq _ _ (by push_cast; ring)
      have e2 : g2 ((B : ℤ) + 1) = 1 := ring_choose_self_of_eq _ _ (by push_cast; ring)
      rw [e1, e2, hc1]
      ring
    · subst h
      have e1 : g1 (-((B : ℤ) + 1)) = -1 := by
        simp only [hg1d]
        rw [show -((B : ℤ) + 1) + B = -1 by ring, ring_choose_neg_one, pow_succ, pow_mul]
        simp
      have e2 : g2 (-((B : ℤ) + 1)) = 0 := ring_choose_eq_zero_of_nonneg_of_lt _ _ (by omega) (by push_cast; omega)
      rw [e1, e2, hc2]
      ring

section graded

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)

def diagonalMultiplier (a : Fin n) (f : ℤ → ℤ) (x : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ m ∈ x.support, monomial m (x.coeff m * ((f (wtS LL S m a) : ℤ) : R))

open Classical in

def monomialRestriction (q : (ι × Fin n →₀ ℕ) → Prop) (x : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ m ∈ x.support.filter q, monomial m (x.coeff m)

theorem coeff_diagonalMultiplier (a : Fin n) (f : ℤ → ℤ) (x : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    coeff m (diagonalMultiplier LL S a f x) = x.coeff m * ((f (wtS LL S m a) : ℤ) : R) := by
  classical
  simp only [diagonalMultiplier, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.mem_support_iff, not_not] at h
    rw [h, zero_mul]

open Classical in
theorem coeff_monomialRestriction (q : (ι × Fin n →₀ ℕ) → Prop) (x : MvPolynomial (ι × Fin n) R) (m : ι × Fin n →₀ ℕ) :
    coeff m (monomialRestriction q x) = if q m then x.coeff m else 0 := by
  simp only [monomialRestriction, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, MvPolynomial.mem_support_iff]
  by_cases hq : q m <;> by_cases hm : x.coeff m = 0 <;> simp [hq, hm]

theorem diagonalMultiplier_mem (W : Submodule R (MvPolynomial (ι × Fin n) R))
    (hW : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) (a : Fin n) (f : ℤ → ℤ) (hf : f ∈ binomialFunctions) :
    ∀ x ∈ W, diagonalMultiplier LL S a f x ∈ W := by
  have hb : ∀ (k : ℕ) (x : MvPolynomial (ι × Fin n) R),
      binomPol R LL S a k x = diagonalMultiplier LL S a (fun w => Ring.choose w k) x := by
    intro k x
    conv_lhs => rw [x.as_sum]
    rw [map_sum]
    simp only [binomialOperator_monomial]
    rfl
  induction hf using AddSubgroup.closure_induction with
  | mem f hf =>
    obtain ⟨k, rfl⟩ := hf
    intro x hx
    rw [← hb]
    exact hW a k x hx
  | zero =>
    intro x _
    have e : diagonalMultiplier LL S a 0 x = 0 := by
      ext m
      simp [coeff_diagonalMultiplier]
    rw [e]
    exact W.zero_mem
  | add f g _ _ hf hg =>
    intro x hx
    have e : diagonalMultiplier LL S a (f + g) x = diagonalMultiplier LL S a f x + diagonalMultiplier LL S a g x := by
      ext m
      simp [coeff_diagonalMultiplier, mul_add]
    rw [e]
    exact W.add_mem (hf x hx) (hg x hx)
  | neg f _ hf =>
    intro x hx
    have e : diagonalMultiplier LL S a (-f) x = -diagonalMultiplier LL S a f x := by
      ext m
      simp [coeff_diagonalMultiplier]
    rw [e]
    exact W.neg_mem (hf x hx)

theorem weightEntry_restriction_mem (W : Submodule R (MvPolynomial (ι × Fin n) R))
    (hW : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W) (a : Fin n) (w0 : ℤ) :
    ∀ x ∈ W, monomialRestriction (fun m => wtS LL S m a = w0) x ∈ W := by
  intro x hx
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ m ∈ x.support, -(B : ℤ) ≤ wtS LL S m a ∧ wtS LL S m a ≤ B := by
    refine ⟨∑ m ∈ x.support, (wtS LL S m a).natAbs, fun m hm => ?_⟩
    have h := Finset.single_le_sum (f := fun m => (wtS LL S m a).natAbs) (fun _ _ => Nat.zero_le _) hm
    have h2 : |wtS LL S m a| ≤ ((∑ m ∈ x.support, (wtS LL S m a).natAbs : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h
    exact ⟨by linarith [neg_abs_le (wtS LL S m a)], by linarith [le_abs_self (wtS LL S m a)]⟩
  obtain ⟨f, hf, hfw⟩ := binomialFunctions_window_indicator w0 B
  have e : monomialRestriction (fun m => wtS LL S m a = w0) x = diagonalMultiplier LL S a f x := by
    ext m
    rw [coeff_monomialRestriction, coeff_diagonalMultiplier]
    by_cases hm : m ∈ x.support
    · rw [hfw _ (hB m hm).1 (hB m hm).2]
      split_ifs <;> simp
    · rw [MvPolynomial.mem_support_iff, not_not] at hm
      simp [hm]
  rw [e]
  exact diagonalMultiplier_mem LL S W hW a f hf x hx

end graded

theorem binomial_stable_contains_components : BinomialStableContainsComponents := by
  intro R _ ι _ LL n S W hW x hx nu
  classical
  have key : ∀ s : Finset (Fin n), monomialRestriction (fun m => ∀ a ∈ s, wtS LL S m a = nu a) x ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : monomialRestriction (fun m => ∀ a ∈ (∅ : Finset (Fin n)), wtS LL S m a = nu a) x = x := by
        ext m
        rw [coeff_monomialRestriction]
        simp
      rw [e]
      exact hx
    | @insert a s _ ih =>
      have e : monomialRestriction (fun m => ∀ b ∈ insert a s, wtS LL S m b = nu b) x =
          monomialRestriction (fun m => wtS LL S m a = nu a) (monomialRestriction (fun m => ∀ b ∈ s, wtS LL S m b = nu b) x) := by
        ext m
        rw [coeff_monomialRestriction, coeff_monomialRestriction, coeff_monomialRestriction]
        by_cases h1 : wtS LL S m a = nu a <;> by_cases h2 : ∀ b ∈ s, wtS LL S m b = nu b <;>
          simp [h1, h2, Finset.forall_mem_insert]
      rw [e]
      exact weightEntry_restriction_mem LL S W hW a (nu a) _ ih
  have e : weightComponent LL S nu x = monomialRestriction (fun m => ∀ a ∈ Finset.univ, wtS LL S m a = nu a) x := by
    ext m
    rw [coeff_weightComponent, coeff_monomialRestriction]
    by_cases h : wtS LL S m = nu
    · have h' : ∀ a ∈ (Finset.univ : Finset (Fin n)), wtS LL S m a = nu a := fun a _ => by rw [h]
      rw [if_pos h, if_pos h']
    · have h' : ¬ ∀ a ∈ (Finset.univ : Finset (Fin n)), wtS LL S m a = nu a :=
        fun h'' => h (funext fun a => h'' a (Finset.mem_univ a))
      rw [if_neg h, if_neg h']
  rw [e]
  exact key _

end Formalism.MainNotions.G.GLWeightTheory
end
end
