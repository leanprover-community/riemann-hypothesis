import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MultiplicityDescent.BesselIsometryScalar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.BeIntegrable
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.WeightedL1OfL2
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoWA

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Down

open ReciprocityTheory.ChartRestriction.DS.Mult1 Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def KV {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)) :
    Submodule ℂ H :=
  Submodule.span ℂ {x | ∃ g ∈ UH (Hpk k r), ∃ v, Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ v ∧ x = σ g v}

def muHN {k r : ℕ} (μW μN : Measure (Mt k r)) : Measure (Mt k r) :=
  (μW.prod μN).map (fun p : Mt k r × Mt k r => fun i j => (Matrix.of p.1 * Matrix.of p.2) i j)

def BesselMapEquivariance {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μW μN μG ν : Measure (Mt k r))
    (σ : Mat k r → (H →L[ℂ] H)) : Prop :=
  ∃ l : H → Wp,
    (∀ u ∈ KV σ, ∀ v ∈ KV σ, l (u + v) = l u + l v) ∧ (∀ (a : ℂ), ∀ u ∈ KV σ, l (a • u) = a • l u) ∧
    (∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, ∀ v ∈ KV σ, l (σ (h * m) v) = psi k r z c m • π h (l v)) ∧
    (∀ u ∈ KV σ, ∀ v ∈ KV σ,
      Integrable (fun p : Mt k r × Mt k r =>
        (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) u⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹)
        (μW.prod μN) ∧
      ∫ p : Mt k r × Mt k r,
        (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) u⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹
        ∂(μW.prod μN) = (innerSL ℂ (l v)).smulRight (l u)) ∧
    ∀ u ∈ KV σ, u ≠ 0 → ∀ v ∈ KV σ,
      ENNReal.ofReal (‖l v‖ ^ 2) * Formalism.MainNotions.S.l2SG (k := k) (r := r) ν (fun g => l (σ g u)) =
        ENNReal.ofReal (‖u‖ ^ 2 * ‖l v‖ ^ 2 / Formalism.MainNotions.S.fdegH μG σ u)

def StNormL : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X → aM k r ≤ X.a →
    ∀ l : X.Hs → Wp, IsMultOneMap D X l → ∀ d : ℝ, IsFdegG D X d → ∀ ν : Measure (Mt k r),
      Formalism.MainNotions.S.IsQuotMeas D.μG (muS D) ν → ∀ u ∈ Vfl X, ∀ v ∈ Vfl X,
        ENNReal.ofReal (‖l v‖ ^ 2) * Formalism.MainNotions.S.l2SG (k := k) (r := r) ν (fun g => l (X.σ g u)) =
          ENNReal.ofReal (‖u‖ ^ 2 * ‖l v‖ ^ 2 / d)

def LocalDataToSetting : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μW μN μG ν : Measure (Mt k r)),
    1 ≤ k → c ≠ 0 → inWb k r z → 0 < Tz k r z →
    Formalism.MainNotions.S.IsURepOn (UWset k r z) π → Formalism.MainNotions.S.IsIrredOn (UWset k r z) π →
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW → Formalism.MainNotions.S.IsHaarOn (Nset k r) μN → Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG →
    Formalism.MainNotions.S.IsQuotMeas μG (muHN μW μN) ν →
    ∃ (D : RealPlaceData k r Wp Wp) (t : Mat k r), IsDiag D ∧ D.z = z ∧ D.π = π ∧ D.μG = μG ∧ t ∈ GV k r ∧
      (∀ h ∈ UWset k r z, t * h = h * t) ∧
      (∀ m ∈ Nset k r, t * m * t⁻¹ ∈ Nset k r ∧ t⁻¹ * m * t ∈ Nset k r ∧ psi k r z c (t * m * t⁻¹) = psiD D m) ∧
      MeasurePreserving (fun p : Mt k r × Mt k r =>
        ((p.1, fun i j => (t⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.1)⁻¹) * t) i j) : Mt k r × Mt k r))
        (μW.prod μN) (D.μW.prod D.μN) ∧
      Formalism.MainNotions.S.IsQuotMeas D.μG (muS D) (ν.map fun x : Mt k r => fun i j => (t⁻¹ * Matrix.of x * t) i j)

def LocalSquareIntegrableKFinite : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : Mat k r → (Wp →L[ℂ] Wp)) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (μW μN μG ν : Measure (Mt k r)) (a : ℝ),
    1 ≤ k → c ≠ 0 → inWb k r z → 0 < Tz k r z → 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ a →
    Formalism.MainNotions.S.IsURepOn (UH (Hpk k r)) σ → Formalism.MainNotions.S.IsIrredOn (UH (Hpk k r)) σ →
    Formalism.MainNotions.S.IsURepOn (UWset k r z) π → Formalism.MainNotions.S.IsIrredOn (UWset k r z) π →
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW → Formalism.MainNotions.S.IsHaarOn (Nset k r) μN → Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG →
    Formalism.MainNotions.S.IsQuotMeas μG (muHN μW μN) ν →
    (∀ v w : H, MemLp (fun x : Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ) 2 μG) →
    (∀ v v' : H, Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ v → Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ v' →
      ∃ C : ℝ, ∀ x ∈ UH (Hpk k r), ‖⟪v', σ x v⟫_ℂ‖ ≤ C * gN x ^ (-a)) →
    (∃ w₀ : H, w₀ ≠ 0 ∧ Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ w₀) →
    BesselMapEquivariance z c π μW μN μG ν σ

def AdmissibleAtRealPlace (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (u : D.what₂.Word) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat D.R.k D.R.rS → (H →L[ℂ] H))
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : Mat D.R.k D.R.rS → (Wp →L[ℂ] Wp)) (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (w : H)
    (μW μN μG ν : Measure (Mt D.R.k D.R.rS)),
    Formalism.MainNotions.S.IsRowsDS D τ σ → Formalism.MainNotions.S.IsColsType D u τ z π →
    (∀ a : Fin D.R.rS, z (eI D.R.k D.R.rS a) = 0 ∧ z (esI D.R.k D.R.rS a) = 0) →
    0 < Tz D.R.k D.R.rS z →
    Formalism.MainNotions.S.IsLowUnitH D.R.k D.R.rS (Formalism.MainNotions.S.epsSH D.R) (Formalism.MainNotions.S.lamSH D.R (D.hc τ)) σ w →
    Formalism.MainNotions.S.IsHaarOn (UWset D.R.k D.R.rS z) μW → Formalism.MainNotions.S.IsHaarOn (Nset D.R.k D.R.rS) μN →
    Formalism.MainNotions.S.IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG → Formalism.MainNotions.S.IsQuotMeas μG (muHN μW μN) ν →
    BesselMapEquivariance z ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) π μW μN μG ν σ

def LocalMultiplicityOne : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (Ca : ℝ), Formalism.MainNotions.LocalBesselAndTopKernel.FormalDegreeDecay D Ca → 1 ≤ Ca → 1 ≤ D.R.k → D.R.r = 2 * D.R.rS + D.R.k + 1 →
    (2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) ≠ 0 → AdmissibleAtRealPlace D

end ReciprocityTheory.ChartRestriction.DS.Mult1.Down
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Down

open ReciprocityTheory.ChartRestriction.DS.Mult1 Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv ReciprocityTheory.ChartRestriction.DS.Mult1.Fold
  ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit

variable {k r : ℕ}

def cj (t : Mat k r) (x : Mt k r) : Mt k r := fun i j => (t⁻¹ * Matrix.of x * t) i j

def cjP (x y : Mt k r) : Mt k r := (Matrix.of x * Matrix.of y * (Matrix.of x)⁻¹ : Mat k r)

end ReciprocityTheory.ChartRestriction.DS.Mult1.Down
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Down

open ReciprocityTheory.ChartRestriction.DS.Mult1 Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv ReciprocityTheory.ChartRestriction.DS.Mult1.Fold
  ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit

variable {k r : ℕ}

section twist

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mat k r → (H →L[ℂ] H)} {t : Mat k r}

theorem tw_cancel (ht : t ∈ GV k r) (g : Mat k r) : t * (t⁻¹ * g * t) * t⁻¹ = g := by
  simp only [Matrix.mul_assoc]
  rw [gv_mul_inv ht, Matrix.mul_one, ← Matrix.mul_assoc, gv_mul_inv ht, Matrix.one_mul]

theorem tw_irr (hσ : Formalism.MainNotions.S.IsIrredOn (GV k r) σ) (ht : t ∈ GV k r) :
    Formalism.MainNotions.S.IsIrredOn (GV k r) (fun g => σ (t * g * t⁻¹)) := by
  intro S hS hst
  refine hσ S hS fun g hg v hv => ?_
  have := hst (t⁻¹ * g * t) (gv_mul (gv_mul (gv_inv ht) hg) ht) v hv
  simpa only [tw_cancel ht] using this

end twist

end ReciprocityTheory.ChartRestriction.DS.Mult1.Down
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Down.KF

open ReciprocityTheory.ChartRestriction.DS.Mult1 Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv

section abstract

variable {K : Type} [Group K] [TopologicalSpace K]

def Fin2 (α : C(K, ℂ)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a : ι → K → ℂ) (β : ι → C(K, ℂ)), ∀ k₀ κ, α (k₀ * κ) = ∑ i, a i k₀ * β i κ

def finAlg (K : Type) [Group K] [TopologicalSpace K] : StarSubalgebra ℂ C(K, ℂ) where
  carrier := {α | Fin2 α}
  mul_mem' := by
    rintro α α' ⟨ι, _, a, β, h⟩ ⟨ι', _, a', β', h'⟩
    refine ⟨ι × ι', inferInstance, fun i k => a i.1 k * a' i.2 k, fun i => β i.1 * β' i.2, fun k₀ κ => ?_⟩
    rw [ContinuousMap.mul_apply, h, h', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousMap.mul_apply]; ring
  add_mem' := by
    rintro α α' ⟨ι, _, a, β, h⟩ ⟨ι', _, a', β', h'⟩
    refine ⟨ι ⊕ ι', inferInstance, Sum.elim a a', Sum.elim β β', fun k₀ κ => ?_⟩
    rw [ContinuousMap.add_apply, h, h', Fintype.sum_sum_type]
    rfl
  algebraMap_mem' c := ⟨Unit, inferInstance, fun _ _ => c, fun _ => 1, fun k₀ κ => by simp⟩
  star_mem' := by
    rintro α ⟨ι, _, a, β, h⟩
    refine ⟨ι, inferInstance, fun i k => star (a i k), fun i => star (β i), fun k₀ κ => ?_⟩
    rw [ContinuousMap.star_apply, h, star_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [star_mul', ContinuousMap.star_apply]

theorem exists_pairing [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (hsep : (finAlg K).SeparatesPoints) (g : C(K, ℂ)) (hg : g 1 ≠ 0) :
    ∃ α : C(K, ℂ), Fin2 α ∧ ∫ κ, α κ * g κ ∂μ ≠ 0 := by
  by_contra hn
  push Not at hn
  have hint : ∀ α : C(K, ℂ), Integrable (fun κ => α κ * g κ) μ := fun α =>
    (BoundedContinuousFunction.mkOfCompact (α * g)).integrable μ
  let Λ : C(K, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun α => ∫ κ, α κ * g κ ∂μ
      map_add' := fun a b => by
        rw [← integral_add (hint a) (hint b)]
        simp only [ContinuousMap.add_apply, add_mul]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc] }
  have hΛ : ∀ α, ‖Λ α‖ ≤ (‖g‖ * μ.real Set.univ) * ‖α‖ := fun α => by
    refine (norm_integral_le_of_norm_le_const (C := ‖α‖ * ‖g‖) (Filter.Eventually.of_forall fun κ => ?_)).trans
      (le_of_eq (by ring))
    rw [norm_mul]
    exact mul_le_mul (α.norm_coe_le_norm κ) (g.norm_coe_le_norm κ) (norm_nonneg _) (norm_nonneg _)
  have hcl : IsClosed {α : C(K, ℂ) | Λ.mkContinuous _ hΛ α = 0} := isClosed_eq (Λ.mkContinuous _ hΛ).continuous continuous_const
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints (finAlg K) hsep
  have hmem : star g ∈ closure ((finAlg K : StarSubalgebra ℂ C(K, ℂ)) : Set C(K, ℂ)) := by
    have : star g ∈ (finAlg K).topologicalClosure := by rw [htop]; trivial
    exact this
  have h0 : ∫ κ, (star g) κ * g κ ∂μ = 0 := hcl.closure_subset_iff.2 (fun α hα => hn α hα) hmem
  have e : ∀ κ, (star g) κ * g κ = ((‖g κ‖ ^ 2 : ℝ) : ℂ) := fun κ => by
    rw [ContinuousMap.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [e] at h0
  rw [integral_complex_ofReal] at h0
  have h1 : ∫ κ, ‖g κ‖ ^ 2 ∂μ = 0 := by exact_mod_cast h0
  have hc : Continuous fun κ => ‖g κ‖ ^ 2 := g.continuous.norm.pow 2
  have hi : Integrable (fun κ => ‖g κ‖ ^ 2) μ :=
    (BoundedContinuousFunction.mkOfCompact (⟨_, hc⟩ : C(K, ℝ))).integrable μ
  have h2 := (integral_eq_zero_iff_of_nonneg (fun κ => sq_nonneg _) hi).1 h1
  have h3 := congrFun ((hc.ae_eq_iff_eq μ continuous_const).1 h2) 1
  exact hg (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3))

end abstract

variable {k r : ℕ}

def KK (k r : ℕ) : Set (Mat k r) := GV k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _)




end ReciprocityTheory.ChartRestriction.DS.Mult1.Down.KF
end
end
