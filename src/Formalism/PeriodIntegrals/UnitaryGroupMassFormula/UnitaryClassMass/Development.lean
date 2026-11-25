module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Development
public import Formalism.PeriodIntegrals.UJClassMassAlt
public import Formalism.PeriodIntegrals.UJClassMass
public import Formalism.HermitianLattices.StatementMass
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

section
@[expose] public section

open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Abstract

variable {G : Type*} [Group G] (Γ Kf : Subgroup G)
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) (L0 : Submodule (𝓞 K) V)

structure IsDict (Λ : G → Submodule (𝓞 K) V) (ι : Γ → V ≃ₗ[K] V) : Prop where
  mem : ∀ g, Λ g ∈ genus h L0
  isIsom : ∀ γ, ι γ ∈ isom h
  equiv : ∀ g (γ : Γ) (k : Kf), Λ ((γ : G) * g * k) = gmap (ι γ) (Λ g)
  inj : ∀ g g' (u : V ≃ₗ[K] V), u ∈ isom h → gmap u (Λ g') = Λ g →
    ∃ (γ : Γ) (k : Kf), g = (γ : G) * g' * k
  surj : ∀ N ∈ genus h L0, ∃ g, Λ g = N
  card : ∀ g, Nat.card (PI.UJClassMass.stab Γ Kf g) = Nat.card (autL h (Λ g))

variable {Γ Kf h L0}

private lemma gmap_mul_lemma (a b : V ≃ₗ[K] V) (L : Submodule (𝓞 K) V) :
    gmap (a * b) L = gmap a (gmap b L) := by
  first
  | (simp only [Formalism.HermitianLatticesTheory.gmap]; rw [← Submodule.map_comp]; rfl)

private lemma gmap_one_unitary_class_mass (L : Submodule (𝓞 K) V) : gmap (1 : V ≃ₗ[K] V) L = L := by
  first
  | (simp only [Formalism.HermitianLatticesTheory.gmap]; exact Submodule.map_id L)

private lemma gmap_inv_gmap_unitary_class_mass (g : V ≃ₗ[K] V) (L : Submodule (𝓞 K) V) : gmap g⁻¹ (gmap g L) = L := by
  rw [← gmap_mul_lemma, inv_mul_cancel, gmap_one_unitary_class_mass]

private lemma mul_mul_inv_mem_autL_gmap {g a : V ≃ₗ[K] V} {N : Submodule (𝓞 K) V} (hg : g ∈ isom h)
    (ha : a ∈ autL h N) : g * a * g⁻¹ ∈ autL h (gmap g N) := by
  have ⟨ha1, ha2⟩ : a ∈ isom h ∧ gmap a N = N := ha
  show g * a * g⁻¹ ∈ isom h ∧ gmap (g * a * g⁻¹) (gmap g N) = gmap g N
  exact ⟨mul_mem (mul_mem hg ha1) (inv_mem hg), by rw [gmap_mul_lemma, gmap_mul_lemma, gmap_inv_gmap_unitary_class_mass, ha2]⟩

private lemma inv_mul_mul_mem_autL {g b : V ≃ₗ[K] V} {N : Submodule (𝓞 K) V} (hg : g ∈ isom h)
    (hb : b ∈ autL h (gmap g N)) : g⁻¹ * b * g ∈ autL h N := by
  have ⟨hb1, hb2⟩ : b ∈ isom h ∧ gmap b (gmap g N) = gmap g N := hb
  show g⁻¹ * b * g ∈ isom h ∧ gmap (g⁻¹ * b * g) N = N
  exact ⟨mul_mem (mul_mem (inv_mem hg) hb1) hg, by rw [gmap_mul_lemma, gmap_mul_lemma, hb2, gmap_inv_gmap_unitary_class_mass]⟩

private lemma natCard_autL_gmap {g : V ≃ₗ[K] V} (hg : g ∈ isom h) (N : Submodule (𝓞 K) V) :
    Nat.card (autL h (gmap g N)) = Nat.card (autL h N) :=
  Nat.card_congr
    { toFun := fun b => ⟨g⁻¹ * b.1 * g, inv_mul_mul_mem_autL hg b.2⟩
      invFun := fun a => ⟨g * a.1 * g⁻¹, mul_mul_inv_mem_autL_gmap hg a.2⟩
      left_inv := fun b => Subtype.ext (by simp [mul_assoc])
      right_inv := fun a => Subtype.ext (by simp [mul_assoc]) }

private lemma sum_inv_card_autL_eq_of_isClassReps {s t : Finset (Submodule (𝓞 K) V)} (hs : IsClassReps h L0 s)
    (ht : IsClassReps h L0 t) :
    ∑ N ∈ s, ((Nat.card (autL h N) : ℕ) : ℝ)⁻¹ = ∑ N ∈ t, ((Nat.card (autL h N) : ℕ) : ℝ)⁻¹ := by
  classical
  have hs' : (∀ M ∈ s, M ∈ genus h L0) ∧
      ∀ M ∈ genus h L0, ∃! N, N ∈ s ∧ ∃ u ∈ isom h, gmap u N = M := hs
  have ht' : (∀ M ∈ t, M ∈ genus h L0) ∧
      ∀ M ∈ genus h L0, ∃! N, N ∈ t ∧ ∃ u ∈ isom h, gmap u N = M := ht
  have hex : ∀ N ∈ s, ∃ P, P ∈ t ∧ ∃ u ∈ isom h, gmap u P = N :=
    fun N hN => (ht'.2 N (hs'.1 N hN)).exists
  refine Finset.sum_bij (fun N hN => (hex N hN).choose) (fun N hN => (hex N hN).choose_spec.1)
    ?_ ?_ ?_
  · intro N₁ h₁ N₂ h₂ heq
    obtain ⟨u₁, hu₁, e₁⟩ := (hex N₁ h₁).choose_spec.2
    obtain ⟨u₂, hu₂, e₂⟩ := (hex N₂ h₂).choose_spec.2
    rw [heq] at e₁
    have key : gmap (u₂ * u₁⁻¹) N₁ = N₂ := by rw [gmap_mul_lemma, ← e₁, gmap_inv_gmap_unitary_class_mass, e₂]
    exact (hs'.2 N₂ (hs'.1 N₂ h₂)).unique ⟨h₁, _, mul_mem hu₂ (inv_mem hu₁), key⟩
      ⟨h₂, 1, one_mem _, gmap_one_unitary_class_mass N₂⟩
  · intro P hP
    obtain ⟨N, ⟨hN, u, hu, e⟩, -⟩ := hs'.2 P (ht'.1 P hP)
    refine ⟨N, hN, ?_⟩
    obtain ⟨v, hv, e'⟩ := (hex N hN).choose_spec.2
    have key : gmap (u * v) (hex N hN).choose = P := by rw [gmap_mul_lemma, e', e]
    exact (ht'.2 P (ht'.1 P hP)).unique ⟨(hex N hN).choose_spec.1, _, mul_mem hu hv, key⟩
      ⟨hP, 1, one_mem _, gmap_one_unitary_class_mass P⟩
  · intro N hN
    obtain ⟨v, hv, e'⟩ := (hex N hN).choose_spec.2
    have hc := natCard_autL_gmap hv (hex N hN).choose
    rw [e'] at hc
    rw [hc]

theorem mass_eq_of_reps {s : Finset (Submodule (𝓞 K) V)} (hs : IsClassReps h L0 s) :
    mass h L0 = ∑ N ∈ s, ((Nat.card (autL h N) : ℕ) : ℝ)⁻¹ := by
  have hex : ∃ t, IsClassReps h L0 t := ⟨s, hs⟩
  rw [Formalism.HermitianLatticesTheory.mass, dite_eq_left hex]
  exact sum_inv_card_autL_eq_of_isClassReps hex.choose_spec hs

theorem sum_eq_mass {Λ : G → Submodule (𝓞 K) V} {ι : Γ → V ≃ₗ[K] V} (D : IsDict Γ Kf h L0 Λ ι)
    (n : ℕ) (g : Fin n → G)
    (hcov : ∀ x, ∃ i, ∃ γ : Γ, ∃ k : Kf, x = (γ : G) * g i * k)
    (hdisj : ∀ i j (γ γ' : Γ) (k k' : Kf), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j) :
    ∑ i, ((Nat.card (PI.UJClassMass.stab Γ Kf (g i)) : ℝ))⁻¹ = mass h L0 := by
  classical
  have hR : ∀ i j (u : V ≃ₗ[K] V), u ∈ isom h → gmap u (Λ (g j)) = Λ (g i) → i = j := by
    intro i j u hu huj
    obtain ⟨γ, k, hk⟩ := D.inj (g i) (g j) u hu huj
    exact hdisj i j 1 γ 1 k (by simpa using hk)
  have hinj : Function.Injective (fun i => Λ (g i)) := fun i j hij =>
    hR i j 1 (one_mem _) (by rw [gmap_one_unitary_class_mass]; exact hij.symm)
  have hs : IsClassReps h L0 (Finset.univ.image (fun i => Λ (g i))) := by
    show (∀ M ∈ Finset.univ.image (fun i => Λ (g i)), M ∈ genus h L0) ∧
      ∀ M ∈ genus h L0, ∃! N, N ∈ Finset.univ.image (fun i => Λ (g i)) ∧ ∃ u ∈ isom h, gmap u N = M
    refine ⟨?_, ?_⟩
    · intro M hM
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hM
      rw [← hi]
      exact D.mem _
    · intro M hM
      obtain ⟨x, rfl⟩ := D.surj M hM
      obtain ⟨i, γ, k, rfl⟩ := hcov x
      refine ⟨Λ (g i), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), ι γ, D.isIsom γ,
        (D.equiv (g i) γ k).symm⟩, ?_⟩
      rintro N ⟨hN, u, hu, huN⟩
      obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hN
      have hj' : Λ (g j) = N := hj
      subst hj'
      rw [D.equiv] at huN
      have key : gmap ((ι γ)⁻¹ * u) (Λ (g j)) = Λ (g i) := by
        rw [gmap_mul_lemma, huN, gmap_inv_gmap_unitary_class_mass]
      obtain rfl := hR i j _ (mul_mem (inv_mem (D.isIsom γ)) hu) key
      rfl
  rw [mass_eq_of_reps hs, Finset.sum_image (by intro i _ j _ hij; exact hinj hij)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [D.card]

end Abstract

end PI.UnitaryGroupMassFormula.UJClassMass

end
end
end


@[expose] public section

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Concrete

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]

def latSet (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin M) E V)
    (L0 : Submodule (𝓞 E) V) (g : HA (AF F) σ J) : Set V :=
  {v | b.equivFun v ∈ PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ J (crdOf b L0) g}

def ratMat (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (γ : GamG σ J) : GL (Fin M) E :=
  Classical.choose (Subgroup.mem_map.mp
    (Subgroup.mem_subgroupOf.mp (γ.2 : (γ.1 : HR (AF F) σ J) ∈ HFinIn (AF F) σ J)))

def linOf {M : ℕ} (b : Module.Basis (Fin M) E V) (u : GL (Fin M) E) : V ≃ₗ[E] V :=
  LinearEquiv.ofLinear (Matrix.toLin b b (u : Matrix (Fin M) (Fin M) E))
    (Matrix.toLin b b ((u⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E))
    (by rw [← Matrix.toLin_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin_one])

def iotaG (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin M) E V)
    (γ : GamG σ J) : V ≃ₗ[E] V :=
  linOf b (ratMat σ J γ)

end Concrete

theorem coe_gmap {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (u : V ≃ₗ[K] V) (N : Submodule (𝓞 K) V) :
    (gmap u N : Set V) = u '' N := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_coe]
  rfl

def LatStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsFullLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ g : HA (AF F) σ (gramOf h b), ∃ N : Submodule (𝓞 E) V,
      (N : Set V) = latSet σ (gramOf h b) b L0 g ∧ N ∈ genus h L0

def IsomStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsFullLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ γ : GamG σ (gramOf h b), iotaG σ (gramOf h b) b γ ∈ isom h

def EquivStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsFullLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ (g : HA (AF F) σ (gramOf h b)) (γ : GamG σ (gramOf h b)) (k : SFin σ (gramOf h b) (crdOf b L0)),
      latSet σ (gramOf h b) b L0 ((γ : HA (AF F) σ (gramOf h b)) * g * k) = iotaG σ (gramOf h b) b γ '' latSet σ (gramOf h b) b L0 g

def InjStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsFullLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ (g g' : HA (AF F) σ (gramOf h b)) (u : V ≃ₗ[E] V), u ∈ isom h →
      u '' latSet σ (gramOf h b) b L0 g' = latSet σ (gramOf h b) b L0 g →
      ∃ (γ : GamG σ (gramOf h b)) (k : SFin σ (gramOf h b) (crdOf b L0)), g = (γ : HA (AF F) σ (gramOf h b)) * g' * k

def SurjStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsFullLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ N ∈ genus h L0, ∃ g : HA (AF F) σ (gramOf h b), latSet σ (gramOf h b) b L0 g = N

def CardStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsFullLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ g : HA (AF F) σ (gramOf h b),
      Nat.card (stab (GamG σ (gramOf h b)) (SFin σ (gramOf h b) (crdOf b L0)) g) =
        Nat.card {u : V ≃ₗ[E] V // u ∈ isom h ∧ u '' latSet σ (gramOf h b) b L0 g = latSet σ (gramOf h b) b L0 g}

def Dict : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    h.IsSymm → h.Nondegenerate → Submodule.IsFullLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∃ (Λ : HA (AF F) σ (gramOf h b) → Submodule (𝓞 E) V) (ι : GamG σ (gramOf h b) → V ≃ₗ[E] V),
      IsDict (GamG σ (gramOf h b)) (SFin σ (gramOf h b) (crdOf b L0)) h L0 Λ ι

theorem uJClassMass_of_dict (hD : Dict) : PI.UJClassMass2.UJClassMass := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig n g hcov hdisj
  obtain ⟨Λ, ι, D⟩ := hD F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig
  exact sum_eq_mass D n g hcov hdisj

theorem dict_of (s1 : LatStep) (si : IsomStep) (s2 : EquivStep) (s3 : InjStep) (s4 : SurjStep)
    (s5 : CardStep) : Dict := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig
  have S1 := s1 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig
  choose Λ hΛ using S1
  refine ⟨Λ, iotaG σ (gramOf h b) b, ⟨fun g => (hΛ g).2, si F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig,
    ?_, ?_, ?_, ?_⟩⟩
  · intro g γ k
    apply SetLike.coe_injective
    rw [coe_gmap, (hΛ g).1, (hΛ _).1]
    exact s2 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig g γ k
  · intro g g' u hu hgm
    apply s3 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig g g' u hu
    have e := congrArg (fun N : Submodule (𝓞 E) V => (N : Set V)) hgm
    simp only [coe_gmap] at e
    rwa [(hΛ g).1, (hΛ g').1] at e
  · intro N hN
    obtain ⟨g, hg⟩ := s4 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig N hN
    exact ⟨g, SetLike.coe_injective ((hΛ g).1.trans hg)⟩
  · intro g
    rw [s5 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig g]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
    show _ ∧ _ ↔ _ ∧ _
    rw [← (hΛ g).1, ← coe_gmap]
    exact and_congr Iff.rfl ⟨fun e => SetLike.coe_injective e, fun e => by rw [e]⟩

theorem uJClassMass_of (s1 : LatStep) (si : IsomStep) (s2 : EquivStep) (s3 : InjStep)
    (s4 : SurjStep) (s5 : CardStep) : PI.UJClassMass2.UJClassMass := by
  exact uJClassMass_of_dict (dict_of s1 si s2 s3 s4 s5)

end PI.UnitaryGroupMassFormula.UJClassMass

end
