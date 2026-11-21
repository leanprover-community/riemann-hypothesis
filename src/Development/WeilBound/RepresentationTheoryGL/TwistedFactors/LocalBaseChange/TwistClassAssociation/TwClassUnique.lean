import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.LocalUnitNormIndex.LocalUnitNormIndex

section
noncomputable section

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace PositivityTheory.Lbc

def V1 : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μG : Measure G) [μG.IsMulLeftInvariant] [μG.IsOpenPosMeasure] [SFinite μG]
    (H : Subgroup G), IsClosed (H : Set G) →
    ∀ (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] [μH.IsInvInvariant] [SFinite μH]
      (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) →
    ∀ (F : G → ℝ≥0∞), (∀ h ∈ H, ∀ g, F (h * g) = F g) → (∀ g, ∀ j ∈ J, F (g * j) = F g) →
    ∀ R : Set G, (∀ g, ∃ x ∈ R, ∃ h ∈ H, ∃ j ∈ J, g = h * x * j) →
      (∀ x ∈ R, ∀ y ∈ R, (∃ h ∈ H, ∃ j ∈ J, y = h * x * j) → x = y) →
      quotLIntegral μG H μH F = ∑' x : R, F x * μG J / μH {h : H | (x : G)⁻¹ * (h : G) * x ∈ J}

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def fixT (N : ℕ) (θ : MulAut (GL (Fin N) k)) : Subgroup (Tor k N) :=
  (MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id _)).comap (Tor k N).subtype

variable (k) in

def orbSet (N : ℕ) (J : Subgroup (GL (Fin N) k)) (θ : MulAut (GL (Fin N) k)) (t δ : GL (Fin N) k) :
    Set (Tor k N ⧸ (fixT k N θ ⊔ J.subgroupOf (Tor k N))) :=
  {q | ∃ s : Tor k N, (s : Tor k N ⧸ (fixT k N θ ⊔ J.subgroupOf (Tor k N))) = q ∧
    ∃ κ ∈ J ⊓ Tor k N, (s : GL (Fin N) k)⁻¹ * δ * θ s = t * κ}

variable (k) in

def V2 : Prop :=
  ∀ (N : ℕ) (J : Subgroup (GL (Fin N) k)) (θ : MulAut (GL (Fin N) k)) (l : ℕ) (t : GL (Fin N) k),
    admitted k N J θ l → GoodT k N J θ l t →
    ∀ [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)]
      [MeasurableMul₂ (GL (Fin N) k)] [MeasurableInv (GL (Fin N) k)]
      (μG : Measure (GL (Fin N) k)) [μG.IsHaarMeasure] [SFinite μG],
    ∀ δ ∈ Tor k N, IncrV k N (tnorm θ l δ) →
    ∀ (μδ : Measure (twCent θ.toMonoidHom δ)) [μδ.IsHaarMeasure],
      twOrbIntegral θ.toMonoidHom μG δ μδ (Set.indicator (dcos J t) 1) =
        ((orbSet k N J θ t δ).encard : ℝ≥0∞) * μG J / μδ {x | (x : GL (Fin N) k) ∈ J}

variable (k) in

def TwistClassVanishing : Prop :=
  ∀ (N : ℕ) (J : Subgroup (GL (Fin N) k)) (θ : MulAut (GL (Fin N) k)) (l : ℕ) (t : GL (Fin N) k),
    admitted k N J θ l → GoodT k N J θ l t →
    ∀ [MeasurableSpace (GL (Fin N) k)] (μG : Measure (GL (Fin N) k)) (δ : GL (Fin N) k)
      (μδ : Measure (twCent θ.toMonoidHom δ)),
      (¬ ∃ g : GL (Fin N) k, ∃ κ ∈ J ⊓ Tor k N, twConj θ.toMonoidHom g δ = t * κ) →
      twOrbIntegral θ.toMonoidHom μG δ μδ (Set.indicator (dcos J t) 1) = 0

def sigmaAut {F E : Type} [Field F] [Field E] [Algebra F E] (n : ℕ) (σ : E ≃ₐ[F] E) :
    MulAut (GL (Fin n) E) where
  toFun := sigmaGL σ
  invFun := sigmaGL σ.symm
  left_inv g := by ext i j; simp [sigmaGL_val]
  right_inv g := by ext i j; simp [sigmaGL_val]
  map_mul' := map_mul _

def ElemAssoc : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [IsGalois F E]
    (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) (J' : Subgroup (GL (Fin n) E)) (J : Subgroup (GL (Fin n) F))
      (t' : GL (Fin n) E) (t : GL (Fin n) F),
      admitted E n J' (sigmaAut n σ) (Module.finrank F E) → admitted F n J 1 1 →
      GoodT E n J' (sigmaAut n σ) (Module.finrank F E) t' → GoodT F n J 1 1 t →
      incl (E := E) t = normGL σ t' →
      (∀ s ∈ Tor F n, s ∈ J ↔ ∃ s' ∈ J' ⊓ Tor E n, incl (E := E) s = normGL σ s') →
    ∀ [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)]
      [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
      (μE : Measure (GL (Fin n) E)) (μF : Measure (GL (Fin n) F)),
      μE.IsHaarMeasure → μF.IsHaarMeasure →
      (∀ (δ : GL (Fin n) E) (γ : GL (Fin n) F) (h : GL (Fin n) E)
          (μδ : Measure (twCent (sigmaGL σ) δ)) (μγ : Measure (Subgroup.centralizer {γ})),
          IsRegSemisimple γ → normGL σ δ = h * incl γ * h⁻¹ →
          μδ.IsHaarMeasure → μγ.IsHaarMeasure →
          Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ =
            Measure.map (fun s : Subgroup.centralizer {γ} => incl (s : GL (Fin n) F)) μγ →
          orbIntegral μF γ μγ (fun g => μE J' / μF J * Set.indicator (dcos J t) 1 g) =
            twOrbIntegral (sigmaGL σ) μE δ μδ (Set.indicator (dcos J' t') 1)) ∧
      (∀ (γ : GL (Fin n) F) (μγ : Measure (Subgroup.centralizer {γ})),
          IsRegSemisimple γ → (¬ ∃ δ : GL (Fin n) E, IsNormOf σ δ γ) → μγ.IsHaarMeasure →
          orbIntegral μF γ μγ (Set.indicator (dcos J t) 1) = 0)

end PositivityTheory.Lbc

end
end

section
noncomputable section

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace PositivityTheory.Lbc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def TwCentTor : Prop :=
  ∀ (N : ℕ) (J : Subgroup (GL (Fin N) k)) (θ : MulAut (GL (Fin N) k)) (l : ℕ),
    admitted k N J θ l → ∀ δ ∈ Tor k N, IncrV k N (tnorm θ l δ) →
    ∀ g : GL (Fin N) k, g ∈ twCent θ.toMonoidHom δ ↔ (g ∈ Tor k N ∧ θ g = g)

def GLMeas : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)],
    MeasurableMul₂ (GL (Fin n) k) ∧ MeasurableInv (GL (Fin n) k) ∧
      ∀ μ : Measure (GL (Fin n) k), μ.IsHaarMeasure → SFinite μ

def NormTor : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [IsGalois F E]
    (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ n : ℕ, (∀ s : GL (Fin n) E, tnorm (sigmaAut n σ) (Module.finrank F E) s = normGL σ s) ∧
      ∀ s ∈ Tor E n, ∃ s₀ ∈ Tor F n, incl (E := E) s₀ = normGL σ s

def OrbConj : Prop :=
  ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μG : Measure G) [μG.IsMulLeftInvariant] [SFinite μG] (γ g : G)
    (μγ : Measure (Subgroup.centralizer {γ})) (μγ' : Measure (Subgroup.centralizer {g⁻¹ * γ * g}))
    [SFinite μγ] [μγ.IsInvInvariant] [SFinite μγ'] [μγ'.IsInvInvariant] (f : G → ℝ≥0∞), Measurable f →
    Measure.map (fun x : Subgroup.centralizer {γ} => g⁻¹ * (x : G) * g) μγ =
      Measure.map (fun x : Subgroup.centralizer {g⁻¹ * γ * g} => (x : G)) μγ' →
    orbIntegral μG (g⁻¹ * γ * g) μγ' f = orbIntegral μG γ μγ f

def TwOrbConj : Prop :=
  ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (θ : Monoid.End G) (μG : Measure G) [μG.IsMulLeftInvariant] [SFinite μG] (δ g : G)
    (μδ : Measure (twCent θ δ)) (μδ' : Measure (twCent θ (twConj θ g δ)))
    [SFinite μδ] [μδ.IsInvInvariant] [SFinite μδ'] [μδ'.IsInvInvariant] (f : G → ℝ≥0∞), Measurable f →
    Measure.map (fun x : twCent θ δ => g⁻¹ * (x : G) * g) μδ =
      Measure.map (fun x : twCent θ (twConj θ g δ) => (x : G)) μδ' →
    twOrbIntegral θ μG (twConj θ g δ) μδ' f = twOrbIntegral θ μG δ μδ f

def HaarIndex : Prop :=
  ∀ (A : Type) [Group A] [MeasurableSpace A] [MeasurableMul A] (μ : Measure A) [μ.IsMulLeftInvariant]
    (U V : Subgroup A), MeasurableSet (U : Set A) → U ≤ V → U.relIndex V ≠ 0 →
    μ V = (U.relIndex V : ℝ≥0∞) * μ U

def ConjDescent : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (n : ℕ) (γ γ' : GL (Fin n) F),
    IsRegSemisimple γ → (∃ h : GL (Fin n) E, incl (E := E) γ' = h * incl γ * h⁻¹) →
    ∃ g : GL (Fin n) F, γ' = g * γ * g⁻¹

def TwClassUnique : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [IsGalois F E]
    (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) (δ δ₀ : GL (Fin n) E), IsTwRegSemisimple σ δ →
      (∃ h : GL (Fin n) E, normGL σ δ = h * normGL σ δ₀ * h⁻¹) → TwConjugate (sigmaGL σ) δ₀ δ

end PositivityTheory.Lbc

end
end
