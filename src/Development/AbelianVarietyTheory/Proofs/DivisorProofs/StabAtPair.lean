import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt

section
noncomputable section

namespace GlobalTheory.ThK.LemF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def IsLocPart {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ) : Prop :=
  ei ≠ 0 ∧ (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) ∧
    ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)

def fac (χ : Chr F E) (z : ℝ) (t : (AE F E)ˣ) : ℂ := (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)

def LocOpMul : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ v : Pl F, ∀ x y : UA σ X.J × UA σ W.J,
      x.1 ∈ UAt σ X (evFin F v) → x.2 ∈ UAt σ W (evFin F v) → y.1 ∈ UAt σ X (evFin F v) → y.2 ∈ UAt σ W (evFin F v) →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v), locOp v (om (x * y)) φ = locOp v (om x) (locOp v (om y) φ)

def EvZeroLocLaw : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ ei ev, IsLocPart M M₁ e ei ev → ∀ v : Pl F, ∀ g ∈ UAt σ X (evFin F v), ∀ t h₁ m, IsLevi H' t h₁ m →
      m ∈ UAt σ W (evFin F v) → h₁ ∈ UAt σ W₁ (evFin F v) → ∀ u ∈ unip σ W H', u ∈ UAt σ W (evFin F v) →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        ev v (locOp v (om (g, u * m)) φ) = fac χX ((n : ℝ) / 2) t • locOp v (om₁ (g, h₁)) (ev v φ)

def EvZeroInfLaw : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ ei ev, IsLocPart M M₁ e ei ev → ∀ g ∈ UAt σ X (evI F), ∀ t h₁ m, IsLevi H' t h₁ m →
      m ∈ UAt σ W (evI F) → h₁ ∈ UAt σ W₁ (evI F) → ∀ u ∈ unip σ W H', u ∈ UAt σ W (evI F) →
      ∀ f : SInf F (Fin n × Fin d),
        ei (locOpInf (om (g, u * m)) f) = fac χX ((n : ℝ) / 2) t • locOpInf (om₁ (g, h₁)) (ei f)

def ConeLawB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure →
      (∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ ∈ SB (Fin b × Fin (a + b) → Fv F v)) ∧
      (∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, u)) φ) =
          coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ) ∧
      ∀ t h₁ m, IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) → h₁ ∈ UAt σ G₁.W (evFin F v) →
      ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, m)) φ) =
          fac X.β ((a : ℝ) / 2) t •
            locOp v (om₁' (1, h₁)) (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ)

def ConeLawA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure →
      (∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) φ ∈ SB (Fin b × Fin (b + a') → Fv F v)) ∧
      (∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, u)) φ) =
          coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) φ) ∧
      ∀ t h₁ m, IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) → h₁ ∈ UAt σ G₁.W (evFin F v) →
      ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, m)) φ) =
          fac X.α ((a' : ℝ) / 2) t •
            locOp v (om₁ (1, h₁)) (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) φ)

def ConeInvB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure → ∀ l : ((Fin b × Fin (a + b) → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ g₀ ∈ UAt σ G₁.V' (evFin F v), ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F v), l (locOp v (om₁' (g₀, 1)) ψ) = l ψ) →
      ∀ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        l (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (g, 1)) φ)) =
          l (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ)

def ConeInvA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure → ∀ l : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ g₀ ∈ UAt σ G₁.V (evFin F v), ∀ ψ ∈ SB (Fin b × Fin (b + a') → Fv F v), l (locOp v (om₁ (g₀, 1)) ψ) = l ψ) →
      ∀ g ∈ UAt σ G.V (evFin F v), ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        l (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (g, 1)) φ)) =
          l (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) φ)

def EvInvB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (l : ((Fin b × Fin (a + b) → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      (∀ g₀ ∈ UAt σ G₁.V' (evFin F v), ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F v), l (locOp v (om₁' (g₀, 1)) ψ) = l ψ) →
      (∀ u ∈ unip σ G.V' H, u ∈ UAt σ G.V' (evFin F v) → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        l (ev' v (locOp v (om' (u, 1)) φ)) = l (ev' v φ)) ∧
      ∀ g₀ g, IsLevi H 1 g₀ g → g ∈ UAt σ G.V' (evFin F v) → g₀ ∈ UAt σ G₁.V' (evFin F v) →
        ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), l (ev' v (locOp v (om' (g, 1)) φ)) = l (ev' v φ)

def EvInvA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (l : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      (∀ g₀ ∈ UAt σ G₁.V (evFin F v), ∀ ψ ∈ SB (Fin b × Fin (b + a') → Fv F v), l (locOp v (om₁ (g₀, 1)) ψ) = l ψ) →
      (∀ u ∈ unip σ G.V H, u ∈ UAt σ G.V (evFin F v) → ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        l (ev v (locOp v (om (u, 1)) φ)) = l (ev v φ)) ∧
      ∀ g₀ g, IsLevi H 1 g₀ g → g ∈ UAt σ G.V (evFin F v) → g₀ ∈ UAt σ G₁.V (evFin F v) →
        ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), l (ev v (locOp v (om (g, 1)) φ)) = l (ev v φ)

def InfInvB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ l : SInf F (Fin b × Fin (a + b)) →L[ℂ] ℂ,
      (∀ g₀ ∈ UAt σ G₁.V' (evI F), ∀ f, l (locOpInf (om₁' (g₀, 1)) f) = l f) →
      (∀ u ∈ unip σ G.V' H, u ∈ UAt σ G.V' (evI F) → ∀ f, l (ei' (locOpInf (om' (u, 1)) f)) = l (ei' f)) ∧
      (∀ g₀ g, IsLevi H 1 g₀ g → g ∈ UAt σ G.V' (evI F) → g₀ ∈ UAt σ G₁.V' (evI F) →
        ∀ f, l (ei' (locOpInf (om' (g, 1)) f)) = l (ei' f)) ∧
      ∀ g ∈ UAt σ G.V' (evI F), ∀ f : SInf F (Fin (b + 2) × Fin (a + (b + 2))),
        ∫ k, ∫ y, l (coneInfInt B G.M' om' ei' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOpInf (om' (g, 1)) f)
          k.1 y.1) ∂μ ∂μK =
        ∫ k, ∫ y, l (coneInfInt B G.M' om' ei' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) f k.1 y.1) ∂μ ∂μK

def InfInvA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ l : SInf F (Fin b × Fin (b + a')) →L[ℂ] ℂ,
      (∀ g₀ ∈ UAt σ G₁.V (evI F), ∀ f, l (locOpInf (om₁ (g₀, 1)) f) = l f) →
      (∀ u ∈ unip σ G.V H, u ∈ UAt σ G.V (evI F) → ∀ f, l (ei (locOpInf (om (u, 1)) f)) = l (ei f)) ∧
      (∀ g₀ g, IsLevi H 1 g₀ g → g ∈ UAt σ G.V (evI F) → g₀ ∈ UAt σ G₁.V (evI F) →
        ∀ f, l (ei (locOpInf (om (g, 1)) f)) = l (ei f)) ∧
      ∀ g ∈ UAt σ G.V (evI F), ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
        ∫ k, ∫ y, l (coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) (locOpInf (om (g, 1)) f) k.1 y.1) ∂μ ∂μK =
        ∫ k, ∫ y, l (coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f k.1 y.1) ∂μ ∂μK

def LemFZero : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ ei ev, IsLocPart M M₁ e ei ev → ∀ v : Pl F,
      (∀ u ∈ unip σ W H', u ∈ UAt σ W (evFin F v) → ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        ev v (locOp v (om (1, u * h)) φ) = ev v (locOp v (om (1, h)) φ)) ∧
      (∀ t h₁ m, IsLevi H' t h₁ m → m ∈ UAt σ W (evFin F v) → h₁ ∈ UAt σ W₁ (evFin F v) → ∀ h ∈ UAt σ W (evFin F v),
        ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v (locOp v (om (1, m * h)) φ) =
          fac χX ((n : ℝ) / 2) t • locOp v (om₁ (1, h₁)) (ev v (locOp v (om (1, h)) φ))) ∧
      ∀ (P₁ : Type) [AddCommGroup P₁] [Module ℂ P₁] (p₁ : ((Fin n × Fin d₁ → Fv F v) → ℂ) →ₗ[ℂ] P₁),
        augAt om₁ v ≤ LinearMap.ker p₁ → ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v),
        ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
          p₁ (ev v (locOp v (om (1, h)) (locOp v (om (g, 1)) φ))) = p₁ (ev v (locOp v (om (1, h)) φ))

def LemFConeB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure →
      (∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ h ∈ UAt σ G.W (evFin F v),
        ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, u * h)) φ) =
          coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, h)) φ)) ∧
      (∀ t h₁ m, IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) → h₁ ∈ UAt σ G₁.W (evFin F v) →
        ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, m * h)) φ) =
          fac X.β ((a : ℝ) / 2) t • locOp v (om₁' (1, h₁))
            (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, h)) φ))) ∧
      ∀ (P₁ : Type) [AddCommGroup P₁] [Module ℂ P₁] (p₁ : ((Fin b × Fin (a + b) → Fv F v) → ℂ) →ₗ[ℂ] P₁),
        augAt om₁' v ≤ LinearMap.ker p₁ → ∀ g ∈ UAt σ G.V' (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v),
        ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
          p₁ (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1)
            (locOp v (om' (1, h)) (locOp v (om' (g, 1)) φ))) =
          p₁ (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, h)) φ))

def LemFConeA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure →
      (∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ h ∈ UAt σ G.W (evFin F v),
        ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, u * h)) φ) =
          coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, h)) φ)) ∧
      (∀ t h₁ m, IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) → h₁ ∈ UAt σ G₁.W (evFin F v) →
        ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, m * h)) φ) =
          fac X.α ((a' : ℝ) / 2) t • locOp v (om₁ (1, h₁))
            (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, h)) φ))) ∧
      ∀ (P₁ : Type) [AddCommGroup P₁] [Module ℂ P₁] (p₁ : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] P₁),
        augAt om₁ v ≤ LinearMap.ker p₁ → ∀ g ∈ UAt σ G.V (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v),
        ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
          p₁ (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2)
            (locOp v (om (1, h)) (locOp v (om (g, 1)) φ))) =
          p₁ (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, h)) φ))

end GlobalTheory.ThK.LemF

end
end

section
noncomputable section

namespace GlobalTheory.ThK.LemF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def coneEvFun (B : Base F E) {b a' : ℕ} (G : Geo σ (b + 2) a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (om : Rep σ G.V G.W) (v : Pl F)
    (ev : ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ)
    (l : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (φ : (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ)
    (x : UA σ G.V.J) : ℂ :=
  l (ev (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' 1))) (locOp v (om (x, 1)) φ)))

end GlobalTheory.ThK.LemF
end
end

section
noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {R : Type} [Zero R] {n : ℕ}

variable (σ) in

def stabAt (X : Spc F E n) (ev : AF F → R) (x : Fin n → E) : Subgroup (UAtSub σ X ev) where
  carrier := {g | mat g.1 *ᵥ incV F x = incV F x}
  one_mem' := by
    show mat (1 : UA σ X.J) *ᵥ incV F x = incV F x
    rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec]
  mul_mem' := by
    intro g h hg hh
    show mat (g.1 * h.1) *ᵥ incV F x = incV F x
    rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hh, hg]
  inv_mem' := by
    intro g hg
    show mat g.1⁻¹ *ᵥ incV F x = incV F x
    conv_lhs => rw [← hg]
    rw [Matrix.mulVec_mulVec, ← GlobalTheory.StabHaar.mat_mul, inv_mul_cancel, GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec]

theorem mem_stabAt {X : Spc F E n} {ev : AF F → R} {x : Fin n → E} {g : UAtSub σ X ev} :
    g ∈ stabAt σ X ev x ↔ mat g.1 *ᵥ incV F x = incV F x := Iff.rfl

def kIncl {X : Spc F E n} (K : Subgroup (UA σ X.J)) (ev : AF F → R) : KAt K ev →* UAtSub σ X ev :=
  Subgroup.inclusion inf_le_right

@[simp] theorem kIncl_val {X : Spc F E n} (K : Subgroup (UA σ X.J)) (ev : AF F → R) (k : KAt K ev) :
    (kIncl K ev k).1 = k.1 := rfl

variable (E) in

def absPow (ev : AF F → R) (k : ℕ) : idelesAt E ev →* ℝ≥0 :=
  (powMonoidHom k).comp ((absE F E).comp (idelesAt E ev).subtype)

@[simp] theorem absPow_apply (ev : AF F → R) (k : ℕ) (t : idelesAt E ev) : absPow E ev k t = absE F E t.1 ^ k := rfl

end GlobalTheory.ThK.LemF.QuotInv
end
end

section
noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {R : Type} [Zero R]

def hAd (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (z y : Fin n → AE F E) : AE F E :=
  z ⬝ᵥ (incM F J *ᵥ fun i => cA σ (y i))

theorem cA_cA {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => exact congrArg (a ⊗ₜ[F] ·) (hσ e)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable (F E) in

def vecAt (m : ℕ) (ev : AF F → R) : AddSubgroup (Fin m → AE F E) where
  carrier := {w | At ev w}
  zero_mem' := fun u _ => smul_zero u
  add_mem' := fun {a b} ha hb u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]
  neg_mem' := fun {a} ha u hu => by rw [smul_neg, ha u hu, neg_zero]

def skewAt (σ : E →ₐ[F] E) (ev : AF F → R) : AddSubgroup (AE F E) where
  carrier := {c | At ev c ∧ cA σ c = -c}
  zero_mem' := ⟨fun u _ => smul_zero u, by simp⟩
  add_mem' := fun {a b} ha hb =>
    ⟨fun u hu => by rw [smul_add, ha.1 u hu, hb.1 u hu, add_zero], by rw [map_add, ha.2, hb.2, neg_add]⟩
  neg_mem' := fun {a} ha => ⟨fun u hu => by rw [smul_neg, ha.1 u hu, neg_zero], by rw [map_neg, ha.2]⟩

def vecAtSmul {m : ℕ} {ev : AF F → R} (s : AE F E) : vecAt F E m ev →+ vecAt F E m ev where
  toFun w := ⟨s • w.1, fun u hu => by rw [smul_comm, w.2 u hu, smul_zero]⟩
  map_zero' := Subtype.ext (smul_zero s)
  map_add' a b := Subtype.ext (smul_add s a.1 b.1)

def normSmul {σ : E →ₐ[F] E} {ev : AF F → R} (hσ : ∀ e, σ (σ e) = e) (s : AE F E) : skewAt σ ev →+ skewAt σ ev where
  toFun c := ⟨(s * cA σ s) * c.1, fun u hu => by rw [← mul_smul_comm, c.2.1 u hu, mul_zero], by
    rw [map_mul, map_mul, cA_cA hσ, c.2.2]; ring⟩
  map_zero' := Subtype.ext (mul_zero _)
  map_add' a b := Subtype.ext (mul_add _ a.1 b.1)

variable (σ) in

def stabAtPair {n : ℕ} (X : Spc F E n) (ev : AF F → R) (x y : Fin n → E) : Subgroup (stabAt σ X ev x) where
  carrier := {q | mat q.1.1 *ᵥ incV F y = incV F y}
  one_mem' := by
    show mat (1 : UA σ X.J) *ᵥ incV F y = incV F y
    rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec]
  mul_mem' := by
    intro g h hg hh
    show mat (g.1.1 * h.1.1) *ᵥ incV F y = incV F y
    rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec]
    rw [show mat h.1.1 *ᵥ incV F y = incV F y from hh]
    exact hg
  inv_mem' := by
    intro g hg
    show mat g.1.1⁻¹ *ᵥ incV F y = incV F y
    have hg' : mat g.1.1 *ᵥ incV F y = incV F y := hg
    conv_lhs => rw [← hg']
    rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]

variable (σ) in

def nMat {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (ι : Matrix (Fin n) (Fin m) E)
    (w : Fin m → AE F E) (c : AE F E) : Matrix (Fin n) (Fin n) (AE F E) :=
  1 + Matrix.vecMulVec (incM F ι *ᵥ w + c • incV F x) (incM F J *ᵥ fun i => cA σ (incV F x i)) -
    Matrix.vecMulVec (incV F x) (incM F J *ᵥ fun i => cA σ ((incM F ι *ᵥ w) i))

theorem nMat_mulVec (σ : E →ₐ[F] E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E)
    (ι : Matrix (Fin n) (Fin m) E) (w : Fin m → AE F E) (c : AE F E) (z : Fin n → AE F E) :
    nMat σ J x ι w c *ᵥ z = z + hAd σ J z (incV F x) • (incM F ι *ᵥ w + c • incV F x) -
      hAd σ J z (incM F ι *ᵥ w) • incV F x := by
  have key : ∀ (p r : Fin n → AE F E), Matrix.vecMulVec p r *ᵥ z = (z ⬝ᵥ r) • p := fun p r => by
    funext i
    simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [nMat, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, key, hAd]

end GlobalTheory.ThK.LemF.QuotInv

end
end
