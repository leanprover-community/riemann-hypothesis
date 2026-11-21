import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.LevelIdeal

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree

def levIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) : Ideal (𝓞 E) :=
  l.Mb ⊓ Ideal.span {(l.A : 𝓞 E)}

def levOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) {r : ℕ} (X : Data E r) :
    Subgroup (GL (Fin r) E) :=
  levelGrp (ccH E) X.Gm X.Λ (levIdeal l)

def UnfLat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ k, SDTrace (U.X k).ξ0 (U.X k).Gm (U.X k).Λ

def UnfSign : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 0 < r → ∀ k, ∀ τ ∈ (U.X k).Ψ, (τ (U.X k).ξ0).im < 0

def UnfLevelIn : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ k, ∀ γ ∈ levOf l (U.X k), ∀ x ∈ (U.X k).dom,
      ∃ γ' ∈ (U.X k).Γ, ∃ b ∈ Bor (U.X k).Ψ r, lact γ x = rmul (lact γ' x) b

def UnfBlock : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ k, ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom,
      ∃ δ ∈ levOf l (U.X k), ∃ b : Frame (U.X k).Ψ r, lact γ x = rmul (lact δ x) b ∧
        ∀ τ (a a' : Fin r), (a' : ℕ) < (U.X k).p0 → (U.X k).p0 ≤ (a : ℕ) → b τ a a' = 0

def ScalarOfBlock : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Γ₀ : Subgroup (GL (Fin r) E))
    (γ : GL (Fin r) E), 0 < X.p0 → X.p0 < r →
    (∀ x ∈ X.dom, ∃ δ ∈ Γ₀, ∃ b : Frame X.Ψ r, lact γ x = rmul (lact δ x) b ∧
      ∀ τ (a a' : Fin r), (a' : ℕ) < X.p0 → X.p0 ≤ (a : ℕ) → b τ a a' = 0) →
    ∃ s : Eˣ, ∃ δ ∈ Γ₀, (δ : Matrix (Fin r) (Fin r) E) = (s : E) • (γ : Matrix (Fin r) (Fin r) E)

def OrbitsOfIncl : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Γ₀ : Subgroup (GL (Fin r) E)),
    (∀ γ ∈ X.Γ, ∃ s : Eˣ, ∃ δ ∈ Γ₀, (δ : Matrix (Fin r) (Fin r) E) = (s : E) • (γ : Matrix (Fin r) (Fin r) E)) →
    (∀ γ ∈ Γ₀, ∀ x ∈ X.dom, ∃ γ' ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ x = rmul (lact γ' x) b) →
    SameOrbits X X.Γ Γ₀

def EqVolUnf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 3 ≤ r → 0 < Dw.p → 0 < Dw.q →
    ∀ (k k' : U.Comp) (x : Frame (U.X k).Ψ r) (x' : Frame (U.X k').Ψ r) (FF : Set (V (nd (U.X k))))
      (FF' : Set (V (nd (U.X k')))), IsOrth (U.X k) x → IsOrth (U.X k') x' → IsFundSet (U.X k) x FF →
      IsFundSet (U.X k') x' FF' → muF (U.X k) x FF = muF (U.X k') x' FF'

theorem inf_span_ne_bot {R : Type} [CommRing R] [IsDomain R] {I J : Ideal R} {m a : R} (h : I * J = Ideal.span {m})
    (hm : m ≠ 0) (ha : a ≠ 0) : I ⊓ Ideal.span {a} ≠ ⊥ := by
  have h1 : m ∈ I * J := h ▸ Ideal.mem_span_singleton_self m
  have h2 : m * a ∈ I ⊓ Ideal.span {a} :=
    ⟨I.mul_mem_right _ (Ideal.mul_le_inf h1).1, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)⟩
  intro h0
  rw [h0] at h2
  exact mul_ne_zero hm ha h2


end PositivityTheory.EqVol
