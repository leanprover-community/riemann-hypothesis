module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange

@[expose] public section

noncomputable section

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

def AllClassesSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty),
    l.A = 1 → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty →
    ∀ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La), D'.p = D.p → D'.q = D.q →
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
        (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) →
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a') →
      ∃ (i : Fin U.n) (gam : D'.La ≃ₗ[𝓞 E] (U.Di i).La),
        (∀ a a', (U.Di i).EF (gam a) (gam a') = D'.EF a a') ∧
        ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
          ∃ e, gam (f l.M a) = U.t i a + l.M • e

namespace AllClasses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isTorsionFree (D : Datum H) : Module.IsTorsionFree (𝓞 E) D.La := by
  have := D.proj
  infer_instance

theorem exists_isTypeFn (H : Host E) (p q : ℕ) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H p q ty := by
  classical
  let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then p else q
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))).symm
  have h : ∀ τ, Nat.card {i // (e i).1 = τ} = m τ := fun τ => by
    rw [Nat.card_congr ((e.subtypeEquiv (q := fun x => x.1 = τ) fun _ => Iff.rfl).trans
      (Equiv.sigmaSubtype τ))]
    simp
  exact ⟨_, fun i => (e i).1, fun τ => ⟨fun hτ => by rw [h]; simp [m, hτ], fun hτ => by rw [h]; simp [m, hτ]⟩⟩

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem subsingleton_of_rank_zero (D : Datum H) (hD : D.p + D.q = 0) : Subsingleton D.La := by
  have := D.fin
  have := isTorsionFree D
  exact Module.finrank_zero_iff.mp (D.rank.trans hD)

end AllClasses

end GlobalTheory
