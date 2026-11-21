import Formalism.LocalToGlobal.GlobalTheory.LinkTiesOm

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory NumberField

def H1 (Λ : AddSubgroup ℂ) (z w : ℂ) : ℂ := z * (starRingEnd ℂ) w / (TaylorLogMetric.area Λ : ℂ)

def al1 (d : ℕ) (Λ : AddSubgroup ℂ) (x : ℂ) : ℂ := (-1 : ℂ) ^ (round (Real.sqrt d / 2 * (H1 Λ x x).re))

def U1 (Λ : AddSubgroup ℂ) (x : ℂ) (G : ℂ → ℂ) : ℂ → ℂ :=
  fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * H1 Λ z x - (Real.pi : ℂ) * H1 Λ x x / 2)

def IsTheta0 (d : ℕ) (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : Prop :=
  Differentiable ℂ G ∧ (∀ x ∈ Λ, ∀ z, al1 d Λ x * U1 Λ x G z = G z) ∧ G 0 = 1

def normSq1 (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : ℝ :=
  let Fd : Set ℂ := Classical.epsilon (fun Fd => MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume)
  ⨍ z in Fd, ‖G z‖ ^ 2 * Real.exp (-Real.pi * (H1 Λ z z).re)

def normConj (D : D7) (δ : ℂ) (e : TaylorLogMetric.FamE D) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : ℝ :=
  TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D D.host.ccK δ) M ρ)
    (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D D.host.ccK δ) M ρ) L L') (TaylorLogMetric.fnConj D M ρ (e N N' L L'))

def ThetaCompatible (D : D7) (δ : ℂ) (e : TaylorLogMetric.FamE D) : Prop :=
  ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (eL : D.what₂.LL ≃+* M),
    (∀ y, ((eL y : M) : ℂ) = D.what₂.embLL y) ∧
    TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D D.host.ccK δ) M ∧
    (∀ s : D.what₂.LL →+* ℂ, ∃ G, IsTheta0 D.host.d (TaylorLogMetric.lamConj M (conjOf eL s) (TaylorLogMetric.lamOf D D.host.ccK δ)) G ∧
      D.gx.thOne s ^ 2 = normSq1 (TaylorLogMetric.lamConj M (conjOf eL s) (TaylorLogMetric.lamOf D D.host.ccK δ)) G) ∧
    ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ (c : (D.mem u).C.cls i) (c' : (D.mem u).C.cls (i + 1)),
      ∃ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E))
        (L' : Submodule (𝓞 D.host.E) (Fin (D.R.N (i + 1)) → D.host.E)),
        TaylorLogMetric.admitted D (D.R.N i) (D.R.N (i + 1)) L L' ∧ TaylorLogMetric.CoefIn D (e (D.R.N i) (D.R.N (i + 1)) L L') M ∧
        ∀ s : D.what₂.LL →+* ℂ,
          (D.fm u).thFree i s c c' ^ 2 = normConj D δ e M (conjOf eL s) (D.R.N i) (D.R.N (i + 1)) L L'

def ThPow (D : D7) (δ : ℂ) (e : TaylorLogMetric.FamE D) : Prop :=
  ∀ (M : IntermediateField ℚ ℂ) [NumberField M], TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D D.host.ccK δ) M →
    ∀ N N' L L', TaylorLogMetric.admitted D N N' L L' → TaylorLogMetric.CoefIn D (e N N' L L') M → ∀ (ρ : M →ₐ[ℚ] ℂ) (G : ℂ → ℂ),
      IsTheta0 D.host.d (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D D.host.ccK δ)) G →
      normConj D δ e M ρ N N' L L' = normSq1 (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D D.host.ccK δ)) G ^ (D.R.f * N * N')




end Formalism.L2.GlobalTheoryTheory

end
