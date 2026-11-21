import Mathlib
import Formalism.LocalToGlobal.Columns.GoodXgTie

section
namespace PI.XgNamed

def BrauerSplit : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (K : Type) [Field K] (σ : K →+* ℂ) (z : K),
    IsPrimitiveRoot z (Fintype.card Γ) →
    ∀ (n : ℕ) (ρ : Representation ℂ Γ (Fin n → ℂ)), ρ.IsIrreducible →
      ∃ (m : ℕ) (τ : Representation K Γ (Fin m → K))
        (τb : Representation (AlgebraicClosure K) Γ (Fin m → AlgebraicClosure K)),
        τb.IsIrreducible ∧
        (∀ t, LinearMap.toMatrix' (τb t) = (LinearMap.toMatrix' (τ t)).map (algebraMap K (AlgebraicClosure K))) ∧
        ∀ t, σ (τ.character t) = ρ.character t

def GreenExists : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (teich : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g),
    (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → teich x = teich y → x = y) → Formalism.L2.NT.IsGenSys ζ →
    ∀ d k : ℕ, 0 < d → (Formalism.L2.NT.labCusp ζ d k).natDegree = d →
      ∃ χ : GL (Fin d) (ZMod g) → ℂ, Formalism.L2.NT.IsCuspChar χ ∧ Formalism.L2.NT.GreenAt teich χ k

end PI.XgNamed
end

section
namespace PI

def XgCTieBr : Prop :=
  PI.XgNamed.BrauerSplit →
  ∀ {X : Formalism.L2.Col.Fields} (Pr : Formalism.L2.Col.Primes X) {m : ℕ} (Ch : Formalism.L2.Col.Chars X Pr m) (r : ℕ)
    [∀ i, Fact (Pr.g i).Prime] (σ : X.K →+* ℂ) (teich : ∀ i : Fin 2, Formalism.CyclotomicNorms.Fbar (Pr.g i) →* ℂ)
    (ζ : ∀ i : Fin 2, ℕ → Formalism.CyclotomicNorms.Fbar (Pr.g i)),
    Formalism.L2.Col.XgCTie Pr Ch r σ teich ζ

end PI
end
