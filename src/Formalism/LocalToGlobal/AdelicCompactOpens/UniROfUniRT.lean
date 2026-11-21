import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
import Mathlib

section
namespace Formalism.L2.Props

open Matrix

def GLintCompactOpen : Prop :=
  ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] (O : Subring R),
    IsOpen (O : Set R) → IsCompact (O : Set R) → ∀ n : ℕ,
      IsOpen {g : GL (Fin n) R | (∀ a b, (g : Matrix (Fin n) (Fin n) R) a b ∈ O) ∧
          ∀ a b, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b ∈ O} ∧
      IsCompact {g : GL (Fin n) R | (∀ a b, (g : Matrix (Fin n) (Fin n) R) a b ∈ O) ∧
          ∀ a b, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b ∈ O}

section uni

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {n : ℕ}

def ParaR (r : ℕ) (h : GL (Fin n) K) : Prop :=
  (∀ a b, Valued.v ((h : Matrix (Fin n) (Fin n) K) a b) ≤ 1) ∧
    (∀ a b, Valued.v (((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b) ≤ 1) ∧
    ∀ a b : Fin n, r ≤ a.val → b.val < r → Valued.v ((h : Matrix (Fin n) (Fin n) K) a b) < 1

def UniR (r : ℕ) (h : GL (Fin n) K) : Prop :=
  ParaR r h ∧ ∀ a b : Fin n, a.val < r → b.val < r →
    (b.val < a.val → Valued.v ((h : Matrix (Fin n) (Fin n) K) a b) < 1) ∧
    (a = b → Valued.v ((h : Matrix (Fin n) (Fin n) K) a b - 1) < 1)

def detDDR (r : ℕ) (h : GL (Fin n) K) : K :=
  (Matrix.of fun a b : {x : Fin n // r ≤ x.val} => (h : Matrix (Fin n) (Fin n) K) a.1 b.1).det

def supDiagR (r : ℕ) (h : GL (Fin n) K) : K :=
  ∑ a : Fin n, ∑ b : Fin n, if a.val + 1 = b.val ∧ b.val < r then (h : Matrix (Fin n) (Fin n) K) a b else 0

end uni

def ParaDetUnit : Prop :=
  ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] (n r : ℕ) (h : GL (Fin n) K), ParaR r h → Valued.v (detDDR r h) = 1

def UniCharMul : Prop :=
  ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] (n r : ℕ) (ψ₀ : AddChar K ℂ) (ξ : Kˣ →* ℂˣ),
    (∀ x : K, Valued.v x < 1 → ψ₀ x = 1) → (∀ u : Kˣ, Valued.v ((u : K) - 1) < 1 → ξ u = 1) →
    ∀ (g h : GL (Fin n) K) (ug uh ugh : Kˣ), UniR r g → UniR r h →
      (ug : K) = detDDR r g → (uh : K) = detDDR r h → (ugh : K) = detDDR r (g * h) →
      ψ₀ (supDiagR r (g * h)) * (ξ ugh : ℂ) = (ψ₀ (supDiagR r g) * (ξ ug : ℂ)) * (ψ₀ (supDiagR r h) * (ξ uh : ℂ))

end Formalism.L2.Props
end

section
namespace Formalism.L2.Props

open NumberField IsDedekindDomain Formalism.L2.NG ReciprocityTheory.Aut

section

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation3 "L⁺" => NumberField.maximalRealSubfield L

def CompAtUnique : Prop :=
  ∀ (χ : Host.HChar L) (s : SplitPlace L) (ξ ξ' : (s.v.adicCompletion L⁺)ˣ →* ℂˣ),
    IsCompAt χ s ξ → IsCompAt χ s ξ' → ξ = ξ'

def CompAtExists : Prop :=
  ∀ (χ : Host.HChar L) (s : SplitPlace L), ∃ ξ, IsCompAt χ s ξ

def DualUnique : Prop :=
  ∀ a b b' : AlgWt L n, a.IsDual b → a.IsDual b' → b.Iso b'

def UniCharMulNG : Prop :=
  ∀ (s : SplitPlace L) (r : ℕ) (ψ₀ : AddChar (s.v.adicCompletion L⁺) ℂ) (ξ : (s.v.adicCompletion L⁺)ˣ →* ℂˣ),
    IsPsi0 s ψ₀ → (∀ u : (s.v.adicCompletion L⁺)ˣ, Valued.v ((u : s.v.adicCompletion L⁺) - 1) < 1 → ξ u = 1) →
    ∀ (g h : GL (Fin n) (s.v.adicCompletion L⁺)) (ug uh ugh : (s.v.adicCompletion L⁺)ˣ), UniRT s r g → UniRT s r h →
      (ug : s.v.adicCompletion L⁺) = detDD s r g → (uh : s.v.adicCompletion L⁺) = detDD s r h →
      (ugh : s.v.adicCompletion L⁺) = detDD s r (g * h) →
      ψ₀ (supDiag s r (g * h)) * (ξ ugh : ℂ) = (ψ₀ (supDiag s r g) * (ξ ug : ℂ)) * (ψ₀ (supDiag s r h) * (ξ uh : ℂ))

def DualExists : Prop := ∀ a : AlgWt L n, ∃ b, a.IsDual b

def HWUnique : Prop :=
  ∀ (a : AlgWt L n) (τ : L →+* ℂ) (lam lam' : Fin n → ℤ), a.HWAt τ lam → a.HWAt τ lam' → lam = lam'

def HWExists : Prop := ∀ (a : AlgWt L n) (τ : L →+* ℂ), ∃ lam, a.HWAt τ lam

variable {L n}



end

end Formalism.L2.Props
end
