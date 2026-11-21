import Mathlib
import Formalism.LocalToGlobal.Columns.BrzoPairAtZeroRight
import Formalism.LocalToGlobal.Columns.BzdConjTTranspose
import Formalism.LocalToGlobal.Columns.SliceIntegralDeltaNeBot

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.HermitianLattices.TraceIntegrality

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

def extQ (lam : DomWeight n) : ℚ := Formalism.GradedWeylDivisibility.fockQ (extremal ℚ n lam) (extremal ℚ n lam)

def supS : Finset ((Unit × Fin n × Fin n) →₀ ℕ) :=
  Finset.univ.biUnion fun i : VVIdx (oneW lam) => (bVVfun K (oneW lam) i).support

end Std

section Std2

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

def wS (m : (Unit × Fin n × Fin n) →₀ ℕ) : ℝ := (mfact m : ℝ) / (extQ lam : ℝ)

end Std2


section Deg

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

end Deg

def HwNormBound : Prop :=
  ∀ (κ : ℕ) (ν : Fin (κ + 1) → ℕ), Antitone ν →
    Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl (κ + 1)) ν) (Formalism.GradedWeylDivisibility.hw ℚ (le_refl (κ + 1)) ν) ≤
      ((∏ i, (ν i).factorial : ℕ) : ℚ) * ((ν 0 + κ + 1 : ℕ) : ℚ) ^ ((κ + 1) * κ / 2)




end Formalism.L2.Col
