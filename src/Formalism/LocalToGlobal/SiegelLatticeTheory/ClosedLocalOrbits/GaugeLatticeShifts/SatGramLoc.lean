module

public import Formalism.SatakeDualWeyl.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.SatGramLoc

def SplitPrimeLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (p : ℕ), p.Prime →
    {w : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E →
      (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal →
        Nat.card (𝓞 F ⧸ v.asIdeal) = p ∧
          Valued.v ((p : ℕ) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) ∧
      {v : HeightOneSpectrum (𝓞 F) | ((p : ℕ) : 𝓞 F) ∈ v.asIdeal}.ncard = Module.finrank ℚ F

def RedCore : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ x, σ (σ x) = x) → Module.finrank F E = 2 →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : E ⊗[F] v.adicCompletion F),
      e ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring →
      e * e = e → e * Formalism.UG.sigR σ (v.adicCompletion F) e = 0 →
      (∃ c : v.adicCompletion F, Valued.v c < 1 ∧ ∃ t ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E)
          (v.adicCompletionIntegers F).toSubring,
        1 - e - Formalism.UG.sigR σ (v.adicCompletion F) e = ((1 : E) ⊗ₜ[F] c) * t) →
      ∃ r : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F,
        r e = 1 ∧ (∀ a : v.adicCompletion F, r ((1 : E) ⊗ₜ[F] a) = a) ∧
        (∀ x ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring,
          r x ∈ v.adicCompletionIntegers F) ∧
        ∀ x, e * x = x → x = ((1 : E) ⊗ₜ[F] r x) * e

end Formalism.L2.SG.Pf.SatGramLoc
