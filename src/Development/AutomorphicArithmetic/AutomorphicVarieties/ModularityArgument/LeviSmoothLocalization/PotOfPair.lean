module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

def PotOfPair : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : W.HidaSetting l L Ω) (n : ℕ) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l)) (a : ℤ) (P : GL (Fin n) (PadicAlgCl l)),
    Af.IsPairing s.c ρ (cycBar L Ω l ^ a) P →
    ∀ (ψ : ∀ v : W.Vl l L, Fin n → ↥(Dec (F := L) (s.A v)) →* (PadicAlgCl l)ˣ) (m : W.Vl l L → Fin n → ℤ),
    (∀ v i j, i < j → m v j + 2 ≤ m v i) → (∀ v : W.Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (ψ v)) →
    (∃ k : ℕ, 0 < k ∧ ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (ψ v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) →
    ∀ w : HeightOneSpectrum (𝓞 L), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → Win.PotUnl ρ w

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
