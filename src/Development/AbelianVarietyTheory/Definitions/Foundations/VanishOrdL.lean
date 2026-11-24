module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV
open scoped Matrix

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def SrcL (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l) : Prop :=
  (∃ (g : Newform (2 * e + 1)) (χ : G ℚ Ω →* (Qbar l)ˣ) (A : ValuationSubring Ω)
      (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ),
    ¬ l ∣ g.M ∧ ‖ι.symm (g.a l)‖ = 1 ∧ KillsMu l χ ∧
    g.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ)) * (dt W)⁻¹ * χ)) ∧ OverL l A ∧ IsFlagOn W (Dec (F := ℚ) A) κ ∧
    ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      (κ 1 s : Qbar l) * (cycBar ℚ Ω l (s : G ℚ Ω) : Qbar l) ^ (e : ℤ) * ((dt W (s : G ℚ Ω) : Qbar l)⁻¹ * (χ (s : G ℚ Ω) : Qbar l)) = 1) ∧
  ∀ (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ), OverL l A → IsFlagOn W (Dec (F := ℚ) A) κ →
    ∃ s : ↥(Dec (F := ℚ) A), κ 0 s ≠ cycBar ℚ Ω l s

def VanishOrdL : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ), 1 ≤ e →
    ∀ W : R2 Ω l, admitted ι e W → SrcL ι e W → BlochKatoSelmerVanishes l (Loc.colRep W)

end GlobalTheory.Ord2

end
