module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTPresNuOfPolys
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.Mdl

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Z.Kato.Joint

theorem htLaw_congr {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {c : Coef l}
    {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} {j : Ω →+* Qbar l} {m₀ c₀ : ℕ}
    {R R' : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l} (h : HTLawCsOfCoef A c Z j m₀ c₀ R)
    (hR : ∀ m, 1 ≤ m → ∀ ψ z, R m ψ z = R' m ψ z) : HTLawCsOfCoef A c Z j (max m₀ 1) c₀ R' := by
  obtain ⟨ζ, hζ, hm⟩ := h
  refine ⟨ζ, hζ, fun m hm1 => ?_⟩
  obtain ⟨ι, x, P, o, hP, hψ⟩ := hm m (le_trans (le_max_left _ _) hm1)
  refine ⟨ι, x, P, o, hP, fun ψ hprim => ?_⟩
  rw [← hR m (le_trans (le_max_right _ _) hm1)]
  exact hψ ψ hprim

end UpperTheory.V.Z.Kato.Joint

end
