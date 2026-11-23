module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

noncomputable section

namespace GlobalTheory.HeightCounting.LabConjModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open GlobalTheory.WeilDeligne Pointwise

section General

variable {Ω : Type} [Field Ω]

variable {E : Type} [Field E] [NumberField E] [Algebra E Ω]

end General

section Host

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def conjInt (H : Host R) : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

theorem coe_conjInt (x : 𝓞 H.E) : ((conjInt H x : 𝓞 H.E) : H.E) = H.conj (x : H.E) := rfl

theorem isConjPl_iff {w w' : PlE H} : IsConjPl H w w' ↔ ∀ x, x ∈ w.asIdeal ↔ conjInt H x ∈ w'.asIdeal := by
  refine ⟨fun h x => h x _ (coe_conjInt x), fun h x y hy => ?_⟩
  have : y = conjInt H x := RingOfIntegers.ext (hy.trans (coe_conjInt x).symm)
  rw [this]; exact h x

theorem eq_of_isConjPl {w₀ w₁ w : PlE H} (h₀ : IsConjPl H w₀ w) (h₁ : IsConjPl H w₁ w) : w₀ = w₁ := by
  apply HeightOneSpectrum.ext
  ext x
  rw [isConjPl_iff.1 h₀, isConjPl_iff.1 h₁]

end Host


end GlobalTheory.HeightCounting.LabConjModel

end
