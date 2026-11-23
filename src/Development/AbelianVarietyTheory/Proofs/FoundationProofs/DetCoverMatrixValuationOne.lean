module

import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AntitoneZeroOneEqOfSumEq
public import Formalism.SatakeDualWeyl.StatementE
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.UG (GLint)

noncomputable section
namespace GlobalTheory.GLintCover

section
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

theorem v_eq_one_of_mul {x y : v.adicCompletion F} (hx : x ∈ Formalism.UG.Ov F v) (hy : y ∈ Formalism.UG.Ov F v)
    (hxy : x * y = 1) : Valued.v x = 1 := by
  have h1 : Valued.v x * Valued.v y = 1 := by rw [← map_mul, hxy, map_one]
  have hy1 : Valued.v y ≤ 1 := hy
  have hx1 : Valued.v x ≤ 1 := hx
  refine le_antisymm hx1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v x * Valued.v y := h1.symm
    _ ≤ Valued.v x := mul_le_of_le_one_right' hy1

theorem det_v {n : ℕ} {X : GL (Fin n) (v.adicCompletion F)} (hX : X ∈ GLint (Fin n) (Formalism.UG.Ov F v)) :
    Valued.v (X : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = 1 := by
  apply GlobalTheory.valued_det_eq_one_of_glint <;> assumption

variable {n : ℕ} {ϖ : v.adicCompletion F} {a : Fin n → ℤ}

end
end GlobalTheory.GLintCover

noncomputable section
namespace GlobalTheory.GLintCover

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

variable {ϖ : v.adicCompletion F} {a : Fin n → ℤ}

end GlobalTheory.GLintCover

noncomputable section
namespace GlobalTheory.GLintCover

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
variable {ϖ : v.adicCompletion F} {a : Fin n → ℤ}


end GlobalTheory.GLintCover
