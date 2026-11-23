module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.CompF
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsAdjOne
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

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {s : X ⟶ Sp R}

theorem exists_adj (S : Thick (dp0 R) s) (hS : InN κ S) (d n : ℕ) (hn : 1 ≤ n) :
    ∃ (P : Thick (dp0 R) s) (i : S ⟶ P) (y : Fin d → P.B), InN κ P ∧ IsLev P.δ n ∧ (∀ k, y k ∈ P.J) ∧
      ∀ (V : Thick (dp0 R) s), IsLev V.δ n → ∀ (φ : S ⟶ V) (z : Fin d → V.B), (∀ k, z k ∈ V.J) →
        ∃! ψ : P ⟶ V, i ≫ ψ = φ ∧ ∀ k, ψ.φ (y k) = z k :=
  exists_adj' S hS d n hn

end FubiniStudyChowHeightFormula₂.Adr
