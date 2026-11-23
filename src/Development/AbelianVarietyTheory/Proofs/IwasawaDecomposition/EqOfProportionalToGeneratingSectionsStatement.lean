module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratesAlong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Proportional
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfProportionalToGeneratingSections
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup

theorem _root_.GlobalTheory.T.eq_of_proportional_to_generating_sections : ∀ (R : Type) [CommRing R] (X W : Scheme.{0}) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (ψ ψ' : W ⟶ PSpace R m), GeneratesAlong ⊤ σ g → ψ ≫ PSpace.str R m = ψ' ≫ PSpace.str R m → Proportional σ g ψ → Proportional σ g ψ' → ψ = ψ' := by
  first | exact @GlobalTheory.ProjBlowup.eq_of_proportional | exact GlobalTheory.ProjBlowup.eq_of_proportional | (intros; apply GlobalTheory.ProjBlowup.eq_of_proportional <;> assumption)
