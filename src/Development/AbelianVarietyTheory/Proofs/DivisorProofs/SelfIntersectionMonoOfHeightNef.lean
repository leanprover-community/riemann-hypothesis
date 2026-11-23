module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtLinearMapEvalAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArithIntersectionNonnegOfSmallSectionDiffStatement
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

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem selfInter_mono : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (α β : ℝ), Le B A → (∀ x y : ℕ, HtNef ((A.pow x).tens (B.pow y)) D) → A.IsSelfInter α → B.IsSelfInter β → β ≤ α := by
  intro hC k _ Y _ p D hX A B α β hle hnef hα hβ
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k Y p D hX).2 (Fin 2) ![A, B]).1
  have hpos := GlobalTheory.T.mixedArithIntersection_nonneg_of_small_section_diff hC k Y p D hX A B Φ hΦ hle
  have hmono := GlobalTheory.monotone_form_along_segment D Φ fun x y => hpos x y (hnef x y)
  have hd := ((hC.arIso k Y p D hX).2 (Fin 2) _ Φ hΦ).1
  have h0 : Φ (MvPolynomial.X 0 ^ (D + 1)) = α := HermLB.IsSelfInter.unique hX (hd 0) hα
  have h1 : Φ (MvPolynomial.X 1 ^ (D + 1)) = β := HermLB.IsSelfInter.unique hX (hd 1) hβ
  rw [← h0, ← h1]
  exact hmono

end GlobalTheory.HSNef
