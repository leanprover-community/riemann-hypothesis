module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCombinationSquareZeroLiftsChart
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

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_affineCombination_squareZero_lifts_chart : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V →
    ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (ι : Type) [Fintype ι] (u : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S), u ⁻¹ᵁ V = ⊤ →
    (∀ i, spMap q ≫ w i = spMap q ≫ u) →
    ∃ c : Sp S ⟶ Y, GlobalTheory.SecGlue.IsCombIn V u c w a ∧ spMap q ≫ c = spMap q ≫ u ∧
      ∀ (R' : Type) [CommRing R'] (p : Y ⟶ Sp R'), (∀ i, w i ≫ p = u ≫ p) → c ≫ p = u ≫ p := by
  first | exact @GlobalTheory.SecGlue.CombEx.exists_comb | exact GlobalTheory.SecGlue.CombEx.exists_comb | (intros; apply GlobalTheory.SecGlue.CombEx.exists_comb <;> assumption)
