module

public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalizedLatticeExponentEqRoundedDepthGoodPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.onObj_exponent_eq_rounded_depth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (Dw : ℕ → Datum H) (Xo : ∀ j, Moduli (Dw j) lv) (c : Coeff lv) [StarRing (𝓞 E)] (Dd : DepData E)
  (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ),
  (∀ v j, O.E v j = EAt (Xo := Xo (ι j)) (c := c) (LL := K) Dd v (ι j)) → (∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) →
  (O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) → PiSplit (H := H) Dd → LeafPage O →
  ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J), ¬ (plc v ∈ O.sm ∨ plc v = O.q1 ∨ plc v = O.dd ∨ plc v = O.g1 ∨ plc v = O.g2) →
    O.e0 v j ≤ (Dd.Q.T : ℝ) * ((nuWAt (Xo := Xo (ι j)) Dd (placeBelow (K := c.F) v) (ι j)).toReal / (ramOverZ (placeBelow (K := c.F) v) : ℝ)) + 1 ∧
    (nuWAt (Xo := Xo (ι j)) Dd (placeBelow (K := c.F) v) (ι j) = 0 → O.e0 v j = 0) := by
  first | exact @GlobalTheory.GoodDepth.normalizedLattice_exponent_eq_roundedDepth_goodPlace | exact GlobalTheory.GoodDepth.normalizedLattice_exponent_eq_roundedDepth_goodPlace | (intros; apply GlobalTheory.GoodDepth.normalizedLattice_exponent_eq_roundedDepth_goodPlace <;> assumption)
