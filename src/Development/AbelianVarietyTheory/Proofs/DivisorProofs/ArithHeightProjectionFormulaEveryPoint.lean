module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaInductiveStepStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaPointCurveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightPullbackResidueDegreeStatement
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

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem hasDim_iff_clo {Y : Scheme.{0}} (y : Y) (e : ℕ) : HasDim y e ↔ topologicalKrullDim (clo y) = (e : ℕ) := by
  have hemb := (cloι y).isClosedEmbedding
  have hr : Set.range (cloι y) = closure ({y} : Set Y) := by
    rw [← Set.image_univ, ← (genericPoint_spec (clo y)).def, ← hemb.isClosedMap.closure_image_eq_of_continuous
      hemb.continuous, Set.image_singleton, cloι_genericPoint]
  have h := (hemb.toIsEmbedding.toHomeomorph).isHomeomorph.topologicalKrullDim_eq
  unfold HasDim
  rw [h, hr]

theorem heightProj : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ),
    IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ),
    L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ y : Y, h' y = (π.residueDegree y : ℝ) * h (π y) := by
  intro k _ X Y p q D E hX hY π hπ L h h' H H'
  have key : ∀ (n : ℕ) (w : Y), HasDim w (n + 1) → h' w = (π.residueDegree w : ℝ) * h (π w) := by
    intro n
    induction n with
    | zero =>
      intro w hw
      rcases hY.vertical_or_horizontal (cloι w) with ⟨l, _, hl⟩ | ⟨hc, e, he⟩
      · exact GlobalTheory.T.arith_height_pullback_residue_degree k X Y p q D E hX hY π hπ L h h' H H' w l hl
      · exact GlobalTheory.T.arithHeight_projectionFormula_pointCurve k X Y p q D E hX hY π hπ L h h' H H' w hc hw
    | succ m ih =>
      intro w hw
      rcases hY.vertical_or_horizontal (cloι w) with ⟨l, _, hl⟩ | ⟨hc, e, he⟩
      · exact GlobalTheory.T.arith_height_pullback_residue_degree k X Y p q D E hX hY π hπ L h h' H H' w l hl
      · exact GlobalTheory.T.arithHeight_projectionFormula_inductiveStep k X Y p q D E hX hY π hπ L h h' H H' w m hc hw ih
  intro y
  rcases hY.vertical_or_horizontal (cloι y) with ⟨l, _, hl⟩ | ⟨hc, e, he⟩
  · exact GlobalTheory.T.arith_height_pullback_residue_degree k X Y p q D E hX hY π hπ L h h' H H' y l hl
  · exact key e y ((hasDim_iff_clo y (e + 1)).2 he)

end GlobalTheory.MixHt
