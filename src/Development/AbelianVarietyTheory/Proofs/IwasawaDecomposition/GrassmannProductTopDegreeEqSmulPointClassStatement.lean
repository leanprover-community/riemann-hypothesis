module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductTopDegreeEqSmulPointClass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical


theorem _root_.GlobalTheory.T.grassmannProduct_topDegree_eq_smul_pointClass : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), IsWeightedHomogeneous Prod.snd Q (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q)) → ∃ c : ℝ, Q - C c * pointPoly H Dw ∈ relIdeal H Dw := by
  first | exact @GlobalTheory.GrassTopDim.top_eq_smul_point | exact GlobalTheory.GrassTopDim.top_eq_smul_point | (intros; apply GlobalTheory.GrassTopDim.top_eq_smul_point <;> assumption)
