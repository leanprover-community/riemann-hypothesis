module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurve
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

theorem _root_.GlobalTheory.T.intersectionNumber_eq_genericRank_mul_projCurve : ∀ (κ : Type) [Field κ] (Z : Scheme.{0}) [IsIntegral Z] [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ (X := Z)) → topologicalKrullDim Z = 1 → ∀ (G : Z.Modules) [GlobalTheory.QCoh.IsFiniteQC G] (N : LB Z), N.IsLB → interNum κ G ![N] = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) ![N] := by
  first | exact @GlobalTheory.VB.interNum_one_eq_genRank_mul | exact GlobalTheory.VB.interNum_one_eq_genRank_mul | (intros; apply GlobalTheory.VB.interNum_one_eq_genRank_mul <;> assumption)
