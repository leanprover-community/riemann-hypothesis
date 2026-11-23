module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicQuotientAlongArc
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

theorem _root_.GlobalTheory.T.exists_holomorphic_quotient_along_arc : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} (m : H0 p B O) (W : Y.Opens) (hW : IsAffineOpen W) (i : B.ι), W ≤ B.U i → ∀ (ψ : ℂ → (Γ(Y, W) →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ O) → ∃ (ρ : ℝ) (a b : Γ(Y, W)), 0 < ρ ∧ ρ ≤ r ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → ψ u b ≠ 0 ∧ ∀ (hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ O) (hi : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ B.U i), H0.val (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) i hO hi m * ψ u b = ψ u a := by
  first | exact @GlobalTheory.Vanishing.exists_quot_along_arc | exact GlobalTheory.Vanishing.exists_quot_along_arc | (intros; apply GlobalTheory.Vanishing.exists_quot_along_arc <;> assumption)
