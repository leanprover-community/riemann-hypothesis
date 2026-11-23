module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicConstantsDescendToNormalIntegralScheme
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

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.algebraicConstants_descend_to_normalIntegralScheme : ∀ (F : Type) [Field F] (W V : Scheme.{0}) [IsIntegral W] [IsIntegral V] [GlobalTheory.IsNormalScheme W] (pW : W ⟶ Sp F) (pV : V ⟶ Sp F) (π : V ⟶ W), π ≫ pW = pV → (∀ b : V.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn pV) b = 0) → b ∈ (GlobalTheory.Cartier.constFn pV).range) → ∀ a : W.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn pW) a = 0) → a ∈ (GlobalTheory.Cartier.constFn pW).range := by
  first | exact @GlobalTheory.ConstDescent.descent | exact GlobalTheory.ConstDescent.descent | (intros; apply GlobalTheory.ConstDescent.descent <;> assumption)
