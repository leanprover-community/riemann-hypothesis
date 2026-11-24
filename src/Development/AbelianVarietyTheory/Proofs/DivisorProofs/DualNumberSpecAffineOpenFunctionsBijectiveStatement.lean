module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSpecAffineOpenFunctionsBijective
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

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB

theorem _root_.GlobalTheory.T.dualNumberSpec_affineOpen_functions_bijective : ∀ (O : Type) [CommRing O] (V : (Sp O).Opens), IsAffineOpen V → Function.Bijective (fun ab : Γ(Sp O, V) × Γ(Sp O, V) => (specO O (DualNumber O)).hom.appLE V ((specO O (DualNumber O)).hom ⁻¹ᵁ V) le_rfl ab.1 + (specO O (DualNumber O)).hom.appLE V ((specO O (DualNumber O)).hom ⁻¹ᵁ V) le_rfl ab.2 * resG _ le_top (epsFn O)) := by
  first | exact @GlobalTheory.LieVB.bijective_add_mul_epsFn | exact GlobalTheory.LieVB.bijective_add_mul_epsFn | (intros; apply GlobalTheory.LieVB.bijective_add_mul_epsFn <;> assumption)
