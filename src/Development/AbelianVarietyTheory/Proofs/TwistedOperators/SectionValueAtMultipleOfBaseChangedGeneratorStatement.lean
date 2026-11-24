module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SectionValueAtMultipleOfBaseChangedGenerator
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
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.FibrePushforward
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

theorem _root_.GlobalTheory.T.section_value_at_multiple_of_baseChanged_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ (T Ω : Type) [CommRing T] [IsReduced T] [Algebra c.F T] [Field Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (z₀ : FrPt Xo c T) (z₁ : FrPt Xo c Ω) (a₀ : T), z₁.x = spMap χ.toRingHom ≫ z₀.x → (∀ τ j, z₁.u τ j = spMap (dualMap χ.toRingHom) ≫ z₀.u τ j) → SecBC χ.toRingHom a₀ z₀.x z₁.x z₀.s z₁.s → evR Xo c f z₁ = χ (a₀ ^ n * evR Xo c f z₀) := by
  first | exact @GlobalTheory.HkValueMul.evR_of_secBC_mul | exact GlobalTheory.HkValueMul.evR_of_secBC_mul | (intros; apply GlobalTheory.HkValueMul.evR_of_secBC_mul <;> assumption)
