module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperNormalCompactification
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.proper_normal_compactification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ), Function.Injective β → (∀ x : c.F, ∃ a b : O, b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → IsProper Y.s ∧ NormalCpt (Z.ξ₀ ≫ Y.j) ∧ (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap (Z.inc.comp β) ∧ (∀ x, x ∈ Z.genFib ↔ ∀ o : O, o ≠ 0 → unitAt (Z.ξ₀ ≫ Y.j) x (Z.inc (β o))) ∧ FiniteDimensional Z.Ω Z.V ∧ Module.finrank Z.Ω (eigSp Z.ρ (Z.inc.comp (tauIn c τ))) = D.p ∧ Module.finrank Z.Ω (eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) = D.q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.model_cpt_facts | exact GlobalTheory.CompanionTheory.Ar.Flat.model_cpt_facts | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.model_cpt_facts <;> assumption)
