module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodCmPointOfIntegralCmObject
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.exists_good_cm_point_of_integral_cm_object : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (ρ : 𝓞 K) (σ : K →+* ℂ) (X : CMObj H K ρ σ Dw.p Dw.q) (La : ℝ) (x : Sp K ⟶ Xo.X) (Φ : FibKey Xo K x) (_ : SABMap Φ.T.t X.B.t (spMap (algebraMap (𝓞 K) K))), (∀ τ, τ ∈ LamF.psiSet H ↔ LamF.labK c K τ (H.rt : E) = (ρ : K)) → (∀ j (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ La ^ 2) → x ≫ Xo.s = sOf c K → ∀ (S : Type) [CommRing S] [Algebra c.F S] (σ₁ : K →ₐ[c.F] S), ∃ (z : CMPt Xo c) (σ' : z.K →ₐ[c.F] S), z.Good (Module.finrank ℚ E / 2) La ∧ spMap σ'.toRingHom ≫ z.y.x = spMap σ₁.toRingHom ≫ x := by
  first | exact @GlobalTheory.LamT.exists_cmPt_good_of_cmObj | exact GlobalTheory.LamT.exists_cmPt_good_of_cmObj | (intros; apply GlobalTheory.LamT.exists_cmPt_good_of_cmObj <;> assumption)
