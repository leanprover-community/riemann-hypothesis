module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTangentOfSingleAffineChart
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

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.hasTangent_of_single_affineChart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (E : Type) [Field E] (c : E) (b : Sp E ⟶ S) (ξ : Sp (PowerSeries E) ⟶ G.left), IsPath G c b ξ → ∀ (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → E) (U : G.left.Opens), IsAffineOpen U → ∀ (hU : ⊤ ≤ ξ ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ V'), (∀ f : Γ(G.left, U), PowerSeries.coeff 1 (evAt ξ hU f) = ∑ i, w i * evAt b hb (dualApp (τ i) hV (dUnit G he f))) → HasTan G b ξ τ w := by
  first | exact @GlobalTheory.Nef.hasTan_of_affine_chart | exact GlobalTheory.Nef.hasTan_of_affine_chart | (intros; apply GlobalTheory.Nef.hasTan_of_affine_chart <;> assumption)
