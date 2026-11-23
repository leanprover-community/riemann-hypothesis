module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PushExLeft
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolomorphicUniformisationExpModelFiber
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isHolomorphic_uniformisationExp_modelFiber : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → IsHolTo Set.univ (fun z => (pushEx Z Fu y i P p hu hp z).left) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.pushEx_hol | exact GlobalTheory.ShFam.Hor.LogCh.pushEx_hol | (intros; apply GlobalTheory.ShFam.Hor.LogCh.pushEx_hol <;> assumption)
