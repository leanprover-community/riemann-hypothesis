module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidArcOfMono
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem arc_rigidity_two_models_of_mono : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c), y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' → y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y = y' ∧ (Mono Y.j → ∃ ψ : W.t.G ≅ W'.t.G, W.Agree W' ψ) :=
  rigidArc_of_mono

end GlobalTheory
