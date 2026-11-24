module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CgTaylor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.FibreTaylor

theorem fibre_taylor_expansion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (xk : ∀ m, Sp (Jet k (Fin 1 × Fin d) m) ⟶ pullback t.G.hom x), (∀ m, xk m ≫ pullback.fst _ _ = (g.x m).left) → (∀ m, xk m ≫ pullback.snd _ _ = spMap (algebraMap k _)) → ∃ _ : IsIntegral (pullback t.G.hom x), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (pullback t.G.hom x) ∧ CharP (pullback t.G.hom x).functionField p ∧ ∀ (U : (pullback t.G.hom x).Opens) (hU : ∀ m, ⊤ ≤ xk m ⁻¹ᵁ U) [Nonempty U] (f : Γ(pullback t.G.hom x, U)), ∃ F : MvPowerSeries (Fin 1 × Fin d) k, (∀ m, ((xk m).appLE U ⊤ (hU m)).hom f = toΓ _ (psJet m F)) ∧ (F = 0 → f = 0) ∧ ((∀ q, MvPowerSeries.pderiv (R := k) q F = 0) → ∃ r : (pullback t.G.hom x).functionField, r ^ p = ((pullback t.G.hom x).germToFunctionField U).hom f) :=
  PositivityTheory.HtPt.Cg.fibre_taylor

end GlobalTheory.CompanionTheory.Ar.FibreTaylor
