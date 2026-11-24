module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.BcField
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndRaw

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPolynomial (X C)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Maps

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {x0 : Sp S ⟶ Xo.X} {x0' : Sp S' ⟶ Xo.X}
  (hx : x0' = spMap ψ ≫ x0)

def bcD : overAt x0' (DualNumber S') ⟶ overAt x0 (DualNumber S) :=
  Over.homMk (spMap (dualMap ψ)) (by
    subst hx
    show spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x0 =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ψ ≫ x0
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg])

theorem list_prod_comp {T T' : Over Xo.X} (f : T' ⟶ T) (L : List (T ⟶ Xo.univ.t.G)) :
    (L.map (f ≫ ·)).prod = f ≫ L.prod := by
  induction L with
  | nil => simp [Hom.one_def]
  | cons a L ih => simp only [List.map_cons, List.prod_cons, ih, Hom.mul_def, comp_lift_assoc]

include hx in
theorem isCombAt_bc {k : ℕ} {v : Fin k → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {cf : Fin k → S}
    {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x0 v cf w) :
    IsCombAt x0' (fun i => spMap (dualMap ψ) ≫ v i) (fun i => ψ (cf i)) (spMap (dualMap ψ) ≫ w) := by
  obtain ⟨u, hu, hp⟩ := h
  refine ⟨fun i => bcD ψ hx ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMap ψ) ≫ (u i).left = _
    rw [hu i, ← Category.assoc, spMap_comp_spMap, dualMap_comp_epsMul, ← spMap_comp_spMap, Category.assoc]
  · have e : List.ofFn (fun i => bcD ψ hx ≫ u i) = (List.ofFn u).map (bcD ψ hx ≫ ·) := by
      rw [List.map_ofFn]
      rfl
    rw [e, list_prod_comp, Over.comp_left, hp]
    rfl

end Maps

end ReciprocityTheory.ChartRestriction.G.PullbackSections
