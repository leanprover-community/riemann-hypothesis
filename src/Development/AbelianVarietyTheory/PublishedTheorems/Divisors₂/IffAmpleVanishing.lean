import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianAmpleAcyclic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleRelativelyAcyclic

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxForm (IsRelAcyclic)
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.RelAcyclicAmple
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleAcyclicModel




example : (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℚ).IsElliptic :=
  ⟨by
    rw [isUnit_iff_ne_zero]
    norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]⟩


end GlobalTheory.AmpleAcyclicModel
