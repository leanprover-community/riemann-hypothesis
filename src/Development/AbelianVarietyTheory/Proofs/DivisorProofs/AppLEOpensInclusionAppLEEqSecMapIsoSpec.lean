module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

namespace GlobalTheory.CechDR

theorem appLE_ι_appLE_eq_secMap : ∀ (X T : Scheme.{0}) (p : T ⟶ X) (U : X.affineOpens) (O : T.Opens) (hO : O ≤ p ⁻¹ᵁ U.1) (V : (p ⁻¹ᵁ U.1).toScheme.Opens) (e : V ≤ (p ⁻¹ᵁ U.1).ι ⁻¹ᵁ O) (r : Γ(X, U.1)), ((p ⁻¹ᵁ U.1).ι.appLE O V e).hom ((p.appLE U.1 O hO).hom r) = (GlobalTheory.CechDR.secMap ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) V).hom r := by
  intro X T p U O hO V e r
  have hU : IsAffineOpen U.1 := U.2
  have key : (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ ((p ∣_ U.1) ≫ hU.isoSpec.hom).appLE ⊤ V (by simp) =
      p.appLE U.1 O hO ≫ (p ⁻¹ᵁ U.1).ι.appLE O V e := by
    change (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ (Scheme.Hom.appTop ((p ∣_ U.1) ≫ hU.isoSpec.hom) ≫
      (p ⁻¹ᵁ U.1).toScheme.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) = _
    rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change U.1.topIso.inv ≫ (p ∣_ U.1).appLE ⊤ V (show V ≤ (p ∣_ U.1) ⁻¹ᵁ ⊤ from fun _ _ => trivial) = _
    rw [morphismRestrict_appLE, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    exact (p.map_appLE _ _).trans (p.appLE_map _ _).symm
  exact (congrArg (fun f => f.hom r) key).symm

end GlobalTheory.CechDR
