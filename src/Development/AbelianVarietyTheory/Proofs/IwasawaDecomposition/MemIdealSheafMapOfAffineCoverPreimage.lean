module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
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
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.IdealPushCover

theorem mem_map_ideal_of_cover : ∀ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) [QuasiCompact ρ] (I : Y'.IdealSheafData) (U : X.affineOpens) {ι : Type} (W : ι → Y'.affineOpens) (hW : ∀ i, (W i : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens)), ρ ⁻¹ᵁ (U : X.Opens) ≤ ⨆ i, (W i : Y'.Opens) → ∀ b : Γ(X, U), (∀ i, (ρ.appLE U (W i) (hW i)).hom b ∈ I.ideal (W i)) → b ∈ (I.map ρ).ideal U := by
  intro X Y' ρ _ I U ι W hW hcov b hb
  have hk : ∀ V : Y'.affineOpens, I.ideal V = RingHom.ker (I.subschemeι.app V.1).hom := fun V => by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  rw [Scheme.IdealSheafData.map, Scheme.Hom.ker_apply, RingHom.mem_ker, Scheme.Hom.comp_app]
  change (I.subschemeι.app (ρ ⁻¹ᵁ U.1)).hom ((ρ.app U.1).hom b) = 0
  refine GlobalTheory.Cartier.ext_germ fun z hz => ?_
  rw [map_zero]
  have hz' : I.subschemeι z ∈ ⨆ i, (W i : Y'.Opens) := hcov hz
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz'
  have hzi : z ∈ I.subschemeι ⁻¹ᵁ (W i : Y'.Opens) := hi
  have h0 : (I.subschemeι.app (W i).1).hom ((ρ.appLE U (W i) (hW i)).hom b) = 0 := by
    have := hb i
    rw [hk, RingHom.mem_ker] at this
    exact this
  have e1 : (ρ.appLE U (W i) (hW i)).hom b = resG Y' (hW i) ((ρ.app U.1).hom b) := rfl
  rw [e1, GlobalTheory.Cartier.app_resG] at h0
  rw [← GlobalTheory.Cartier.germ_resG (I.subschemeι.preimage_mono (hW i)) z hzi, h0, map_zero]

end GlobalTheory.IdealPushCover
