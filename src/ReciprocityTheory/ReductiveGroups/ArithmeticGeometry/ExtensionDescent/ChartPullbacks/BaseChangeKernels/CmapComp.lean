module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

abbrev cmap {κ X A : Type} [AddCommGroup X] [CommRing A] (b : Module.Basis κ ℤ X) (v : κ → Aˣ) :
    Multiplicative X →* A :=
  (Units.coeHom A).comp (AddMonoidHom.toMultiplicativeLeft
    (b.constr ℤ (fun k => Additive.ofMul (v k))).toAddMonoidHom)

theorem cmap_comp {κ X A A' : Type} [AddCommGroup X] [CommRing A] [CommRing A']
    (b : Module.Basis κ ℤ X) (ρ : A →+* A') (v : κ → Aˣ) (v' : κ → A'ˣ)
    (hv : ∀ k, (v' k).val = ρ (v k).val) (x : Multiplicative X) :
    cmap b v' x = ρ (cmap b v x) := by
  have hlin : b.constr ℤ (fun k => Additive.ofMul (v' k)) =
      (MonoidHom.toAdditive (Units.map (ρ : A →* A'))).toIntLinearMap ∘ₗ
        b.constr ℤ (fun k => Additive.ofMul (v k)) := by
    refine b.ext (fun k => ?_)
    rw [LinearMap.comp_apply, Module.Basis.constr_basis, Module.Basis.constr_basis]
    show Additive.ofMul (v' k) = Additive.ofMul (Units.map (ρ : A →* A') (v k))
    congr 1
    exact Units.ext (by simpa using hv k)
  have hx := congrArg (fun f => ((Additive.toMul (f (Multiplicative.toAdd x)) : A'ˣ) : A')) hlin
  first
  | exact hx
  | simpa using hx

open ReciprocityTheory.ChartRestriction.G.Semi in
theorem appLE_res {X Y : Scheme.{0}} (g : Y ⟶ X) {U U₀ : X.Opens} (hU : U ≤ U₀) {V W : Y.Opens}
    (hV : V ≤ g ⁻¹ᵁ U) (hW : W ≤ g ⁻¹ᵁ U₀) (hVW : V ≤ W) (u : Γ(X, U₀)ˣ) :
    (res hVW (res hW (pullU g U₀ u))).val = (g.appLE U V hV).hom (res hU u).val := by
  have key : g.app U₀ ≫ Y.presheaf.map (homOfLE hW).op ≫ Y.presheaf.map (homOfLE hVW).op =
      X.presheaf.map (homOfLE hU).op ≫ g.appLE U V hV := by
    rw [Scheme.Hom.map_appLE, ← Functor.map_comp, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  have h2 := congrArg (fun f => f.hom u.val) key
  first
  | exact h2
  | simpa [res, pullU] using h2

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
