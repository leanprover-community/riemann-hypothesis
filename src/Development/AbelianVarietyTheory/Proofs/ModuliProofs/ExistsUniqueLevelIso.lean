module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.AlgebraLevelSetting
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfLevel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTower
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UU
open GlobalTheory.IndefiniteRowSideFullHecke.AlgebraLevelSetting (SymTriv Level Step FormalTorus Lv pr torus_w)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UniformizationSetting

section Formal
variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
  [IsCommMonObj G] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

local notation "𝔪" => IsLocalRing.maximalIdeal V

omit [IsDomain V] in
instance connectedSpace_level (e : ℕ) : ConnectedSpace (Spec (CommRingCat.of (V ⧸ 𝔪 ^ (e + 1)))) :=
  SplitTorus.connectedSpace_of_isLocalRing _


omit [IsDomain V] [GrpObj G] [IsCommMonObj G] in
theorem thickMap_pr (e : ℕ) : thickMap V 𝔪 e G ≫ pr 𝔪 (e + 1) G = pr 𝔪 e G :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)


omit [IsDomain V] in
theorem nonempty_formalTorus (hG : IsSemiAbelian G) (Q₀ : TQ (thickObj V 𝔪 0 G) X) :
    Nonempty (FormalTorus 𝔪 Q₀.i) := by
  have := hG.smooth
  have := hG.geomConnected
  have hs : ∀ e, Smooth (thickObj V 𝔪 e G).hom := fun e => by
    show Smooth (pullback.snd _ _)
    infer_instance
  have hc : ∀ e, GeometricallyConnected (thickObj V 𝔪 e G).hom := fun e => by
    show GeometricallyConnected (pullback.snd _ _)
    infer_instance
  have step : ∀ (e : ℕ) (Q : TQ (thickObj V 𝔪 e G) X), ∃ Q' : TQ (thickObj V 𝔪 (e + 1) G) X,
      TorusCompat (thickTrans V _ e) (thickMap V _ e G) Q.i Q'.i := fun e Q => by
    exact exists_tq_lift (TowerEx.isNilpotent_max (e + 1)) _ (Ideal.Quotient.factor_surjective _) _ _
      (TowerEx.isGrpPullback_thickMap 𝔪 e G) Q
  choose nxt hnxt using step
  let Q : ∀ e, TQ (thickObj V 𝔪 e G) X := fun e => Nat.rec (motive := fun e => TQ (thickObj V 𝔪 e G) X) Q₀ nxt e
  exact ⟨⟨fun e => (Q e).i, fun e => (Q e).i_hom, rfl, fun e => hnxt e (Q e)⟩⟩



end Formal

end GlobalTheory.UniformizationSetting
end
