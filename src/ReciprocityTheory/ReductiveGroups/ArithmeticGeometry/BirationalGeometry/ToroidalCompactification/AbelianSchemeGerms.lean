module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {S : Scheme.{0}}

theorem isAbelianScheme_of_proper (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) [IsProper G.hom] :
    IsAbelianScheme G :=
  ⟨hG.comm, hG.smooth, inferInstance, hG.geomConnected⟩

theorem isAbelianScheme_tensor (G H : Over S) [GrpObj G] [GrpObj H] (hG : IsAbelianScheme G)
    (hH : IsAbelianScheme H) : IsAbelianScheme (G ⊗ H) := by
  have := hG.comm
  have := hH.comm
  have := hG.smooth
  have := hH.smooth
  have := hG.proper
  have := hH.proper
  have := hG.geomConnected
  have := hH.geomConnected
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [Over.tensorObj_hom, pullback.condition]
    infer_instance
  · rw [Over.tensorObj_hom, pullback.condition]
    infer_instance
  · rw [Over.tensorObj_hom, pullback.condition]
    exact GeometricallyConnected.comp _ _

theorem isAbelianScheme_tensor_unit (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) :
    IsAbelianScheme (G ⊗ 𝟙_ (Over S)) := by
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  have hc : (G ⊗ 𝟙_ (Over S)).hom = pullback.snd G.hom (𝟙_ (Over S)).hom := by
    rw [Over.tensorObj_hom, pullback.condition]
    exact Category.comp_id _
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [hc]; infer_instance
  · rw [hc]; infer_instance
  · rw [hc]; infer_instance

theorem isAbelianScheme_powObj (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) :
    ∀ n : ℕ, IsAbelianScheme (powObj G (n + 1))
  | 0 => isAbelianScheme_tensor_unit G hG
  | n + 1 => isAbelianScheme_tensor G (powObj G (n + 1)) hG (isAbelianScheme_powObj G hG n)

theorem globalFns_powObj (hGF : GlobalFnsSt) (G : Over S) [GrpObj G] (hG : IsSemiAbelian G)
    [IsProper G.hom] (n : ℕ) : Function.Bijective (powObj G n).hom.appTop.hom := by
  cases n with
  | zero =>
    show Function.Bijective (𝟙 S : S ⟶ S).appTop.hom
    simp only [Scheme.Hom.id_appTop, CommRingCat.hom_id]
    exact Function.bijective_id
  | succ n => exact hGF _ _ (isAbelianScheme_powObj G (isAbelianScheme_of_proper G hG) n)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms
