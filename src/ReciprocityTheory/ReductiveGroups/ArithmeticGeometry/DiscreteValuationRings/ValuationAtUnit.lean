module

public import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.ValuationAtUnit

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem exists_glue_ratio {Y : Scheme.{0}} {M : LB Y} (hc : ⨆ j, M.U j = ⊤) (s : LB.Sec M) (τ : LB.Gen M)
    (hτ : τ.IsGen) : ∃ a : Γ(Y, ⊤), ∀ j, s.f j = (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom a * (τ.s j).val := by
  let r : ∀ j, Γ(Y, M.U j) := fun j => s.f j * ((τ.s j)⁻¹ : Γ(Y, M.U j)ˣ).val
  have compat : ∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)).op).hom (r i) =
      (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom (r j) := by
    intro i j
    have hs := s.compat i j
    have hti : (Y.presheaf.map (homOfLE (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)).op).hom ((τ.s i)⁻¹ : Γ(Y, M.U i)ˣ).val =
        (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom ((τ.s j)⁻¹ : Γ(Y, M.U j)ˣ).val *
          ((M.g i j)⁻¹ : Γ(Y, M.U i ⊓ M.U j)ˣ).val := by
      have := congrArg (fun u => (u⁻¹ : Γ(Y, M.U i ⊓ M.U j)ˣ).val) (hτ i j)
      simp only [mul_inv_rev, Units.val_mul] at this
      exact this
    have hg : (M.g i j : Γ(Y, M.U i ⊓ M.U j)ˣ).val * ((M.g i j)⁻¹ : Γ(Y, M.U i ⊓ M.U j)ˣ).val = 1 := by
      rw [← Units.val_mul, _root_.mul_inv_cancel, Units.val_one]
    simp only [r, map_mul]
    rw [hs, hti]
    linear_combination ((Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom (s.f j) *
      (Y.presheaf.map (homOfLE (inf_le_right : M.U i ⊓ M.U j ≤ M.U j)).op).hom ((τ.s j)⁻¹ : Γ(Y, M.U j)ˣ).val) * hg
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' M.U ⊤ (fun j => homOfLE le_top) hc.ge r compat
  have ha' : ∀ j, (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom a = r j := ha
  refine ⟨a, fun j => ?_⟩
  rw [ha' j]
  simp only [r]
  rw [_root_.mul_assoc, ← Units.val_mul, _root_.inv_mul_cancel, Units.val_one, _root_.mul_one]

end ReciprocityTheory.ChartRestriction.G.DVR.ValuationAtUnit
