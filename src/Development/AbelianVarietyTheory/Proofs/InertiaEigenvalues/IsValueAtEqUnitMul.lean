module

public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueSecEqMulGen
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ValueTwoGen

def genSec {Y : Scheme.{0}} {M : LB Y} (t : LB.Gen M) (ht : t.IsGen) : LB.Sec M where
  f := fun j => (t.s j).val
  compat := fun i j => congrArg Units.val (ht i j)

theorem exists_unit_gen {Y : Scheme.{0}} (M : LB Y) (hc : ⨆ j, M.U j = ⊤)
    (t t' : LB.Gen M) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ j, (t'.s j).val =
      (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom (w : Γ(Y, ⊤)) * (t.s j).val := by
  obtain ⟨w, hw, -⟩ := GlobalTheory.EvVal.existsUnique_sec_eq_mul_gen M hc (genSec t' ht') t ht
  obtain ⟨w', hw', -⟩ := GlobalTheory.EvVal.existsUnique_sec_eq_mul_gen M hc (genSec t ht) t' ht'
  obtain ⟨_, -, hu⟩ := GlobalTheory.EvVal.existsUnique_sec_eq_mul_gen M hc (genSec t ht) t ht
  have h1 : (1 : Γ(Y, ⊤)) = w' * w := by
    have a := hu 1 (fun j => by simp [genSec])
    have b := hu (w' * w) (fun j => by
      have e1 := hw' j
      have e2 := hw j
      simp only [genSec] at e1 e2 ⊢
      rw [map_mul, _root_.mul_assoc, ← e2, ← e1])
    exact a.trans b.symm
  exact ⟨⟨w, w', by rw [_root_.mul_comm]; exact h1.symm, h1.symm⟩, fun j => hw j⟩

end GlobalTheory.ValueTwoGen
