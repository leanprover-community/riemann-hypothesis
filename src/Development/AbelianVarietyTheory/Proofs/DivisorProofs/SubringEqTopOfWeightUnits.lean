module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenAndBijectiveOfWeightUnits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSmoothAffineSurjectiveFourierTerms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum



theorem subring_eq_top_of_weight_units : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (i : splitTorus (Sp R) D.X ⟶ Y.H), IsMonHom i → IsPullback i (toUnit _) Y.q η[D.P.A] → ∀ {κ : Type} (bs : Module.Basis κ ℤ D.X) (V : D.P.A.left.Opens), IsAffineOpen V → ∀ (u : κ → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)ˣ), (∀ c, GlobalTheory.UU.IsWt i _ (u c).val (bs c)) → ∀ S : Subring Γ(Y.H.left, Y.q.left ⁻¹ᵁ V), (∀ c, (Y.q.left.app V).hom c ∈ S) → (∀ c, (u c).val ∈ S ∧ ((u c)⁻¹).val ∈ S) → S = ⊤ := by
  intro R _ _ D Y i hi hk κ bs V hV u hu S hS hSu
  obtain ⟨hsm, haff, hsurj⟩ := Y.q_props
  have hmon : IsMonHom Y.q := Y.isMonHom_q
  let m : Multiplicative D.X →* Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)ˣ :=
    AddMonoidHom.toMultiplicativeLeft (bs.constr ℤ (fun k => Additive.ofMul (u k))).toAddMonoidHom
  have hm : ∀ k, m (Multiplicative.ofAdd (bs k)) = u k := fun k =>
    congrArg Additive.toMul (bs.constr_basis ℤ (fun k => Additive.ofMul (u k)) k)
  have key : ∀ χ : D.X, GlobalTheory.UU.IsWt i _ (m (Multiplicative.ofAdd χ)).val χ ∧
      (m (Multiplicative.ofAdd χ)).val ∈ S ∧ (m (Multiplicative.ofAdd χ))⁻¹.val ∈ S := by
    intro χ
    have hχ : χ ∈ AddSubgroup.closure (Set.range bs) := by
      rw [← Submodule.span_int_eq_addSubgroupClosure, bs.span_eq]; trivial
    refine AddSubgroup.closure_induction (p := fun x _ => GlobalTheory.UU.IsWt i _ (m (Multiplicative.ofAdd x)).val x ∧
      (m (Multiplicative.ofAdd x)).val ∈ S ∧ (m (Multiplicative.ofAdd x))⁻¹.val ∈ S) ?_ ?_ ?_ ?_ hχ
    · rintro _ ⟨k, rfl⟩
      rw [hm]; exact ⟨hu k, hSu k⟩
    · rw [ofAdd_zero, map_one]; exact ⟨GlobalTheory.UU.isWt_one, S.one_mem, by simpa using S.one_mem⟩
    · intro x y _ _ hx hy
      rw [ofAdd_add, map_mul]
      refine ⟨hx.1.mul hy.1, ?_, ?_⟩
      · rw [Units.val_mul]; exact S.mul_mem hx.2.1 hy.2.1
      · rw [mul_inv, Units.val_mul]; exact S.mul_mem hx.2.2 hy.2.2
    · intro x _ hx
      rw [ofAdd_neg, map_inv]
      exact ⟨hx.1.inv, hx.2.2, by rw [inv_inv]; exact hx.2.1⟩
  have hbij := (isAffineOpen_and_bijective_of_weight_units (Sp R) D.X Y.H D.P.A Y.q i hmon hi inferInstance
    hsurj inferInstance hk V hV m (fun χ => (key χ).1)).2
  refine (Subring.eq_top_iff' S).2 fun f => ?_
  obtain ⟨x, rfl⟩ := hbij.2 f
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; exact S.zero_mem
  | add a b ha hb => rw [map_add (f := _)]; exact S.add_mem ha hb
  | single χ c =>
    change AddMonoidAlgebra.liftNC _ _ _ ∈ S
    rw [AddMonoidAlgebra.liftNC_single]
    exact S.mul_mem (hS c) (key χ).2.1

end GlobalTheory.Mum
