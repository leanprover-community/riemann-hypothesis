module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.NotEvenIrr
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

theorem UpperTheory.ncard_unit_translates_order_eq_relIndex :
    ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (τ : K) (a : (Etau K τ)ˣ) (y : Etau K τ), {S : Set (Etau K τ) | ∃ u ∈ Gu O τ, S = PS.ml (a * u) (Ord O y)}.ncard = (Hu O y).relIndex (Gu O τ) := by
  intro O K _ _ _ τ a y
  set G := Gu O τ
  set H := (Hu O y).subgroupOf G
  have key : ∀ g₁ g₂ : G, PS.ml (a * (g₁ : (Etau K τ)ˣ)) (PK.Ord O y) =
      PS.ml (a * (g₂ : (Etau K τ)ˣ)) (PK.Ord O y) ↔ g₁⁻¹ * g₂ ∈ H := by
    intro g₁ g₂
    rw [Subgroup.mem_subgroupOf]
    show _ ↔ PS.ml (((g₁⁻¹ * g₂ : G)) : (Etau K τ)ˣ) (PK.Ord O y) = PK.Ord O y
    rw [PS.ml_mul, PS.ml_mul, (PS.ml_inj a).eq_iff, Subgroup.coe_mul, Subgroup.coe_inv, PS.ml_mul]
    constructor
    · intro h
      rw [← h, ← PS.ml_mul, inv_mul_cancel, PS.ml_one]
    · intro h
      conv_lhs => rw [← h]
      rw [← PS.ml_mul, mul_inv_cancel, PS.ml_one]
  let f : G ⧸ H → Set (Etau K τ) :=
    Quotient.lift (fun g : G => PS.ml (a * (g : (Etau K τ)ˣ)) (PK.Ord O y))
      (fun g₁ g₂ hg => (key g₁ g₂).2 (QuotientGroup.leftRel_apply.1 hg))
  have hf : Function.Injective f := by
    intro q₁ q₂ hq
    obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective q₂
    exact QuotientGroup.eq.2 ((key _ _).1 hq)
  have hrange : {S : Set (Etau K τ) | ∃ u ∈ G, S = PS.ml (a * u) (PK.Ord O y)} = Set.range f := by
    ext S
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨((⟨u, hu⟩ : G) : G ⧸ H), rfl⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨g, g.2, rfl⟩
  rw [hrange, Set.ncard_range_of_injective hf]
  rfl
