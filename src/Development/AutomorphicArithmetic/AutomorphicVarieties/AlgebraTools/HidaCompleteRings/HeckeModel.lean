module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing UpperTheory.V.Hi

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.heckeModel :
    ∀ (A M ι : Type) [CommRing A] [AddCommGroup M] [Module A M] (Y : Submodule A M) (op : ι → Module.End A M), CommOn Y op → ∃ (T : Type) (_ : CommRing T) (_ : Algebra A T) (j : T →ₐ[A] Module.End A Y) (t : ι → T), Function.Injective j ∧ j.range = heckeAlg Y op ∧ (∀ i, Restr (j (t i)) (op i)) ∧ Algebra.adjoin A (Set.range t) = ⊤ ∧ (IsNoetherianRing A → Module.Finite A Y → Module.Finite A T) := by
  intro A M ι _ _ _ Y op h
  have key : ∀ s ∈ {t : Module.End A Y | ∃ i, Restr t (op i)},
      ∀ t ∈ {t : Module.End A Y | ∃ i, Restr t (op i)}, s * t = t * s := by
    rintro s ⟨i, hi⟩ t ⟨j, hj⟩
    refine LinearMap.ext fun y => Subtype.ext ?_
    change (s (t y) : M) = t (s y)
    rw [hi, hj, hj, hi]
    exact h.2 i j y y.2
  have hc : ∀ a b : heckeAlg Y op, a * b = b * a := by
    exact isMulCommutative_iff.mp
      (Algebra.isMulCommutative_adjoin A (fun a ha b hb _ => key a ha b hb))
  let t : ι → heckeAlg Y op := fun i =>
    ⟨(op i).restrict (h.1 i), Algebra.subset_adjoin ⟨i, fun _ => rfl⟩⟩
  have htop : Algebra.adjoin A (Set.range t) = ⊤ := by
    have h1 : Set.range t = ((↑) : heckeAlg Y op → Module.End A Y) ⁻¹'
        {t : Module.End A Y | ∃ i, Restr t (op i)} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, fun _ => rfl⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, Subtype.ext (LinearMap.ext fun y => Subtype.ext (hi y).symm)⟩
    rw [h1]
    exact Algebra.adjoin_adjoin_coe_preimage
  have hfin : IsNoetherianRing A → Module.Finite A Y → Module.Finite A (heckeAlg Y op) := by
    intro _ _
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := Y)
    let f : heckeAlg Y op →ₗ[A] (Fin n → Y) :=
      { toFun := fun t i => (t : Module.End A Y) (s i)
        map_add' := fun a b => by ext i; simp
        map_smul' := fun a b => by ext i; simp }
    have hf : Function.Injective f := by
      intro a b hab
      refine Subtype.ext (LinearMap.ext_on_range hs fun i => ?_)
      exact congrFun hab i
    exact Module.Finite.of_injective f hf
  exact ⟨heckeAlg Y op, { (inferInstance : Ring (heckeAlg Y op)) with mul_comm := hc },
    (inferInstance : Algebra A (heckeAlg Y op)), (heckeAlg Y op).val, t, Subtype.val_injective,
    Subalgebra.range_val _, fun i _ => rfl, htop, hfin⟩
