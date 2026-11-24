module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
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
import Mathlib.Tactic.Linter.HaveILetI
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

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.wtCut :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [Group D] [TopologicalSpace D] (I : Subgroup D) (d k m : ℕ) (A N : Type) [AddCommGroup A] [Finite A] [AddCommGroup N], GenI l I d → (∀ x : A, l ^ k • x = 0) → ∀ (Z : AddSubgroup (D → N)), Finite Z → ∀ p : Fin m → N →+ A, (∀ z ∈ Z, IsLocallyConstant z ∧ ∀ j s s', p j (z (s * s')) = p j (z s) + p j (z s')) → Nat.card Z ≤ {z | z ∈ Z ∧ ∀ j, ∀ s ∈ I, p j (z s) = 0}.ncard * Nat.card A ^ (m * d) := by
  intro l _ D _ _ I d k m A N _ _ _ hG hA Z _ p hZ
  obtain ⟨u, -, hu⟩ := hG
  let Φ : Z →+ (Fin m → Fin d → A) :=
    { toFun := fun z j a => p j (z.1 (u a))
      map_zero' := by
        funext j a
        simp
      map_add' := by
        intro x y
        funext j a
        simp }
  let S : Set (D → N) := {z | z ∈ Z ∧ ∀ j, ∀ s ∈ I, p j (z s) = 0}
  have hSfin : S.Finite := Set.Finite.subset (Set.toFinite (Z : Set (D → N))) (fun z hz => hz.1)
  have hker : ∀ z ∈ Φ.ker, (z : D → N) ∈ S := by
    intro z hz
    refine ⟨z.2, fun j s hs => ?_⟩
    have hz0 : ∀ a, p j (z.1 (u a)) = 0 := fun a => congrFun (congrFun hz j) a
    exact hu k A hA (fun s => p j (z.1 s)) ((hZ _ z.2).1.comp (p j))
      (fun s t => (hZ _ z.2).2 j s t) hz0 s hs
  have h1 : Nat.card Φ.ker ≤ S.ncard := by
    rw [← Nat.card_coe_set_eq]
    haveI := hSfin.to_subtype
    refine Nat.card_le_card_of_injective (fun z : Φ.ker => (⟨z.1.1, hker z.1 z.2⟩ : S)) ?_
    intro a b hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext (Subtype.ext hab)
  have h2 : Nat.card Φ.range ≤ Nat.card A ^ (m * d) := by
    calc Nat.card Φ.range ≤ Nat.card (Fin m → Fin d → A) :=
          Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective
      _ = Nat.card A ^ (m * d) := by
          simp only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin]
          rw [← pow_mul, mul_comm]
  calc Nat.card Z = Nat.card Φ.ker * Φ.ker.index := (AddSubgroup.card_mul_index _).symm
    _ = Nat.card Φ.ker * Nat.card Φ.range := by rw [AddSubgroup.index_ker]
    _ ≤ S.ncard * Nat.card A ^ (m * d) := Nat.mul_le_mul h1 h2
