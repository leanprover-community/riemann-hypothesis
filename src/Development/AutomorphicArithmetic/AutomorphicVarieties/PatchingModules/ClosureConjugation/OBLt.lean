module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.StCoiLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UnitsExist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DCorner
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.IdemNil
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem oB_lt {n a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ n) (i : Fin n) :
    ((oB n a i : Fin n) : ℕ) < a ↔ (i : ℕ) < a := by
  unfold oB
  split_ifs with hi
  · simp only [hi, iff_true]
    exact h1
  · simp only [hi, iff_false, not_lt]
    have := i.2
    omega

private theorem oB_oB {n a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ n) (i : Fin n) : oB n a (oB n a i) = oB n a i := by
  have key := oB_lt h1 h2 i
  unfold oB at key ⊢
  by_cases hi : (i : ℕ) < a
  · have : ((if (i : ℕ) < a then (⟨0, by omega⟩ : Fin n) else ⟨n - 1, by omega⟩ : Fin n) : ℕ) < a := key.2 hi
    simp only [hi, if_true] at this ⊢
    simp only [this, if_true]
  · have : ¬ ((if (i : ℕ) < a then (⟨0, by omega⟩ : Fin n) else ⟨n - 1, by omega⟩ : Fin n) : ℕ) < a :=
      fun h => hi (key.1 h)
    simp only [hi, if_false] at this ⊢
    simp only [this, if_false]

private theorem single_mem {F : Type} [Field F] {n a : ℕ} (p q : Fin n) (h : (p : ℕ) < a ↔ (q : ℕ) < a) :
    (single p q 1 : Matrix (Fin n) (Fin n) F) ∈ Ev F F n a := by
  intro i j
  refine ⟨fun _ => Submodule.mem_top, fun hij => ?_⟩
  rw [Matrix.single_apply]
  split_ifs with hpq
  · obtain ⟨rfl, rfl⟩ := hpq
    exact absurd h hij
  · exact Submodule.zero_mem _

theorem UpperTheory.V.Pa.idem :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Module.Finite B E] (a : ℕ) (D : Det n B E) (T : TrInv B E) (r : E →ₐ[B] Matrix (Fin n) (Fin n) F), 1 ≤ a → a ≤ n → IsUnit (2 : B) → D.IsCH → (∀ y, T.tr y = D.tr y) → RingHom.ker (algebraMap B F) = maximalIdeal B → (∀ y, (D.chi y).map (algebraMap B F) = (r y).charpoly) → (∀ y, r (T.st y) = (r y)ᵀ) → (∀ Z ∈ Ev F F n a, ∃ y, r y = Z) → ∃ U : T.Units (Fin n) (oB n a), (∀ i, r (U.x i) = single (oB n a i) i 1) ∧ ∀ i, D.D B[X] (1 + X ⊗ₜ U.ep i) = 1 + X := by
  intro B E F _ _ _ _ _ _ n _ _ _ a D T r h1 h2 h2u hCH htr hker hchi hst hsurj
  have hn : 1 ≤ n := le_trans h1 h2
  haveI : IsAdicComplete (maximalIdeal B) E := GlobalTheory.isAdicComplete_of_finite (maximalIdeal B) E
  obtain ⟨hnil, hidem⟩ := idem_nil D r hCH hker hchi
  have hdiag : ∀ i : Fin n, ∃ y, r y = single i i 1 := fun i =>
    hsurj _ (single_mem i i Iff.rfl)
  obtain ⟨ep, hcoi, hstep, hrep⟩ :=
    st_coi_lift T (maximalIdeal B) r h2u (le_of_eq hker.symm) hnil hst hdiag
  have hD : ∀ i, D.D B[X] (1 + X ⊗ₜ ep i) = 1 + X := fun i =>
    hidem (ep i) i (hcoi.idem i) (hrep i)
  have hcorner := fun i => d_corner D (ep i) hCH (hcoi.idem i) (hD i) hn
  haveI : HenselianRing B (RingHom.ker (algebraMap B F)) := by
    rw [hker]
    infer_instance
  obtain ⟨U, hUep, hUx⟩ := units_exist T (oB n a) r ep h2u (fun i => oB_oB h1 h2 i) hst
    (fun i => hsurj _ (single_mem _ _ (oB_lt h1 h2 i))) hcoi hstep hrep
    (fun i => by rw [htr]; exact (hcorner i).2.1)
    (fun i y => ⟨D.tr (ep i * y), (hcorner i).1 y⟩)
  refine ⟨U, hUx, fun i => ?_⟩
  rw [hUep]
  exact hD i
