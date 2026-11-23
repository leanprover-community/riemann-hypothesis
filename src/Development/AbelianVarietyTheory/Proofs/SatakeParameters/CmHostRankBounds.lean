module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
public import Mathlib.RingTheory.RingHom.Unramified
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.W1

theorem dv_mem_span_of_formallyUnramified : ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) (B' : Subalgebra k L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.FormallyUnramified → ∀ v ∈ B', ∃ (m : ℕ) (b : Fin m → L) (w : Fin m → K), (∀ j, b j ∈ B' ∧ w j ∈ B) ∧ ι1 (D k L v) = ∑ j, b j • mapDR k K L (ι1 (D k K (w j))) := by
  intro k K L _ _ _ _ _ _ _ B B' φ hφ hU v hv
  letI := φ.toAlgebra
  haveI : IsScalarTower k B B' := IsScalarTower.of_algebraMap_eq fun c => by
    apply Subtype.ext
    change algebraMap k L c = ((φ (algebraMap k B c) : B') : L)
    rw [hφ, IsScalarTower.algebraMap_apply k K L]
    rfl
  haveI : Algebra.FormallyUnramified B B' := hU
  have hspan : Submodule.span B' (Set.range fun a : B => KaehlerDifferential.D k B' (φ a)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨y, rfl⟩ :=
      (KaehlerDifferential.exact_mapBaseChange_map k B B' x).mp (Subsingleton.elim _ _)
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | tmul b m =>
      rw [KaehlerDifferential.mapBaseChange_tmul]
      refine Submodule.smul_mem _ b ?_
      have hm : m ∈ Submodule.span B (Set.range (KaehlerDifferential.D k B)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        rw [KaehlerDifferential.map_D]
        exact Submodule.subset_span ⟨a, rfl⟩
      | zero => simp
      | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
      | smul a x _ hx =>
        rw [map_smul, ← algebraMap_smul B' a]
        exact Submodule.smul_mem _ _ hx
  have hmem : KaehlerDifferential.D k B' ⟨v, hv⟩ ∈
      Submodule.span B' (Set.range fun a : B => KaehlerDifferential.D k B' (φ a)) := hspan ▸ Submodule.mem_top
  obtain ⟨n, f, g, hsum⟩ := Submodule.mem_span_set'.mp hmem
  choose w hw using fun j => (g j).2
  refine ⟨n, fun j => (f j : L), fun j => (w j : K), fun j => ⟨(f j).2, (w j).2⟩, ?_⟩
  have key : KaehlerDifferential.D k L v = ∑ j, (f j : L) • KaehlerDifferential.D k L (algebraMap K L (w j)) := by
    have h := congrArg (KaehlerDifferential.map k k B' L) hsum

    rw [map_sum, KaehlerDifferential.map_D] at h
    refine h.symm.trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ← hw j, KaehlerDifferential.map_D, ← hφ]
    first | rfl | simp [Subalgebra.smul_def]
  have hpull : ∀ a : K, mapDR k K L (ι1 (D k K a)) = ι1 (D k L (algebraMap K L a)) := by
    intro a
    rw [mapDR, ExteriorAlgebra.lift_ι_apply]
    simp [map1]

  simp_rw [hpull, key, map_sum, map_smul]

end GlobalTheory.W1
