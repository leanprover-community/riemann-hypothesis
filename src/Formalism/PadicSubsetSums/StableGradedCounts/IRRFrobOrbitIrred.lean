module

public import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Normal.Basic

@[expose] public section

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Formalism.GaloisIrreducibility (IsOrbit)

theorem frobenius_orbit_irreducible : FrobOrbitIrred := by
  unfold FrobOrbitIrred IsOrbit
  intro K L _ _ _ _ _ f hm hirr
  classical
  have hf0 : f ≠ 0 := hm.ne_zero
  have hfL : f.map (algebraMap K L) ≠ 0 := Polynomial.map_ne_zero hf0
  have hmem : ∀ z : L, z ∈ (f.aroots L).toFinset ↔ aeval z f = 0 := by
    intro z
    rw [Multiset.mem_toFinset, mem_aroots]
    exact ⟨fun h => h.2, fun h => ⟨hf0, h⟩⟩
  have hfrob : ∀ z : L, aeval (z ^ Fintype.card K) f = (aeval z f) ^ Fintype.card K := by
    intro z
    rw [← expand_aeval, FiniteField.expand_card, map_pow]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x hx
    rw [hmem] at hx ⊢
    show aeval (x ^ Fintype.card K) f = 0
    rw [hfrob, hx, zero_pow Fintype.card_ne_zero]
  · intro x hx y hy
    rw [hmem] at hx hy
    let E : IntermediateField K L := IntermediateField.adjoin K (f.rootSet L)
    have hxE : x ∈ E := IntermediateField.subset_adjoin K _ ((mem_rootSet_of_ne hf0).2 hx)
    have hyE : y ∈ E := IntermediateField.subset_adjoin K _ ((mem_rootSet_of_ne hf0).2 hy)
    haveI hSF : IsSplittingField K E f :=
      IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
    haveI : Normal K E := Normal.of_isSplittingField f
    haveI : FiniteDimensional K E := IsSplittingField.finiteDimensional E f
    haveI : Finite E := Module.finite_of_finite K
    haveI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    have hmx : minpoly K x = f := (minpoly.eq_of_irreducible_of_monic hirr hx hm).symm
    have hmy : minpoly K y = f := (minpoly.eq_of_irreducible_of_monic hirr hy hm).symm
    have hxy : minpoly K (⟨y, hyE⟩ : E) = minpoly K (⟨x, hxE⟩ : E) := by
      rw [IntermediateField.minpoly_eq, IntermediateField.minpoly_eq]
      show minpoly K y = minpoly K x
      rw [hmx, hmy]
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit E).1 hxy
    obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K E).2 σ
    have key : ∀ (m : ℕ) (w : E), (((FiniteField.frobeniusAlgEquivOfAlgebraic K E ^ m) w : E) : L) =
        (fun z : L => z ^ Fintype.card K)^[m] (w : L) := by
      intro m
      induction m with
      | zero => intro w; rfl
      | succ m ih =>
        intro w
        rw [pow_succ, AlgEquiv.mul_apply, ih, Function.iterate_succ_apply]
        congr 1
        all_goals (try rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic])
        all_goals (try simp)
    simp only at hσ
    have h2 : ((σ ⟨x, hxE⟩ : E) : L) = y := by
      rw [← AlgEquiv.smul_def, hσ]
    simp only at hn
    rw [← hn, key] at h2
    exact ⟨_, h2⟩
  · have hsep : f.Separable := by
      first
      | exact PerfectField.separable_of_irreducible hirr
      | (haveI : PerfectField K := PerfectField.ofFinite
         exact PerfectField.separable_of_irreducible hirr)
    rw [Multiset.toFinset_card_of_nodup (nodup_roots (hsep.map (f := algebraMap K L)))]
    show Multiset.card (f.map (algebraMap K L)).roots = f.natDegree
    rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
