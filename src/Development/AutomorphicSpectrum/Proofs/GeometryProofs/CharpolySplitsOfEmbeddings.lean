module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
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

@[expose] public section

open Polynomial NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

theorem map_charpoly_lmul_eq_prod_embeddings (E : Type) [Field E] [NumberField E]
    (Ω : Type) [Field Ω] [Fintype (E →+* Ω)]
    (hc : Nat.card (E →+* Ω) = Module.finrank ℚ E) (a : 𝓞 E) :
    (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom Ω) =
      ∏ s : E →+* Ω, (X - C (s (a : E))) := by
  classical
  let e := NumberField.RingOfIntegers.basis E
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card (E →+* Ω) := by
    rw [← Module.finrank_eq_card_basis e, NumberField.RingOfIntegers.rank, ← hc,
      Nat.card_eq_fintype_card]
  let eqv := Fintype.equivOfCardEq hcard
  let P : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E →ₐ[ℤ] Ω :=
    fun j => ((eqv j).comp (algebraMap (𝓞 E) E)).toIntAlgHom
  have hP : Function.Injective P := by
    intro i j hij
    apply eqv.injective
    apply IsFractionRing.injective_comp_algebraMap (A := 𝓞 E) (K := E) (L := Ω)
    show (eqv i).comp (algebraMap (𝓞 E) E) = (eqv j).comp (algebraMap (𝓞 E) E)
    ext x
    exact DFunLike.congr_fun hij x
  have h := GlobalTheory.map_charpoly_leftMulMatrix_eq_prod_algHom e hP a
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, algebraMap_int_eq] at h
  refine h.trans ?_
  exact Fintype.prod_equiv eqv _ _ fun j => rfl

theorem charpoly_lmul_splits_of_conjugates (E : Type) [Field E] [NumberField E]
    (Ω : Type) [Field Ω] [CharZero Ω] (O : Type) [CommRing O] [Algebra O Ω]
    (K : Type) [Field K] (g : O →+* K) (hinj : Function.Injective (algebraMap O Ω))
    (hc : Nat.card (E →+* Ω) = Module.finrank ℚ E)
    (hO : ∀ (s' : E →+* Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap O Ω).range) (a : 𝓞 E) :
    ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K)).Splits := by
  classical
  haveI : Finite (E →+* Ω) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Module.finrank_pos.ne')
  letI : Fintype (E →+* Ω) := Fintype.ofFinite _
  have hO' : ∀ (s' : E →+* Ω) (a : 𝓞 E), ∃ y, algebraMap O Ω y = s' (a : E) :=
    fun s' a => RingHom.mem_range.mp (hO s' a)
  choose o ho using hO'
  have hΩ := GlobalTheory.CompanionTheory.Ar.Flat.DegZ.map_charpoly_lmul_eq_prod_embeddings E Ω hc a
  have hO2 : (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom O) =
      ∏ s : E →+* Ω, (X - C (o s a)) := by
    apply Polynomial.map_injective (algebraMap O Ω) hinj
    rw [Polynomial.map_map,
      RingHom.ext_int ((algebraMap O Ω).comp (Int.castRingHom O)) (Int.castRingHom Ω), hΩ,
      Polynomial.map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, ho]
  have hK : (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K) =
      ∏ s : E →+* Ω, (X - C (g (o s a))) := by
    rw [RingHom.ext_int (Int.castRingHom K) (g.comp (Int.castRingHom O)), ← Polynomial.map_map, hO2,
      Polynomial.map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [hK]
  exact Polynomial.Splits.prod fun s _ => Polynomial.Splits.X_sub_C _

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ
