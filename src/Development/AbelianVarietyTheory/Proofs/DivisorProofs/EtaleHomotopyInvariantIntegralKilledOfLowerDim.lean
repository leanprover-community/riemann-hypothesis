module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInvOfDirectedUnionStatement
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
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

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

private theorem ringKrullDim_le_quotient_of_algebraMap_eq_zero (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (s : R) (hs : algebraMap R S s = 0) :
    ringKrullDim S ≤ ringKrullDim (R ⧸ Ideal.span {s}) := by
  rw [ringKrullDim_quotient]
  have hmem : ∀ P : PrimeSpectrum S, (⟨P.asIdeal.comap (algebraMap R S), inferInstance⟩ : PrimeSpectrum R) ∈
      PrimeSpectrum.zeroLocus (R := R) (Ideal.span {s}) := fun P => by
    simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le,
      Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hs, Ideal.zero_mem]
  exact Order.krullDim_le_of_strictMono (fun P => ⟨_, hmem P⟩)
    (fun P Q h => Subtype.mk_lt_mk.mpr (Ideal.IsIntegral.comap_lt_comap (R := R) h))

private theorem hInv_adjoin_of_dim_quotient_lt (q : ℕ) [NeZero q] (d : ℕ)
    (hlow : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R)
    (D : Type) [CommRing D] [Algebra.FiniteType ℤ D] (hqD : IsUnit (q : D)) (E : Type) [CommRing E]
    [Algebra D E] [Algebra.IsIntegral D E] (s : D) (hsE : algebraMap D E s = 0)
    (hlt : ringKrullDim (D ⧸ Ideal.span {s}) < d) (F : Finset E) :
    HInv q ((Algebra.adjoin D (F : Set E)).restrictScalars ℤ) := by
  set T := Algebra.adjoin D (F : Set E)
  have : Algebra.IsIntegral D T := ⟨fun x =>
    (isIntegral_algHom_iff T.val Subtype.val_injective).mp (Algebra.IsIntegral.isIntegral (x : E))⟩
  have : Algebra.FiniteType D T := (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset F)
  have : Algebra.FiniteType ℤ T := Algebra.FiniteType.trans (R := ℤ) (S := D) inferInstance inferInstance
  have hsT : algebraMap D T s = 0 := Subtype.ext (by simpa using hsE)
  have h1 : ringKrullDim T < d := (ringKrullDim_le_quotient_of_algebraMap_eq_zero D T s hsT).trans_lt hlt
  have h2 : IsUnit (q : T) := by simpa using hqD.map (algebraMap D T)
  exact hlow T h2 h1



theorem GlobalTheory.hInv_of_integral_killed_of_lower : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ (E : Type) [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (s : D), s ≠ 0 → algebraMap D E s = 0 → HInv q E := by
  intro q _ d hlow D _ _ _ hqD hdD E _ _ _ s hs0 hsE
  have hquot := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hs0)
  have hlt : ringKrullDim (D ⧸ Ideal.span {s}) < d := by
    have h := hquot.trans hdD
    generalize ringKrullDim (D ⧸ Ideal.span {s}) = a at h ⊢
    cases a using WithBot.recBotCoe with
    | bot => exact WithBot.bot_lt_coe _
    | coe a =>
      have h' : a + 1 ≤ (d : ℕ∞) := by exact_mod_cast h
      have ha : a ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) (le_trans le_self_add h')
      exact_mod_cast (ENat.add_one_le_iff ha).mp h'
  exact GlobalTheory.T.hInv_of_directed_union_subalgebras q E (Finset E) (fun F => (Algebra.adjoin D (F : Set E)).restrictScalars ℤ)
    (fun F G h x hx => Algebra.adjoin_mono (Finset.coe_subset.mpr h) hx)
    (fun a => ⟨{a}, Algebra.subset_adjoin (by simp)⟩)
    (fun F => by
      have h := hqD.map (algebraMap D (Algebra.adjoin D (F : Set E)))
      rw [map_natCast] at h
      exact h)
    (fun F => hInv_adjoin_of_dim_quotient_lt q d hlow D hqD E s hsE hlt F)
