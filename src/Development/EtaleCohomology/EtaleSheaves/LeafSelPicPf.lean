module

public import Development.EtaleCohomology.EtaleSheaves.LeafPicCut
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

noncomputable section
open nonZeroDivisors IsDedekindDomain

namespace LateralTheory.E.LeafSelPicPf
open LateralTheory.E.LeafPicCut

lemma units_torsionFree {B : Type} [CommRing B] [IsDedekindDomain B] {q : ℕ} (hq : q ≠ 0)
    (x : (FractionalIdeal B⁰ (FractionRing B))ˣ) (h : x ^ q = 1) : x = 1 := by
  have hx0 : (x : FractionalIdeal B⁰ (FractionRing B)) ≠ 0 := x.ne_zero
  have hc : ∀ v : HeightOneSpectrum B,
      FractionalIdeal.count (FractionRing B) v (x : FractionalIdeal B⁰ (FractionRing B)) = 0 := by
    intro v
    have h1 := FractionalIdeal.count_pow (FractionRing B) v q (x : FractionalIdeal B⁰ (FractionRing B))
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one, FractionalIdeal.count_one] at h1
    have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq
    exact (mul_eq_zero.mp h1.symm).resolve_left hq'
  ext1
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (FractionRing B) hx0]
  simp [hc]

lemma exists_rep {B : Type} [CommRing B] [IsDedekindDomain B] (q : ℕ) (c : ClassGroup B) (hc : c ^ q = 1) :
    ∃ (I : (FractionalIdeal B⁰ (FractionRing B))ˣ) (f : (FractionRing B)ˣ),
      ClassGroup.mk (FractionRing B) I = c ∧ toPrincipalIdeal B (FractionRing B) f = I ^ q := by
  revert hc
  refine ClassGroup.induction (R := B) (FractionRing B) (fun I hc => ?_) c
  · refine ⟨I, ?_⟩
    have h1 : ClassGroup.mk (FractionRing B) (I ^ q) = ClassGroup.mk (FractionRing B) 1 := by
      rw [map_pow, hc, map_one]
    obtain ⟨x, hx⟩ := ClassGroup.mk_eq_mk.mp h1
    refine ⟨x⁻¹, rfl, ?_⟩
    rw [map_inv, inv_eq_iff_mul_eq_one, mul_comm, hx]

theorem LeafSelPic_of : LeafSelPic := by
  intro B _ _ q _ hfin
  classical
  have hex := fun c : {c : ClassGroup B // c ^ q = 1} => exists_rep q c.1 c.2
  choose I f hI hf using hex
  have hsel : ∀ c, f c ∈ sel B q := fun c => by
    simp only [sel, Subgroup.mem_comap, MonoidHom.mem_range]
    exact ⟨I c, by rw [hf c]; rfl⟩
  let φ : {c : ClassGroup B // c ^ q = 1} → selQ B q := fun c => QuotientGroup.mk ⟨f c, hsel c⟩
  refine Finite.of_injective φ ?_
  intro c d hcd
  have h1 := QuotientGroup.eq.mp hcd
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range] at h1
  obtain ⟨u, hu⟩ := h1
  simp only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hu
  have hx : ((I c)⁻¹ * I d * (toPrincipalIdeal B (FractionRing B) u)⁻¹) ^ q = 1 := by
    rw [mul_pow, mul_pow, inv_pow, inv_pow, ← map_pow, hu, ← hf c, ← hf d, map_mul, map_inv]
    group
  have h2 := units_torsionFree (NeZero.ne q) _ hx
  apply Subtype.ext
  rw [← hI c, ← hI d]
  refine ClassGroup.mk_eq_mk.mpr ⟨u, ?_⟩
  rw [mul_inv_eq_one, inv_mul_eq_iff_eq_mul] at h2
  exact h2.symm

end LateralTheory.E.LeafSelPicPf
