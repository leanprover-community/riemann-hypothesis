module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPtHomApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexProd
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.TraceBlocks

theorem levOp_secM_apply_self : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G), Function.Injective ι → ∀ (ρ : Representation ℂ H V) (K K' : Subgroup G) (F : G → ℂ), (∀ k ∈ K', ∀ x, F (x * k) = F x) → {q : G ⧸ K' | F q.out ≠ 0}.Finite → ∀ x : G, Finite (ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G) → {h : H | F (x⁻¹ * ι h * x) ≠ 0}.Finite → ∀ v : V, levOp (rightReg ℂ G V) K K' F LinearMap.id (secM ι ρ K' x v) x = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ((stabCard ι K' x : ℂ))⁻¹ • ∑ᶠ h : H, F (x⁻¹ * ι h * x) • ρ h v := by
  intro G H V _ _ _ _ ι _ ρ K K' F hF hS x _ hT v
  have hout : ∀ y : G, F (y : G ⧸ K').out = F y := by
    intro y
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K' y
    rw [hk, hF _ k.2]
  have hcond : ∀ (q : G ⧸ K') (h : H),
      ((ι h * x)⁻¹ * (x * q.out) ∈ K') ↔ (((x⁻¹ * ι h * x : G) : G ⧸ K') = q) := by
    intro q h
    have e : (ι h * x)⁻¹ * (x * q.out) = (x⁻¹ * ι h * x)⁻¹ * q.out := by group
    rw [e]
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.symm
  have hreg : ∀ (g : G) (φ : G → V) (y : G), rightReg ℂ G V g φ y = φ (y * g) := fun _ _ _ => rfl
  have hsec : ∀ y, secM ι ρ K' x v y =
      ((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K' then ρ h else 0) v := fun _ => rfl
  rw [GlobalTheory.BCT.LevOpTmul.levOp_apply _ K K' F LinearMap.id hS.toFinset (fun q hq => by simpa using hq)]
  rw [finsum_eq_sum_of_support_subset (f := fun h : H => F (x⁻¹ * ι h * x) • ρ h v) (s := hT.toFinset) (fun h hh => by
    rw [Set.Finite.coe_toFinset]
    intro h0; exact hh (by simp only [h0, zero_smul]))]
  simp only [Pi.smul_apply, Finset.sum_apply, LinearMap.id_apply, hreg, hsec]
  congr 1
  have hin : ∀ q ∈ hS.toFinset, (∑ᶠ h : H, if (ι h * x)⁻¹ * (x * q.out) ∈ K' then ρ h else 0) =
      ∑ h ∈ hT.toFinset, if (((x⁻¹ * ι h * x : G) : G ⧸ K') = q) then ρ h else 0 := by
    intro q hq
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hq
    rw [finsum_eq_sum_of_support_subset (s := hT.toFinset)]
    · exact Finset.sum_congr rfl fun h _ => by simp only [hcond]
    · intro h hh
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hh
      obtain ⟨hc, _⟩ := hh
      rw [Set.Finite.coe_toFinset]
      show _ ≠ _
      rw [hcond] at hc
      rw [← hout, hc]; exact hq
  rw [Finset.sum_congr rfl fun q hq => by rw [hin q hq]]
  simp only [LinearMap.sum_apply, Finset.sum_apply, ite_apply, LinearMap.zero_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h hh => ?_
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hh
  have : ∀ q ∈ hS.toFinset, F q.out • ((stabCard ι K' x : ℂ))⁻¹ • (if (((x⁻¹ * ι h * x : G) : G ⧸ K') = q) then ρ h else 0) v
      = if (((x⁻¹ * ι h * x : G) : G ⧸ K') = q) then ((stabCard ι K' x : ℂ))⁻¹ • F (x⁻¹ * ι h * x) • ρ h v else 0 := by
    intro q _
    split_ifs with e
    · rw [← e, hout, smul_comm]
    · simp only [LinearMap.zero_apply, smul_zero]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
  rw [if_pos]
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hout]
  exact hh

end GlobalTheory.BCT.TraceBlocks
