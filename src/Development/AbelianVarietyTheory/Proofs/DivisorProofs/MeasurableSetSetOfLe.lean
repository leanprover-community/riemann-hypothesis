module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorUniformizerExponent
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Generic
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem apow_zpow (x : kˣ) (n : ℤ) (z : ℂ) : apow (x ^ n) z = apow x (n * z) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [_root_.zpow_add_one, apow_mul, ih, ← apow_add]; push_cast; ring_nf
  | pred n ih =>
    rw [_root_.zpow_sub_one, apow_mul, ih, apow_inv, ← apow_add]; push_cast; ring_nf

theorem prod_apow_list (ϖ : kˣ) {α : Type*} (l : List α) (f : α → ℂ) :
    (l.map fun b => apow ϖ (f b)).prod = apow ϖ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons b l ih => rw [List.map_cons, List.prod_cons, ih, ← apow_add]; simp

theorem prod_apow_finset (ϖ : kˣ) {α : Type*} (s : Finset α) (f : α → ℂ) :
    ∏ i ∈ s, apow ϖ (f i) = apow ϖ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, ← apow_add]

end Generic
end GlobalTheory.OriginBox

namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Vol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem setOf_le_eq_preimage (u : kˣ) :
    {x : k | valuation k x ≤ valuation k (u : k)} = (fun x => ((u⁻¹ : kˣ) : k) * x) ⁻¹' (𝒪[k] : Set k) := by
  ext x
  have h0 : 0 < valuation k (u : k) := zero_lt_iff.2 (by simp)
  simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff, map_mul,
    Units.val_inv_eq_inv_val, map_inv₀]
  rw [inv_mul_le_one₀ h0]

variable [MeasurableSpace k] [BorelSpace k]

theorem measurableSet_setOf_le (u : kˣ) : MeasurableSet {x : k | valuation k x ≤ valuation k (u : k)} := by
  rw [setOf_le_eq_preimage]
  exact (Model.isOpen_int.preimage (continuous_const.mul continuous_id)).measurableSet

theorem vol_setOf_le (ν : Measure k) (hν : IsUnitVol ν) (u : kˣ) :
    ν {x : k | valuation k x ≤ valuation k (u : k)} = ENNReal.ofReal (nabs k u) := by
  rw [← Model.nabs_vol ν hν u, setOf_le_eq_preimage]
  congr 1
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  rfl

theorem measurableSet_box (G : Grid k) (ϖ : kˣ) (a a' : ℤ) : MeasurableSet (box G ϖ a a') :=
  MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_setOf_le _

open Classical in
theorem vol_box (G : Grid k) (ν : Measure k) (hν : IsUnitVol ν) (ϖ : kˣ) (a a' : ℤ) :
    (varsVol G ν (box G ϖ a a')).toReal = ∏ j, ∏ v, nabs k (ϖ ^ boxExp G a a' j v) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have := hν.1
  rw [varsVol, box, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [vol_setOf_le ν hν, ENNReal.toReal_ofReal (Model.nabs_pos _).le]

end Vol
end GlobalTheory.OriginBox

namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Expo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prod_zpow_units {α : Type*} (ϖ : kˣ) (s : Finset α) (f : α → ℤ) : ∏ i ∈ s, ϖ ^ f i = ϖ ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, _root_.zpow_add]

variable (G : Grid k)

def vtxDet (a a' : ℤ) (X : ℕ × ℕ) : ℤ :=
  if X.1 = G.m then ∑ x : Fin (G.rank (G.m, X.2)), vtxExp a a' (G.m - 1 - X.2) (topRank G X.2) x else 0


open Classical in
def expo (a a' : ℤ) : ℤ :=
  ((oppositePath G.m).map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum -
    2 * ∑ j, ∑ v, boxExp G a a' j v

variable {G}

theorem gdet_eq (ϖ : kˣ) (a a' : ℤ) (g : G.VertexGroup) (hg : ∀ j, g (G.m, j) = colDiag G ϖ a a' j)
    (hg' : ∀ i j, i ≠ G.m → g (i, j) = 1) (X : ℕ × ℕ) : gdet (g X) = ϖ ^ vtxDet G a a' X := by
  obtain ⟨i, j⟩ := X
  by_cases hi : i = G.m
  · rw [show (i, j) = (G.m, j) by rw [hi], hg, vtxDet, if_pos rfl, colDiag, gdet, det_diagGL, prod_zpow_units]
  · rw [hg' i j hi, vtxDet, if_neg hi]
    simp

end Expo
end GlobalTheory.OriginBox
