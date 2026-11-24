module

import Development.WeilBound.CoreStatements.ThetaDilations.IsOpenCoset
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace CompanionTheory.PlacePermOperatorBicommutantSpan

open GlobalTheory.CompanionTheory.SW.Core

variable {V : Type} [AddCommGroup V] [TopologicalSpace V]

def CO (L : AddSubgroup V) : Prop := IsCompact (L : Set V) ∧ IsOpen (L : Set V)

def ind (a : V) (L : AddSubgroup V) : V → ℂ := Set.indicator {x | x - a ∈ L} fun _ => (1 : ℂ)

omit [TopologicalSpace V] in
theorem ind_of_mem {a x : V} {L : AddSubgroup V} (h : x - a ∈ L) : ind a L x = 1 := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.ind_of_mem <;> assumption

omit [TopologicalSpace V] in
theorem ind_of_not {a x : V} {L : AddSubgroup V} (h : x - a ∉ L) : ind a L x = 0 := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.ind_of_not <;> assumption

omit [TopologicalSpace V] in
theorem ind_congr {a b x y : V} {L L' : AddSubgroup V} (h : x - a ∈ L ↔ y - b ∈ L') : ind a L x = ind b L' y := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.ind_congr <;> assumption

omit [TopologicalSpace V] in
theorem ind_add {a l : V} {L : AddSubgroup V} (x : V) (hl : l ∈ L) : ind a L (x + l) = ind a L x := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.ind_add <;> assumption

section top

variable [IsTopologicalAddGroup V]

theorem CO.sup {L L' : AddSubgroup V} (h : CO L) (h' : CO L') : CO (L ⊔ L') := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.CO.sup <;> assumption

theorem CO.inf {L L' : AddSubgroup V} (h : CO L) (h' : IsOpen (L' : Set V)) : CO (L ⊓ L') := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.CO.inf <;> assumption

theorem isOpen_coset (a : V) {L : AddSubgroup V} (h : IsOpen (L : Set V)) : IsOpen {x | x - a ∈ L} := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.isOpen_coset <;> assumption

theorem lc_of_inv {f : V → ℂ} {L : AddSubgroup V} (h : IsOpen (L : Set V)) (hf : ∀ x, ∀ l ∈ L, f (x + l) = f x) :
    IsLocallyConstant f := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.lc_of_inv <;> assumption

theorem sb_ind [T2Space V] (a : V) {L : AddSubgroup V} (h : CO L) : SB (ind a L) := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.sb_ind <;> assumption

end top

omit [AddCommGroup V] in
theorem sb_add {f g : V → ℂ} (hf : SB f) (hg : SB g) : SB (f + g) := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.sb_add <;> assumption

omit [AddCommGroup V] in
theorem sb_mul {f g : V → ℂ} (hf : IsLocallyConstant f) (hg : SB g) : SB fun x => f x * g x := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.sb_mul <;> assumption

omit [AddCommGroup V] in
theorem sb_smul (c : ℂ) {g : V → ℂ} (hg : SB g) : SB (c • g) := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.sb_smul <;> assumption

omit [AddCommGroup V] in
theorem sb_zero : SB (0 : V → ℂ) := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.sb_zero <;> assumption

omit [AddCommGroup V] in
theorem sb_sum {α : Type} (s : Finset α) {f : α → V → ℂ} (h : ∀ a ∈ s, SB (f a)) : SB (∑ a ∈ s, f a) := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.sb_sum <;> assumption

omit [AddCommGroup V] in
theorem sb_homeo {f : V → ℂ} (hf : SB f) (e : V ≃ₜ V) : SB (f ∘ e) := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.sb_homeo <;> assumption

theorem sb_span [IsTopologicalAddGroup V] {φ : V → ℂ} (hφ : SB φ) {L : AddSubgroup V} (hL : IsOpen (L : Set V))
    (hinv : ∀ x, ∀ l ∈ L, φ (x + l) = φ x) : ∃ s : Finset V, φ = ∑ a ∈ s, φ a • ind a L := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.sb_span <;> assumption

variable [MeasurableSpace V] {χ : V → V → ℂ} {μ : Measure V}

theorem co_cpt (h : NADual V χ μ) {K : Set V} (hK : IsCompact K) : ∃ L : AddSubgroup V, CO L ∧ K ⊆ L := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.co_cpt <;> assumption

theorem sb_level (h : NADual V χ μ) {φ : V → ℂ} (hφ : SB φ) :
    ∃ L L' : AddSubgroup V, CO L ∧ CO L' ∧ L' ≤ L ∧ (∀ x, x ∉ L → φ x = 0) ∧ ∀ x, ∀ l ∈ L', φ (x + l) = φ x := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.sb_level <;> assumption

section chi

variable (h : NADual V χ μ)
include h

theorem chi_sym (x y : V) : χ x y = χ y x := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.chi_sym <;> assumption
theorem chi_norm (x y : V) : ‖χ x y‖ = 1 := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.chi_norm <;> assumption
theorem chi_add (x x' y : V) : χ (x + x') y = χ x y * χ x' y := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.chi_add <;> assumption
theorem chi_cont : Continuous fun p : V × V => χ p.1 p.2 := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.chi_cont <;> assumption
theorem chi_ne (x y : V) : χ x y ≠ 0 := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.chi_ne <;> assumption
theorem chi_add' (x y y' : V) : χ x (y + y') = χ x y * χ x y' := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.chi_add' <;> assumption
theorem chi_zero (y : V) : χ 0 y = 1 := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.chi_zero <;> assumption
theorem chi_neg (x y : V) : χ (-x) y = conj (χ x y) := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.chi_neg <;> assumption

def perpG (L : AddSubgroup V) : AddSubgroup V where
  carrier := perp χ L
  zero_mem' := fun x _ => by rw [chi_sym h, chi_zero h]
  add_mem' := fun ha hb x hx => by rw [chi_add' h, ha x hx, hb x hx, one_mul]
  neg_mem' := fun {y} hy x hx => by rw [chi_sym h, chi_neg h, chi_sym h, hy x hx, map_one]

theorem co_perp {L : AddSubgroup V} (hL : CO L) : CO (perpG h L) := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.co_perp <;> assumption

theorem perp_perp {L : AddSubgroup V} (hL : CO L) (x : V) : x ∈ perpG h (perpG h L) ↔ x ∈ L := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.perp_perp <;> assumption

theorem meas_perp {L : AddSubgroup V} (hL : CO L) : (μ L).toReal * (μ (perpG h L)).toReal = 1 := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.meas_perp <;> assumption

theorem chi_lc (a : V) : IsLocallyConstant fun y => χ a y := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.chi_lc <;> assumption

theorem sb_int {φ : V → ℂ} (hφ : SB φ) : Integrable φ μ := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.sb_int <;> assumption

theorem sb_chi {φ : V → ℂ} (hφ : SB φ) (y : V) : SB fun x => φ x * χ x y := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.sb_chi <;> assumption

theorem fou_add {f g : V → ℂ} (hf : SB f) (hg : SB g) : fou χ μ (f + g) = fou χ μ f + fou χ μ g := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.fou_add <;> assumption

omit h in
theorem fou_smul (c : ℂ) (f : V → ℂ) : fou χ μ (c • f) = c • fou χ μ f := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.fou_smul <;> assumption

omit h [AddCommGroup V] [MeasurableSpace V] in
theorem map_sum_sb {T : (V → ℂ) → (V → ℂ)} (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsm : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ) {α : Type} (s : Finset α) (c : α → ℂ) {f : α → V → ℂ}
    (hf : ∀ a, SB (f a)) : T (∑ a ∈ s, c a • f a) = ∑ a ∈ s, c a • T (f a) := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.map_sum_sb <;> assumption

theorem fou_ind {L : AddSubgroup V} (hL : CO L) (a y : V) :
    fou χ μ (ind a L) y = ((μ L).toReal : ℂ) * χ a y * ind 0 (perpG h L) y := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.fou_ind <;> assumption

theorem fou_sb {φ : V → ℂ} (hφ : SB φ) : SB (fou χ μ φ) ∧ ∀ x, fou χ μ (fou χ μ φ) x = φ (-x) := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.fou_sb <;> assumption

theorem planch {φ : V → ℂ} (hφ : SB φ) : ∫ y, ‖fou χ μ φ y‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.planch <;> assumption

theorem schur {T : (V → ℂ) → (V → ℂ)} (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsm : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ)
    (hch : ∀ y φ, SB φ → T (fun u => χ u y * φ u) = fun u => χ u y * T φ u)
    (htr : ∀ x φ, SB φ → T (fun u => φ (u + x)) = fun u => T φ (u + x)) : ∃ c : ℂ, ∀ φ, SB φ → T φ = c • φ := by
  apply PositivityTheory.PlacePermOperatorBicommutantSpan.schur <;> assumption

end chi

end CompanionTheory.PlacePermOperatorBicommutantSpan
