module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassFunctionDegreeEqSumDerivativesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegreeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionTwoBlockCuspidalEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeFieldStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters

@[expose] public section

noncomputable section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.Generic

variable {g : ℕ} [Fact g.Prime]

theorem br_zero_self {d : ℕ} (M : Mt g d) : br 0 d M = M := by
  funext i j
  simp [br, entN, i.isLt, j.isLt]

theorem res_zero_self {d : ℕ} (χ : Gn g d → ℂ) (h : Gn g d) : res 0 d χ 1 h = χ h := by
  unfold res
  have hI : ∀ x : Gn g d, InPar 0 (x : Mt g d) := fun x i j hj _ => absurd hj (Nat.not_lt_zero _)
  have hT : ∀ x : Gn g d, tl 0 (x : Mt g d) = ((1 : Gn g 0) : Mt g 0) := fun x => by
    funext i; exact i.elim0
  simp only [hI, hT, br_zero_self, true_and, zero_mul, pow_zero, inv_one, one_mul, Units.val_inj]
  rw [Finset.sum_ite_eq']
  simp

theorem wh_zero_fun (ψ : AddChar (ZMod g) ℂ) (n : ℕ) : wh ψ (fun _ : Gn g n => (0 : ℂ)) = 0 := by
  simp [wh, tr]

theorem isClass_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, _, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

end GlobalTheory.GLq.Generic

theorem GlobalTheory.GLq.wh_cusp_pos : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ)
    (χ : Gn g d → ℂ), IsCusp χ → ∃ m : ℕ, 0 < m ∧ wh ψ χ = m := by
  intro g _ ψ hψ d χ hc
  have hc' := hc
  obtain ⟨hd, hirr, _⟩ := hc'
  have hder := GlobalTheory.T.classFunction_degree_eq_sum_derivatives g ψ hψ d χ hd (GlobalTheory.GLq.Generic.isClass_of_isIrr hirr)
  rw [Finset.sum_eq_single 0] at hder
  rotate_left
  · intro m hm hm0
    have hmd : m < d := Finset.mem_range.mp hm
    have hz : res m (d - m) χ 1 = fun _ => 0 := by
      funext y
      exact GlobalTheory.T.harishChandraRestrictionTwoBlock_cuspidal_eq_zero g d m χ hc (Nat.pos_of_ne_zero hm0) hmd 1 y
    have : der ψ m χ 1 = 0 := by
      show wh ψ (res m (d - m) χ 1) = 0
      rw [hz]
      exact GlobalTheory.GLq.Generic.wh_zero_fun ψ _
    rw [this, zero_mul]
  · intro h0
    exact absurd (Finset.mem_range.mpr hd) h0
  have h0 : der ψ 0 χ 1 = wh ψ χ := by
    change wh ψ (n := d) (res 0 d χ 1) = wh ψ χ
    congr 1
    funext h
    exact GlobalTheory.GLq.Generic.res_zero_self χ h
  rw [h0] at hder
  obtain ⟨V, _, hV⟩ := hirr
  have hchar : IsChar χ := ⟨V, hV⟩
  obtain ⟨d', hd'pos, hd'⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g d) (eU g d ψ) χ).2.1 ⟨V, ‹_›, hV⟩
  obtain ⟨n, hn⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g d) (eU g d ψ) χ).1 (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g d 0 0 ψ).1 hchar
  have hwh : wh ψ χ = n := hn
  refine ⟨n, Nat.pos_of_ne_zero ?_, hwh⟩
  rintro rfl
  rw [hwh, Nat.cast_zero, zero_mul, hd'] at hder
  exact absurd hder (by exact_mod_cast hd'pos.ne')
