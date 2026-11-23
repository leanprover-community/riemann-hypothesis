module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TargetAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.IrrConj

theorem isIrrSub_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ}
    (H H' : Subgroup Γ) (hH : ∀ s, s ∈ H → s ∈ H')
    (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k) (hg : ∀ s, r' s = g * r s * g⁻¹)
    (hr : IsIrrSub (r.comp H.subtype) ⊤) : IsIrrSub (r'.comp H'.subtype) ⊤ := by
  first
  | exact @_root_.GlobalTheory.ConjugateIrreducibility.target
  | exact _root_.GlobalTheory.ConjugateIrreducibility.target
  | (apply _root_.GlobalTheory.ConjugateIrreducibility.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateIrreducibility.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateIrreducibility.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateIrreducibility.target ..)

theorem dt_eq_of_repIso {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
    (W W' : R2 Ω l) (g : GL (Fin 2) (Qbar l)) (hg : ∀ s, W' s = g * W s * g⁻¹) (s : G ℚ Ω) :
    dt W' s = dt W s := by
  simp only [dt, MonoidHom.comp_apply, hg s, map_mul, map_inv]
  rw [mul_comm (Matrix.GeneralLinearGroup.det g), mul_assoc, mul_inv_cancel, mul_one]

theorem irr_of_repIso : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] (W W' : R2 Ω l),
    RepIso W W' → IsIrr (W.comp (H0g W).subtype) → IsIrr (W'.comp (H0g W').subtype) := by
  intro Ω _ _ l _ W W' ⟨g, hg⟩ h
  refine isIrrSub_conj (H0g W) (H0g W') ?_ W W' g hg h
  intro s hs
  simp only [H0g, Subgroup.mem_inf, MonoidHom.mem_ker] at hs ⊢
  exact ⟨hs.1, by rw [dt_eq_of_repIso W W' g hg]; exact hs.2⟩

end GlobalTheory.IrrConj
