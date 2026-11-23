module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisReg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.LineOfNotIrr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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

@[expose] public section

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Sd

private theorem irr_of_le {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) {H H' : Subgroup Γ}
    (h : H ≤ H') (hi : IsIrr (ρ.comp H.subtype)) : IsIrr (ρ.comp H'.subtype) := by
  exact ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun W hW hI => hi.2.2 W hW fun g v hv => hI ⟨g, h g.2⟩ v hv⟩

private theorem norm_one_of_fin {l : ℕ} [Fact l.Prime] (a : (Qbar l)ˣ) (ha : IsOfFinOrder a) : ‖(a : Qbar l)‖ = 1 := by
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 ha
  have h1 : ‖(a : Qbar l)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1

private theorem norm_cyc (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (s : G F Ω) :
    ‖(cycBar F Ω l s : Qbar l)‖ = 1 := by
  have h : (cycBar F Ω l s : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((ReciprocityTheory.Gal.cycZ F Ω l s : ℤ_[l]) : ℚ_[l]) := rfl
  rw [h, norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]
  exact PadicInt.norm_units _

theorem UpperTheory.V.Sd.sI :
    UpperTheory.V.Sd.SI := by
  intro l _ hl Ω _ _ _ ι φ θ k hk hφ ρ hρ
  have hn : ∀ s, ‖(((cycBar ℚ Ω l ^ (k - 1) * φ) s : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
    intro s
    have h1 : IsOfFinOrder (φ s) := by
      obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hφ
      exact isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, by rw [← MonoidHom.pow_apply, h, MonoidHom.one_apply]⟩
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow,
      norm_cyc, norm_one_of_fin _ h1, one_pow, one_mul]
  have key : ∀ H : Subgroup (G ℚ Ω), IsOpen (H : Set (G ℚ Ω)) → H.Normal → ¬ IsIrr (ρ.comp H.subtype) →
      (∀ s ∈ H, Cong ((cycBar ℚ Ω l ^ (k - 1) * φ) s) 1) ∧ ∀ s, Cong ((cycBar ℚ Ω l ^ (k - 1) * φ) s ^ 2) 1 := by
    intro H hH hN hI
    refine sIabs l hl _ ρ _ hn hρ.irr hρ.res H hN ?_ hI
    obtain ⟨s, hs, a, ha, hc⟩ := eisReg l Ω ι φ θ k hk ρ hρ H hH
    refine ⟨s, hs, ?_⟩
    have ha1 : (a : Qbar l) ≠ 1 := by
      intro h
      have : a = 1 := Units.ext h
      exact ha (this ▸ IsOfFinOrder.one)
    rw [hc]
    exact separable_X_sub_C.mul separable_X_sub_C
      (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 ha1).isUnit)
  refine ⟨fun H hH hN ⟨s, hs, hc⟩ => ?_, fun ⟨s, hc⟩ H hH => ?_⟩
  · by_contra hI
    exact hc ((key H hH hN hI).1 s hs)
  · haveI : IsGalois ℚ Ω := ⟨⟩
    haveI : Finite (G ℚ Ω ⧸ H) := H.quotient_finite_of_isOpen hH
    haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hO : IsOpen (H.normalCore : Set (G ℚ Ω)) :=
      Subgroup.isOpen_of_isClosed_of_finiteIndex _ (H.normalCore_isClosed (H.isClosed_of_isOpen hH))
    refine irr_of_le ρ H.normalCore_le ?_
    by_contra hI
    exact hc ((key _ hO inferInstance hI).2 s)
