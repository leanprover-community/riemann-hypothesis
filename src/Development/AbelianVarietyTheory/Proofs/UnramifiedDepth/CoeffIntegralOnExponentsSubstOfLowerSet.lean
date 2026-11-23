module

public import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
public import Mathlib.RingTheory.MvPowerSeries.Substitution
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Formalism.IncomingBounds.IncomingBound

@[expose] public section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.LowerSubst

open MvPowerSeries

variable {C : Type} [Field C] (V : VF C) {σ : Type} (P : (σ →₀ ℕ) → Prop)

def IntOn (g : MvPowerSeries σ C) : Prop := ∀ μ, P μ → V.Ge 0 (coeff μ g)

theorem intOn_one : IntOn V P (1 : MvPowerSeries σ C) := by
  intro α _
  rw [coeff_one]
  split_ifs with h
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem intOn_mul (hP : ∀ μ ν, ν ≤ μ → P μ → P ν) {f g : MvPowerSeries σ C}
    (hf : IntOn V P f) (hg : IntOn V P g) : IntOn V P (f * g) := by
  intro α hα
  rw [coeff_mul]
  refine VF.Ge.sum fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  exact VF.Ge.mul_int (hf _ (hP α _ (hx ▸ le_self_add) hα)) (hg _ (hP α _ (hx ▸ le_add_self) hα))

theorem intOn_prod (hP : ∀ μ ν, ν ≤ μ → P μ → P ν) {ι : Type*} (s : Finset ι)
    (f : ι → MvPowerSeries σ C) (h : ∀ i ∈ s, IntOn V P (f i)) : IntOn V P (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IntOn V P) (fun _ _ => intOn_mul V P hP) (intOn_one V P) h

theorem intOn_pow (hP : ∀ μ ν, ν ≤ μ → P μ → P ν) {f : MvPowerSeries σ C} (hf : IntOn V P f)
    (n : ℕ) : IntOn V P (f ^ n) := by
  induction n with
  | zero => simpa using intOn_one V P
  | succ n ih => rw [pow_succ]; exact intOn_mul V P hP ih hf

theorem subst_int_on_lower :
    ∀ (C : Type) [Field C] (V : VF C) (σ τ : Type) [Fintype σ] [Fintype τ] (P : (σ →₀ ℕ) → Prop), (∀ μ ν, ν ≤ μ → P μ → P ν) → ∀ (γ : MvPowerSeries τ C) (T : τ → MvPowerSeries σ C), (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) → (∀ w, MvPowerSeries.constantCoeff (T w) = 0) → (∀ w μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (T w))) → ∀ μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.subst T γ)) := by
  intro C _ V σ τ _ _ P hP γ T hγ hT0 hT α hα
  have hs : HasSubst T := hasSubst_of_constantCoeff_zero hT0
  rw [coeff_subst hs, finsum_eq_sum _ (coeff_subst_finite hs γ α)]
  refine VF.Ge.sum fun β _ => ?_
  have hp : IntOn V P (β.prod fun s e => T s ^ e) :=
    intOn_prod V P hP _ _ fun s _ => intOn_pow V P hP (hT s) (β s)
  rw [smul_eq_mul]
  exact VF.Ge.mul_int (hγ β) (hp α hα)

end GlobalTheory.LowerSubst
