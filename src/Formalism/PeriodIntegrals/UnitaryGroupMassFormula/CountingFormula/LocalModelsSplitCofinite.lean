module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def GoodAt {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (L : LocSp D M)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : D.host.E) (Z : MatZ D) (p : PlF D) : Prop :=
  (M p).split = none ∧ (L.H p).IsSelfDual (lattice₂ L p (VS D).L0) ∧
    (∀ a b, GaPlus M δ p T T' Z a b ∈ (M p).L.O) ∧
    ∃ y ∈ (M p).L.O, (GaPlus M δ p T T' Z).det * y = 1

def DensAtGood : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ →
      ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
        ∀ (Z : MatZ D) (p : PlF D), GoodAt L δ (Tn u) (Tn u') Z p →
          ∃ η : ℝ, (η = 1 ∨ η = -1) ∧
            densP L δ ϖ (Tn u) (Tn u') Z p =
              Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[(D.s.atP p).Fp]) η D.R.r (2 * (D.R.rS + 1)) 0

def ResCard : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : PlF D), Nat.card 𝓀[(D.s.atP p).Fp] = p.asIdeal.absNorm

def ModeLCofinite : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ᶠ p in Filter.cofinite, (M p).split = none

theorem resChar_finite (D : Formalism.BasicNotions.D7) (ℓ : ℕ) : {p : PlF D | Loc.resChar p = ℓ}.Finite := by
  have hsub : {p : PlF D | Loc.resChar p = ℓ} ⊆
      {v | v.asIdeal ∣ Ideal.span {(ℓ : 𝓞 D.host.F)}} := by
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [Ideal.dvd_span_singleton, ← hp, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  by_cases hℓ : ℓ = 0
  · subst hℓ
    have hempty : {p : PlF D | Loc.resChar p = 0} = ∅ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hp
      have h1 : ((Ideal.absNorm p.asIdeal : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.absNorm_mem p.asIdeal
      have hc : CharP (𝓞 D.host.F ⧸ p.asIdeal) 0 := by
        have h2 := ringChar.charP (𝓞 D.host.F ⧸ p.asIdeal)
        unfold Loc.resChar at hp
        rwa [hp] at h2
      rw [CharP.cast_eq_zero_iff _ 0, zero_dvd_iff, Ideal.absNorm_eq_zero_iff] at h1
      exact p.ne_bot h1
    rw [hempty]
    exact Set.finite_empty
  · refine (Ideal.finite_factors ?_).subset hsub
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hℓ

theorem local_models_split_cofinite : ModeLCofinite := by
  intro D δ M hA
  have hfin : {p : PlF D | Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)}.Finite := by
    have he : {p : PlF D | Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)} =
        {p | Loc.resChar p = D.host.g 0} ∪ {p | Loc.resChar p = D.host.g 1} := by
      ext p
      simp
    rw [he]
    exact (resChar_finite D _).union (resChar_finite D _)
  rw [Filter.eventually_cofinite]
  refine hfin.subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [← D.s_split p]
  have hAp := (hA p).2.2.2.2.2
  cases hM : (M p).split with
  | none => exact absurd hM hp
  | some g =>
    cases hS : (D.s.atP p).split with
    | none =>
      rw [hM, hS] at hAp
      exact hAp.elim
    | some sg => rfl

end PI.UnitaryGroupMassFormula.CntFormula
