module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelledCharactersEqAndCongrPrimeToPart
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.DC.TameGen

theorem part_pow {G : Type} [Monoid G] {l : ℕ} (hl : l.Prime) {x : G} (hx : IsOfFinOrder x) :
    ∃ a : ℕ, Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ a) = x ^ (l ^ a) := by
  apply GlobalTheory.ParamLabel.Congr.part_pow <;> assumption

theorem pow_eq_of_part_eq {G : Type} [Monoid G] {l : ℕ} (hl : l.Prime) {x y : G} (hx : IsOfFinOrder x)
    (hy : IsOfFinOrder y) (h : Formalism.CyclotomicNorms.primeToPart l x = Formalism.CyclotomicNorms.primeToPart l y) :
    ∃ a : ℕ, x ^ (l ^ a) = y ^ (l ^ a) := by
  obtain ⟨a, ha⟩ := part_pow hl hx
  obtain ⟨b, hb⟩ := part_pow hl hy
  refine ⟨a + b, ?_⟩
  have h1 : x ^ (l ^ (a + b)) = Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ (a + b)) := by
    rw [pow_add, pow_mul, pow_mul, ha]
  have h2 : y ^ (l ^ (a + b)) = Formalism.CyclotomicNorms.primeToPart l y ^ (l ^ (a + b)) := by
    rw [add_comm, pow_add, pow_mul, pow_mul, hb]
  rw [h1, h2, h]

def expo {m : ℕ} : Option (Fin m × Bool) → ℤ
  | none => 0
  | some (j, true) => (j.1 : ℤ) + 1
  | some (j, false) => -((j.1 : ℤ) + 1)

theorem expo_inj {m : ℕ} : Function.Injective (expo (m := m)) := by
  rintro (_ | ⟨i, _ | _⟩) (_ | ⟨j, _ | _⟩) h <;> simp only [expo] at h <;>
    first
    | rfl
    | (exfalso; omega)
    | (have : i = j := Fin.ext (by omega); rw [this])

theorem expo_bound {m : ℕ} (o : Option (Fin m × Bool)) : -(m : ℤ) ≤ expo o ∧ expo o ≤ m := by
  rcases o with (_ | ⟨i, _ | _⟩) <;> simp only [expo]
  · omega
  · have := i.2; omega
  · have := i.2; omega

theorem tameList_eq {g m : ℕ} (w : (ZMod g)ˣ) (o : Option (Fin m × Bool)) :
    DC.tameList (fun j : Fin m => w ^ (2 * (j.1 + 1))) o = w ^ (2 * expo o) := by
  rcases o with (_ | ⟨i, _ | _⟩) <;> simp only [expo, DC.tameList]
  · simp
  · rw [mul_neg, zpow_neg, ← zpow_natCast]; push_cast; rfl
  · rw [← zpow_natCast]; push_cast; rfl

theorem dvd_of_pow_eq {g m : ℕ} (w : (ZMod g)ˣ) {o o' : Option (Fin m × Bool)} (hne : o ≠ o') (k : ℕ)
    (h : (w ^ (2 * expo o)) ^ k = (w ^ (2 * expo o')) ^ k) :
    ∃ D : ℕ, 0 < D ∧ D ≤ 4 * m ∧ orderOf w ∣ D * k := by
  have h1 : expo o ≠ expo o' := fun e => hne (expo_inj e)
  have b1 := expo_bound o
  have b2 := expo_bound o'
  refine ⟨(2 * expo o' - 2 * expo o).natAbs, by omega, by omega, ?_⟩
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, zpow_eq_zpow_iff_modEq] at h
  have h2 := h.dvd
  rw [← sub_mul, Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_natCast] at h2
  exact h2

theorem tameDistinct_gen : ∀ (r g m : ℕ) [Fact g.Prime] (w : (ZMod g)ˣ), orderOf w = g - 1 → 4 * (m : ℝ) * (g : ℝ) ^ ((1 : ℝ) / 4) < (g : ℝ) - 1 → 1 ≤ r → DC.TameDistinct r g (fun j : Fin m => w ^ (2 * (j.1 + 1))) := by
  intro r g m hg w hw hlt hr
  have hg2 : 2 ≤ g := hg.out.two_le
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast (by omega : 1 ≤ g)
  have hcast : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hq : (1 : ℝ) ≤ (g : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow hgR (by norm_num)
  have hm0 : (0 : ℝ) ≤ 4 * (m : ℝ) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro o o' h
    by_contra hne
    rw [tameList_eq, tameList_eq] at h
    obtain ⟨D, hD0, hD, hdvd⟩ := dvd_of_pow_eq w hne 1 (by rw [h])
    rw [mul_one, hw] at hdvd
    have h1 : g - 1 ≤ 4 * m := (Nat.le_of_dvd hD0 hdvd).trans hD
    have h2 : ((g - 1 : ℕ) : ℝ) ≤ ((4 * m : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hcast] at h2
    push_cast at h2
    nlinarith
  · intro l hl hB o o' h
    by_contra hne
    apply hB
    simp only [tameList_eq] at h
    have hfin : ∀ u : (ZMod g)ˣ, IsOfFinOrder (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (u : ZMod g)) := by
      intro u
      exact (((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom.comp (Units.coeHom (ZMod g))).isOfFinOrder
        (isOfFinOrder_of_finite u))
    obtain ⟨a, ha⟩ := pow_eq_of_part_eq hl (hfin _) (hfin _) h
    rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val] at ha
    have ha' := Units.ext ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective ha)
    obtain ⟨D, hD0, hD, hdvd⟩ := dvd_of_pow_eq w hne _ ha'
    rw [hw] at hdvd
    have hn : g - 1 ≠ 0 := by omega
    set v := (g - 1).factorization l with hv
    set M := (g - 1) / l ^ v with hM
    have hmul : l ^ v * M = g - 1 := Nat.ordProj_mul_ordCompl_eq_self _ _
    have hcop : M.Coprime l := (Nat.coprime_ordCompl hl hn).symm
    have hMD : M ∣ D := (Nat.Coprime.pow_right a hcop).dvd_of_dvd_mul_right
      ((Dvd.intro_left _ hmul).trans hdvd)
    have hMle : M ≤ 4 * m := (Nat.le_of_dvd hD0 hMD).trans hD
    have h1 : g - 1 ≤ 4 * m * l ^ v := by
      rw [← hmul, mul_comm]; exact Nat.mul_le_mul_right _ hMle
    have h2 : ((g - 1 : ℕ) : ℝ) ≤ ((4 * m * l ^ v : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hcast] at h2
    push_cast at h2
    have h3 : (g : ℝ) ^ ((1 : ℝ) / 4) < (l : ℝ) ^ v := lt_of_mul_lt_mul_left (hlt.trans_le h2) hm0
    have h4 : ((g : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 < ((l : ℝ) ^ v) ^ 4 :=
      pow_lt_pow_left₀ h3 (by positivity) (by norm_num)
    have h5 : ((g : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = g := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    rw [h5, ← pow_mul, mul_comm] at h4
    refine Or.inr ⟨1, le_rfl, hr, hl, ?_⟩
    rw [pow_one, Nat.padicValNat_def, ← Nat.factorization_def _ hl, ← hv]
    exact_mod_cast h4
  · intro j
    exact ⟨w ^ (j.1 + 1), by rw [← pow_add, ← two_mul]⟩

end GlobalTheory.EX.DC.TameGen
