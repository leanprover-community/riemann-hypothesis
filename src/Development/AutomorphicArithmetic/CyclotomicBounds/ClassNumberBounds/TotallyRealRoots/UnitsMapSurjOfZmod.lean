module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LeNuIffPowMemPrinc
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
import Mathlib.GroupTheory.Nilpotent
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem units_map_surj_of_zmod (n : ℕ) (f : ℤ_[l] →+* ZMod n) :
    Function.Surjective (Units.map f.toMonoidHom) := by
  by_cases hn : n = 1
  · subst hn
    intro y
    exact ⟨1, Subsingleton.elim _ _⟩
  · haveI : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr hn
    have hf : Function.Surjective f := fun y =>
      ⟨((ZMod.cast y : ℤ) : ℤ_[l]), by rw [map_intCast, ZMod.intCast_zmod_cast]⟩
    exact IsLocalRing.surjective_units_map_of_local_ringHom f hf (IsLocalHom.of_surjective f hf)

theorem princ_anti {a b : ℕ} (h : a ≤ b) : princ l b ≤ princ l a := by
  intro u hu
  rw [mem_princ] at hu ⊢
  exact (pow_dvd_pow _ h).trans hu

theorem princ_one_eq_ker : princ l 1 = (red l).ker := by
  ext u
  rw [mem_princ, MonoidHom.mem_ker, pow_one]
  have key : PadicInt.toZMod ((u : ℤ_[l]) - 1) = 0 ↔ (l : ℤ_[l]) ∣ (u : ℤ_[l]) - 1 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton]
  rw [← key, map_sub, map_one, sub_eq_zero]
  simp [red, Units.ext_iff]

theorem redPow_surjective (a : ℕ) : Function.Surjective (redPow l a) :=
  units_map_surj_of_zmod _ _

theorem red_surjective : Function.Surjective (red l) :=
  units_map_surj_of_zmod _ _

end KStar.TotallyRealRoots
