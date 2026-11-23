module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrCharAtOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.normVal :
    NormVal := by
  intro Ω _ _ _ U hU q hq
  classical
  set K : IntermediateField ℚ Ω := IntermediateField.fixedField U with hK
  have hfix : K.fixingSubgroup = U :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U, U.isClosed_of_isOpen hU⟩
  have hfin : FiniteDimensional ℚ K := by
    rw [← InfiniteGalois.isOpen_iff_finite, hfix]
    exact hU
  have hq0 : q ≠ 0 := by omega
  have hpp : q.minFac.Prime := Nat.minFac_prime (by omega)
  haveI : Fact q.minFac.Prime := ⟨hpp⟩
  have ha : 0 < padicValNat q.minFac q := by
    rw [Nat.padicValNat_def]
    exact one_le_multiplicity_of_dvd hq0 (Nat.minFac_dvd q)
  refine ⟨Module.finrank ℚ K * padicValNat q.minFac q, Nat.mul_pos Module.finrank_pos ha, ?_⟩
  intro z n c hz hzq
  rcases n with _ | k
  · have h1 : ((q ^ c : ℕ) : Ω) = ((1 : ℕ) : Ω) := by simpa using hzq
    have h2 : q ^ c = 1 := Nat.cast_injective h1
    rcases (Nat.pow_eq_one.1 h2) with h | h
    · omega
    · simp [h]
  have hzK : z ∈ K := (IntermediateField.mem_fixedField_iff U z).2 hz
  set w : K := ⟨z, hzK⟩ with hwdef
  have hw : w ^ (k + 1) * (algebraMap ℚ K (q : ℚ)) ^ c = 1 := by
    apply Subtype.ext
    simpa [hwdef] using hzq
  have hN := congrArg (Algebra.norm ℚ) hw
  rw [map_mul, map_pow, map_pow, Algebra.norm_algebraMap, map_one] at hN
  have hNw : Algebra.norm ℚ w ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.succ_ne_zero k), zero_mul] at hN
    exact zero_ne_one hN
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq0
  have hv := congrArg (padicValRat q.minFac) hN
  rw [padicValRat.mul (pow_ne_zero _ hNw) (pow_ne_zero _ (pow_ne_zero _ hqQ)),
    padicValRat.pow, padicValRat.pow, padicValRat.pow, padicValRat.one,
    padicValRat.of_nat] at hv
  have hd : ((k + 1 : ℕ) : ℤ) ∣ ((c * (Module.finrank ℚ K * padicValNat q.minFac q) : ℕ) : ℤ) := by
    refine ⟨-padicValRat q.minFac (Algebra.norm ℚ w), ?_⟩
    rw [Nat.padicValNat_def, Nat.cast_mul, Nat.cast_mul]
    linear_combination hv
  exact Int.natCast_dvd_natCast.1 hd
