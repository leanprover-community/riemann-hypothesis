module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

@[expose] public section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_primval :
    ∀ {R : Type} [CommRing R] {N : ℕ} [NeZero N] (χ : DirichletCharacter R N) (x : ZMod χ.conductor), χ.primitiveCharacter x = 0 ∨ ∃ u : (ZMod N)ˣ, χ.primitiveCharacter x = χ u := by
  intro R _ N _ χ x
  by_cases hx : IsUnit x
  · right
    obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective χ.conductor_dvd_level hx.unit
    refine ⟨u, ?_⟩
    conv_rhs => rw [← χ.changeLevel_primitiveCharacter]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, ← ZMod.unitsMap_val, hu]
    · simp
    · exact χ.conductor_dvd_level
  · left
    exact MulChar.map_nonunit _ hx
