module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.chi :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] (q n m : ℕ) (a : Fin q → ℕ), (∀ j, m ≤ a j) → ∀ p : Fin q × Fin n, ∃ χ : Del l n a →* Multiplicative (Om O m), ∀ p', χ (Pi.mulSingle p' (Multiplicative.ofAdd 1)) = Multiplicative.ofAdd (if p = p' then 1 else 0) := by
  intro l _ O _ _ _ _ q n m a ha p
  have hl : (l : O) ∈ maximalIdeal O := by
    haveI : CharP (ResidueField O) l := IsCoef.char
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  have h0 : (zmultiplesHom (Om O m) 1) ((l ^ a p.1 : ℕ) : ℤ) = 0 := by
    have : ((l : O) ^ a p.1) ∈ maximalIdeal O ^ m :=
      Ideal.pow_le_pow_right (ha _) (Ideal.pow_mem_pow hl _)
    have h2 := Ideal.Quotient.eq_zero_iff_mem.mpr this
    simpa using h2
  let f : ZMod (l ^ a p.1) →+ Om O m := ZMod.lift _ ⟨zmultiplesHom (Om O m) 1, h0⟩
  have f1 : f 1 = 1 := by
    have := ZMod.lift_coe (l ^ a p.1) ⟨zmultiplesHom (Om O m) 1, h0⟩ 1
    simpa [f] using this
  refine ⟨(AddMonoidHom.toMultiplicative f).comp
    (Pi.evalMonoidHom (fun p : Fin q × Fin n => Multiplicative (ZMod (l ^ a p.1))) p), fun p' => ?_⟩
  by_cases h : p = p'
  · subst h
    simp [f1]
  · simp [h, Pi.mulSingle_eq_of_ne h]
