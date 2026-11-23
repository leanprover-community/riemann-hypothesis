module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1

theorem UpperTheory.V.Af.Tw.awayTriv :
    UpperTheory.V.Af.Tw.AwayTriv := by
  intro F B _ _ _ _ _ _ N S hN hinf hS b hbS hbin
  classical
  have k1 : (b : AdeleRing (𝓞 F) F).1 * ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).1 = 1 :=
    congrArg Prod.fst (Units.mul_inv b)
  have k2 : ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).1 * (b : AdeleRing (𝓞 F) F).1 = 1 :=
    congrArg Prod.fst (Units.inv_mul b)
  have k3 : (b : AdeleRing (𝓞 F) F).2 * ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.mul_inv b)
  have k4 : ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).2 * (b : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.inv_mul b)
  let binf : Ideles F := ⟨((b : AdeleRing (𝓞 F) F).1, 1), (((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).1, 1),
    Prod.ext k1 (mul_one 1), Prod.ext k2 (mul_one 1)⟩
  let bfin : Ideles F := ⟨(1, (b : AdeleRing (𝓞 F) F).2), (1, ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).2),
    Prod.ext (mul_one 1) k3, Prod.ext (mul_one 1) k4⟩
  have hb : b = binf * bfin := by
    apply Units.ext
    exact Prod.ext (mul_one _).symm (one_mul _).symm
  have hfin2 : (↑bfin : AdeleRing (𝓞 F) F).2 = (↑b : AdeleRing (𝓞 F) F).2 := rfl
  have h1 : N binf = 1 := hinf binf rfl
  have h2 : N bfin = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_local N hN bfin rfl ?_
    intro v
    by_cases hv : v ∈ S
    · have hone : Units.map (GlobalTheory.Mem.LocTriv.ev v) bfin = 1 := by
        apply Units.ext
        rw [Units.coe_map, Units.val_one]
        change (↑bfin : AdeleRing (𝓞 F) F).2 v = 1
        rw [hfin2]
        exact hbin v hv
      rw [hone, map_one, map_one]
    · apply hS v hv
      change Valued.v ((↑bfin : AdeleRing (𝓞 F) F).2 v) = 1
      rw [hfin2]
      exact hbS v hv
  rw [hb, map_mul, h1, h2, one_mul]
