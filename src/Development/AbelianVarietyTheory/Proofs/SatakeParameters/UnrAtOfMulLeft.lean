module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin

namespace GlobalTheory.MuTameQS

theorem val_lt_one_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) y < 1 ↔ Valued.v y < 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one

theorem val_eq_one_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) y = 1 ↔ Valued.v y = 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one

theorem isTame_loc {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    (h : χ.TameAt w) : GlobalTheory.SplitWeil.IsTame (χ.loc w) := by
  intro x hx
  have h1 : Valued.v ((x : w.adicCompletion E) - 1) < 1 := (val_lt_one_iff w _).1 hx
  refine h x ?_ ?_
  · have := Valuation.map_one_add_of_lt _ h1
    rwa [add_sub_cancel] at this
  · rw [← WithZero.exp_zero] at h1
    exact WithZero.lt_mul_exp_iff_le (by simp) |>.1 (by simpa [← WithZero.exp_add] using h1)

theorem not_isUnram_loc {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    (h : ¬ χ.UnrAt w) : ¬ GlobalTheory.SplitWeil.IsUnram (χ.loc w) := fun hu =>
  h fun x hx => hu x ((val_eq_one_iff w _).2 hx)

theorem tameAt_mul {E : Type} [Field E] [NumberField E] {χ χ' : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    (h : χ.TameAt w) (h' : χ'.TameAt w) : (χ * χ').TameAt w := fun x hx hx' => by
  change χ.loc w x * χ'.loc w x = 1
  rw [h x hx hx', h' x hx hx', one_mul]

theorem unrAt_of_mul_left {E : Type} [Field E] [NumberField E] {χ χ' : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    (h : χ.UnrAt w) (h' : (χ * χ').UnrAt w) : χ'.UnrAt w := fun x hx => by
  have := h' x hx
  change χ.loc w x * χ'.loc w x = 1 at this
  rwa [h x hx, one_mul] at this

end GlobalTheory.MuTameQS
