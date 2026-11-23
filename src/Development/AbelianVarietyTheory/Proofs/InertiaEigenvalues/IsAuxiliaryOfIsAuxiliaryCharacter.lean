module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlacesBelowSplitCoprimeConductorOfAdmissible
import Formalism.ConjugateSelfDual.Statement
import Formalism.FrobeniusOrbits.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.GridCharacters

theorem levelLe_of_le {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {m n : ℕ}
    (h : χ.LevelLe w m) (hmn : m ≤ n) : χ.LevelLe w n := fun x hx hx' =>
  h x hx (hx'.trans (WithZero.exp_le_exp.2 (by omega)))

theorem expAt_succ {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    (h : χ.LevelLe w (n + 1)) (h' : ¬ χ.LevelLe w n) : ExpAt χ w (n + 1) := fun m =>
  ⟨fun hm => by
    by_contra hlt
    exact h' (levelLe_of_le hm (by omega)), fun hm => levelLe_of_le h hm⟩

end GlobalTheory.LamTie.GridCharacters
