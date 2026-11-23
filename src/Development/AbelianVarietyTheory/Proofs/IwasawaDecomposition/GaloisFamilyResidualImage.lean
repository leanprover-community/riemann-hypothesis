module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.ChiDefs
public import ReciprocityTheory.NeutralLocalFields.Reciprocity
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.ChiOneRead

theorem localIdele_eq {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    Neutral.B1.localIdele E P u = Units.map (Formalism.L2.NC.locM P) u := by
  classical
  apply Units.ext
  rfl

theorem sqrt_zpow (q : ℕ) (r : ℕ) (t nV : ℕ) (h : nV = r + t) :
    ((Real.sqrt q : ℝ) : ℂ) ^ (-(r : ℤ)) = ((q : ℕ) : ℂ) ^ (((((t : ℝ) - 1) / 2 + (1 - (nV : ℝ)) / 2) : ℝ) : ℂ) := by
  subst h
  have e : (((t : ℝ) - 1) / 2 + (1 - ((r + t : ℕ) : ℝ)) / 2) = -(r : ℝ) / 2 := by push_cast; ring
  rw [e]
  rw [show ((q : ℕ) : ℂ) = ((q : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
    ← Complex.ofReal_zpow]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast; ring

end GlobalTheory.ChiOneRead
