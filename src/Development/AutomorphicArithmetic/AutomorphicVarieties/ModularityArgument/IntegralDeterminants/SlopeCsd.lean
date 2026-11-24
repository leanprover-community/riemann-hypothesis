module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.WeightBounds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightEx
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

theorem UpperTheory.V.Z.Int.slopeCsd :
    GlobalTheory.Cong.DescOffT → UpperTheory.V.Z.Int.SlopeOn .csd := by
  intro hD l _ ι E _ _ _ l' n hl' hn π χ hs w hw B hB
  obtain ⟨h1, h2, h3, rfl⟩ := hs
  obtain ⟨T, -, -, U, hU⟩ := hD E l' n hl' hn π ⟨h1, h2, h3, rfl⟩ ∅
  choose lam hlam using GlobalTheory.CompanionTheory.WeightExist.weightEx E n U hU.aut
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL E n π w
  have hS := UpperTheory.V.Z.Int.coreU l ι E n hn U hU.aut lam hlam w hw σ B (hU.split w hw σ hσ)
    ((GlobalTheory.BcSpehCompare.hasSat_iff hσ B).1 hB)
  have e : (CG.mk π).infChar = fun φ => infOfWeight (lam φ) := funext fun φ => hU.inf φ _ (hlam φ)
  rw [e]
  exact hS
