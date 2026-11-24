module

public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.SeeSaw

namespace GlobalTheory.PlaceCompare.Spherical

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n'' n' n : Type} [Fintype n''] [DecidableEq n''] [Fintype n'] [DecidableEq n'] [Fintype n] [DecidableEq n]

end Local

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum IsDedekindDomain NumberField
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_unram_char (D : D7) (n : ℕ) :
    ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ n ∧ UnramEverywhere D χ := by
  obtain ⟨η, h1, h2, h3, -⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  refine ⟨η ^ n, ⟨?_, fun x => ?_⟩, ⟨h3.1, fun e he a => ?_⟩, fun x a b c => ?_⟩
  · have : ((η ^ n : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ n := by
      funext x; simp
    rw [this]
    exact h1.1.pow n
  · rw [MonoidHom.pow_apply, h1.2 x, one_pow]
  · rw [MonoidHom.pow_apply, h3.2 e he a, pow_one]
  · rw [MonoidHom.pow_apply, h2 x a b c, one_pow]

end Global

end GlobalTheory.PlaceCompare.Spherical

end
