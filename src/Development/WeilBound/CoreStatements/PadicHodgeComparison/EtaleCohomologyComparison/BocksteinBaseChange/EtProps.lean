module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsKumCoc
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

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison

def ModelComponents : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  CompM (Model.Sm (l := l) (K := K)) ∧ CompM (Model.Good (l := l) (K := K))

def GeometricGenericComponents : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M : Model l K), M.Good →
  ∀ d, M.Conn d → M.Geo

def LAdicCoefficientPassage : Prop := ZIn → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (G : Model l K → Prop),
  (∀ M, G M → M.Good) → CompM G → (∀ M, G M → ∀ d, M.Conn d → M.Geo) → EtSide G

structure FormalIn : Prop where
  a1 : GlobalTheory.EtC.A1
  a6nat : GlobalTheory.EtC.DivisorNaturality
  a6ring : GlobalTheory.EtC.DivisorRingCompatibility
  a7 : GlobalTheory.EtC.A7
  a8 : GlobalTheory.EtC.A8
  a9 : GlobalTheory.EtC.A9
  a10 : GlobalTheory.EtC.A10
  et : E.EtIn

def BocksteinInputFromFormal : Prop := FormalIn → InBock

def RootsOfUnityFormal : Prop := FormalIn → InRoot

def SumInputFromFormal : Prop := FormalIn → InSum

end CrystallineSemistableComparison
