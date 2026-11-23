module

public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.PHeisTh

abbrev Ix {D : D7} (V W : HSp D) : Type := Fin V.rank × Fin W.rank × Fin (nE D)

def Co {D : D7} (V W : HSp D) (x : WA V W) (a : Ix V W) : AF D.host.F := Phi V W x a.1 a.2.1 a.2.2

def CoordFinP : Prop :=
  ∀ (D : D7) (V W : HSp D) (x : WA V W), x.map (finPart D) = 0 → ∀ a, (Co V W x a).2 = 0



def PsiOpenP : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∃ G : AddSubgroup (Af F), IsOpen (G : Set (Af F)) ∧ (∀ y ∈ G, ∀ z ∈ Ohat F, z * y ∈ G) ∧
      ∀ y ∈ G, ψ (pairA F 0 y) = 1

def PsiSmoothP : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (k : ℕ) (s : (Fin k → ℝ) →+ Ainf D.host.F), Continuous s →
      ContDiff ℝ ∞ fun t => ψ (pairA D.host.F (s t) 0)

end Formalism.IndefR.PHeisTh

end
