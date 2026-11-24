module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
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

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LJPos

structure SplitPkg (D : D7) (v : Pl D) where
  π : Fv D.host.F v ⊗[D.host.F] D.host.E ≃ₐ[Fv D.host.F v] Fv D.host.F v × Fv D.host.F v
  swap : ∀ y, π (sigR (Fv D.host.F v) D.sp.cm.sig y) = (π y).swap
  int : ∀ y, y ∈ intLoc D.host.F D.host.E v ↔
    (π y).1 ∈ v.adicCompletionIntegers D.host.F ∧ (π y).2 ∈ v.adicCompletionIntegers D.host.F

def PlaceEx : Prop := ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ, IsHeckeChar D χ →
  ∀ r : ℕ, ResEta D χ r → ∀ S : Finset (Pl D), ∃ v ∉ S, ∃ P : SplitPkg D v,
    (∀ a : Fv D.host.F v, (∀ b ∈ v.adicCompletionIntegers D.host.F, psiV D.host.F ψ v (a * b) = 1) ↔
      a ∈ v.adicCompletionIntegers D.host.F) ∧
    (∀ u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, (P.π u).1 ∈ v.adicCompletionIntegers D.host.F →
      (P.π (u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)).1 ∈ v.adicCompletionIntegers D.host.F → (P.π u).2 = 1 →
      χ (ideleAt D.host.F D.host.E v u) = 1) ∧
    ∀ u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, (P.π u).1 = (P.π u).2 → χ (ideleAt D.host.F D.host.E v u) = 1

end PositivityTheory.Rg.Rsw.L.LJPos

end
