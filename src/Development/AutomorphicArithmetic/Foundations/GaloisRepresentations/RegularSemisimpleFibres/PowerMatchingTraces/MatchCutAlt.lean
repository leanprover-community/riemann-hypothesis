module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.NormLoc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.NormOpen
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.matchCut :
    UpperTheory.Gal.InertialTypesAlt.G.MatchCut := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn v c φ f
  have hO := normOpen F E σ hσ hp n hn v
  refine ⟨?_, ?_⟩
  · intro hM _ _ _ _ mE mF hE hF h1 h2 γ hγ ν hν
    obtain ⟨ha, hb⟩ := hM mE mF hE hF h1 h2 γ hγ ν hν
    by_cases hg : γ ∈ normSet E n v
    · have horb : orb mF γ ν ((normSet E n v).indicator f) = orb mF γ ν f := by
        unfold orb
        congr 1
        funext x
        exact Set.indicator_of_mem ((hO.2 γ x).2 hg) f
      rw [horb]
      exact ⟨ha, hb⟩
    · have horb : orb mF γ ν ((normSet E n v).indicator f) = 0 := by
        have hz : (fun x => (normSet E n v).indicator f (x⁻¹ * γ * x)) = fun _ => (0 : ℂ) := by
          funext x
          exact Set.indicator_of_notMem (fun h => hg ((hO.2 γ x).1 h)) f
        unfold orb quotInt
        rw [hz]
        simp
      exact ⟨fun δ hδ => absurd (normLoc F E σ hσ hp n hn v γ δ hδ) hg, fun _ => horb⟩
  · intro hT
    obtain ⟨h1, h2⟩ : IsLocallyConstant f ∧ HasCompactSupport f := hT
    exact ⟨(LocallyConstant.indicator (⟨f, h1⟩ : LocallyConstant _ ℂ) hO.1).isLocallyConstant,
      h2.mono fun x hx hx0 => hx (Set.indicator_apply_eq_zero.2 fun _ => hx0)⟩
