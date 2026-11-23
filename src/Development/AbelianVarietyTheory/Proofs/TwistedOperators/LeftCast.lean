module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefPerEqGenPer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftLowestKTypeCompatibility
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowReal

theorem left_cast {D : D7} {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (X : LSp D) (h : X = ⟨D.sp.X', Λ⟩)
    (φ : GA D D.sp.X' → ℂ) (hφ : ∀ γ ∈ GQ D.sp.X', ∀ g, φ (γ * g) = φ g) :
    ∀ γ ∈ GQ X.sp, ∀ g, φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) (γ * g)) =
      φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g) := by
  subst h
  exact hφ

theorem gen_left : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch =>
    (∀ a ξ, ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g,
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (γ * g) =
        pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) g) ∧
    ∀ t y η, ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formGen ch t y η (γ * g) = formGen ch t y η g := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ => ?_⟩⟩
  refine ⟨fun a ξ γ hγ g => GlobalTheory.RowBplus.pairVec_left ch.G ch.W.θ ξ (col_mem ch a) hγ g, fun t y η => ?_⟩
  have hm := hS.core.models
  exact left_cast (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh) (fun g => η (R.cX.ext ((R.HX t).e y) g))
    (fun γ hγ g => congrArg η
      (GlobalTheory.ThetaProjEquiv.ext_left R.cX ((R.HX t).e y) _ _ ((hm.HX t).2.1.le ⟨y, rfl⟩) γ hγ g))

end GlobalTheory.RowReal

end
