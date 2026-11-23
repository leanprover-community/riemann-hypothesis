module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.IndefiniteReal.RealRec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.Reads

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}



theorem liftGroupForms_eq_extended_rationalForms_companion (x : TwIn ex) : Formalism.IndefR.RecTie.MtRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (twPOf (divisionPairOfAdelicFormsFaceColumnsData x) x.Y.tupT x.Y.tupTie) := by
  intro μ hμ i v
  have key : ∀ (t : x.T) (μ : D.what₂.Tup) (e : x.Y.tup t = μ) (hμ : Formalism.IndefR.RecTie.Used0 D μ) (e' : x.Y.tupT μ = t)
      (v : D.what₂.MtL μ ((i : ℕ) + 1)),
      HEq (x.Y.IL.jMt μ hμ i (D.what₂.jMt μ ((i : ℕ) + 1) v)).1
        (x.R.toRealDat.extV i t (x.R.toRealDat.jV i t (liftForm x.A3.A x.F.P0 x.F.ψ0 i t ((x.Y.eMt i t).symm (e.symm ▸ v))))) := by
    intro t μ e hμ e' v
    subst e
    have := x.Y.mtRead i t hμ ((x.Y.eMt i t).symm v)
    rw [LinearEquiv.apply_symm_apply] at this
    exact heq_of_eq this
  have := eq_of_heq (key _ μ (x.Y.tupTie μ hμ) hμ rfl v)
  rw [this]
  unfold twPOf
  rw [dite_eq_left hμ]
  rfl



end GlobalTheory.Mem.R3.Reads

end
