module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

namespace GlobalTheory.BigOn.PageNumbers

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L}

theorem le_sup_fin (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (k : ℕ) (hk : k < D.R.m) :
    WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK (k + 1)) ≤
      Finset.univ.sup fun j : Fin D.R.m => WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK ((j : ℕ) + 1)) := by
  have h := Finset.le_sup (f := fun j : Fin D.R.m => WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK ((j : ℕ) + 1)))
    (Finset.mem_univ (⟨k, hk⟩ : Fin D.R.m))
  exact h

theorem sup_fin_eq_topDeg (Tp : ParamsT D L Pm) (hK : DV.KapDef D) :
    (Finset.univ.sup fun j : Fin D.R.m => WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK ((j : ℕ) + 1))) = GlobalTheory.IndexAssembly.topDeg Tp hK := by
  apply le_antisymm
  · exact Finset.sup_le fun j _ => GlobalTheory.IndexAssembly.le_topDeg Tp hK ⟨by omega, by omega⟩
  · refine Finset.sup_le fun j hj => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact le_sup_fin Tp hK k (by omega)

end GlobalTheory.BigOn.PageNumbers

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.BigOn

end
