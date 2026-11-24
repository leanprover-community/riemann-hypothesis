module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.HeckeLevelWordBase
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
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.ChainSc

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical



open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.adelWord_of_parts :
    AdelRep → FinConv → PsiWord → ProdOk → LocOk → FrFacts → TwOk → AdelWord := by
  intro hAR hFC hPW hPO hLO hFR hTw hR E _ _ _ n π S T F₀ F hS i ws
  have hle := F₀.C.le i
  have hsec := F₀.hSec
  have hP := (hFR hR E n π S T F₀ F).2.2.2
  have hne : ∀ w ∈ F.d.P, Nonempty (F.d.kap w) := fun w _ => (hLO E n F.d F.ok _ hle).1 w
  have hL0 := hPO E n F.d F.ok (lw F ws) _ hle
  have ht := hPW hR E n π S T F₀ F i ws
  have hok := (hTw hR E n π S T F₀ F hS i).2.2 ws
  have key := hAR E F.d.kap F₀.Sec F.d.P (F.B i) (Equiv.refl _) hsec hP hne (F₀.u₁ _) (F₀.u₂ _)
    (F₀.A i).Ta (F₀.A i).Tb F.d.one (fun _ => F.d.eL _) [] (tw F i ws)
    (prodL F.d (lw F ws) (F₀.C.a i)) (by simp) hL0 ht
  refine ⟨key.2.2, (hFC E (F.B i) F₀.Sec hsec).1, fun v => ?_⟩
  exact (F₀.A i).lef v _ _ _ _ _ (hok.ka v) (hok.kb v)

end
