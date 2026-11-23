module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

theorem GlobalTheory.Fam.finComb3 (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' c'' : WO S T →₀ ℂ) :
    GlobalTheory.SeeSaw.IsFinComb c → GlobalTheory.SeeSaw.IsFinComb c' → GlobalTheory.SeeSaw.IsFinComb c'' → ∃ d, GlobalTheory.SeeSaw.IsFinComb d ∧
      ∀ f, comb ψ S T d f = comb ψ S T c (comb ψ S T c' (comb ψ S T c'' f)) := by
  intro h h' h''
  obtain ⟨c1, hs1, he1⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 c' c''
  obtain ⟨d, hs, he⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 c c1
  have key : ∀ x y : WO S T, Matrix.map x (infPart D) = 0 → Matrix.map y (infPart D) = 0 →
      Matrix.map (x + y) (infPart D) = 0 := by
    intro x y hx hy
    rw [Matrix.map_add _ (fun a b => (infPart D).map_add a b), hx, hy, add_zero]
  refine ⟨d, fun w hw => ?_, fun f => by rw [he, he1]⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := hs w hw
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := hs1 y hy
  exact key _ _ (h x hx) (key _ _ (h' y1 hy1) (h'' y2 hy2))
