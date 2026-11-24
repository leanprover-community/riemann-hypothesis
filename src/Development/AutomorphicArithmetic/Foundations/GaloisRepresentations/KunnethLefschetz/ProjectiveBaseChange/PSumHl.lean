module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.AdicTopOf
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.sumHl_holds :
    UpperTheory.Gal.KunnethLefschetz.SumHl := by
  unfold UpperTheory.Gal.KunnethLefschetz.SumHl
  intro hS l _ X r Y j hj n
  have hb : ∀ k : ℕ, Function.Bijective fun (x : Ht (l ^ k) (sch.obj X) n 0) (s : Fin r) =>
      pull (ZMod (l ^ k)) (sch.map (j s)) (tw (l ^ k) 0) n x :=
    fun k => hS (ZMod (l ^ k)) (tw (l ^ k) 0) j hj n
  constructor
  · intro x y h
    refine Subtype.ext (funext fun k => (hb k).1 (funext fun s => ?_))
    exact congrArg (fun z : Hl l (sch.obj (Y s)) n 0 => z.1 k) (congrFun h s)
  · intro y
    choose x hx using fun k : ℕ => (hb k).2 (fun s => (y s).1 k)
    refine ⟨⟨x, fun k => (hb k).1 (funext fun s => ?_)⟩,
      funext fun s => Subtype.ext (funext fun k => congrFun (hx k) s)⟩
    exact (pull_red _ _ (sch.map (j s)) n 0 (x (k + 1))).trans
      ((congrArg (red (l ^ (k + 1)) (l ^ k) (sch.obj (Y s)) n 0) (congrFun (hx (k + 1)) s)).trans
        (((y s).2 k).trans (congrFun (hx k) s).symm))
