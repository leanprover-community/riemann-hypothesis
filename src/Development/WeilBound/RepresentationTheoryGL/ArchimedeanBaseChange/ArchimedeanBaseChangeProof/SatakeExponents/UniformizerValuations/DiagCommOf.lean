module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.DataExOf
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

@[expose] public section

noncomputable section

namespace PositivityTheory.Rg.BcB.F

theorem diagComm_of (h : Eig.DiagAlg) : GenIn.DiagComm := by
  intro I d blk c c'
  refine ⟨?_, ?_⟩
  · exact ((h _ _ blk _ _ 0).1.symm.trans (by rw [mul_comm])).trans (h _ _ blk _ _ 0).1
  · rw [(h _ _ blk c' 0 0).2.2.2]
    exact ((h _ _ blk _ _ 0).1.symm.trans (by rw [mul_comm])).trans (h _ _ blk _ _ 0).1

theorem genToData : GenToData := by
  intro E _ _ _ n π S T K W G h0 hb hr
  exact ⟨{ ι := G.ι, H := G.H, d := G.d, Γ := G.Γ, gen := G.gen
           comm := fun x y => Prod.ext (funext fun s => G.comm x y s) (h0 _ _ G.blk _ _).1
           commStar := fun x y => Prod.ext (funext fun s => G.commStar x y s) (h0 _ _ G.blk _ _).2
           β := G.βop, βcomm := G.βcomm, m := G.m, u := G.u, ucomm := G.ucomm, v := G.v, v_ne := G.v_ne, uv := G.uv
           eigv := fun x => ⟨G.c x G.i₀, G.vblk x⟩
           a₀ := G.a₀, a₀v := ⟨G.c G.a₀ G.i₀, G.a₀ne, (G.vblk G.a₀).1⟩
           bound := hb, read := hr }⟩

end PositivityTheory.Rg.BcB.F

end
