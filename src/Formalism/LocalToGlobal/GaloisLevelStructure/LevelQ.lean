module

public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.L2

variable {D : D7} {C : Host.CharFrame D} {nch : NChoice D}

theorem qPl_tup (Tp : Host.TupTied D C nch) (μ : D.what₂.Tup) (j : Fin D.R.m) :
    qPl D (Tp.tup μ j) = {v | v ∉ gPl D ∧ ∃ w : PlE D.host, NG.OverPl w v ∧ ¬ (Tp.xi μ).UnrAt w} := by
  ext v
  simp only [qPl, Set.mem_ofPred_eq, Host.TupTied.tup]
  refine and_congr_right fun hv => exists_congr fun w => and_congr_right fun hw => not_congr ?_
  have hm : (C.mu0 j).UnrAt w := by
    refine (C.isMu0 j).unr w fun k hk => hv ?_
    simp only [gPl, Set.mem_ofPred_eq]
    exact ⟨w, hw, k, hk⟩
  constructor
  · intro h x hx
    have hx' := h x hx
    change (C.mu0 j).loc w x * (Tp.xi μ).loc w x = 1 at hx'
    rw [hm x hx, one_mul] at hx'
    exact hx'
  · intro h x hx
    change (C.mu0 j).loc w x * (Tp.xi μ).loc w x = 1
    rw [hm x hx, h x hx, one_mul]

end Formalism.L2
