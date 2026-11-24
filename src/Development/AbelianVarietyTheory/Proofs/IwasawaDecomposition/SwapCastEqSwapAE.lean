module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtId

variable {D : D7}

theorem idFrame_iff_unitFr {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank) :
    GlobalTheory.MtRead.IdFrame hF P ↔ GlobalTheory.MtIn.UnitFr P := by
  constructor
  · rintro ⟨hn, h⟩ κ
    refine Units.ext (Matrix.ext fun a b => ?_)
    have := (RingEquiv.eq_symm_apply _).1 (h κ a b)
    exact this
  · intro h
    refine ⟨rfl, fun κ a b => (RingEquiv.eq_symm_apply _).2 ?_⟩
    exact congrArg (fun g : GL (Fin V.rank) (EAf D) => g.val a b) (h κ)

def castFr {V : HSp D} {n : ℕ} (hn : V.rank = n) (P : principalLevelFrame.RowPsi V V.rank) : principalLevelFrame.RowPsi V n := hn ▸ P

theorem idFrame_castFr {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (hn : V.rank = n)
    {P : principalLevelFrame.RowPsi V V.rank} (h : GlobalTheory.MtIn.UnitFr P) : GlobalTheory.MtRead.IdFrame hF (castFr hn P) := by
  subst hn
  exact (idFrame_iff_unitFr hF P).2 h

end GlobalTheory.MtId

end
