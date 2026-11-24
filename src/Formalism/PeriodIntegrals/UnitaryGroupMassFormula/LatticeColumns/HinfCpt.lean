module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.PoincareInHH

def InfHAHomeo : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (hb : AdBridgeIso I), ∃ e : I.Ginf ≃ₜ* HA (Ainf I.F) I.cm.sig I.J,
    ∀ s, e s = (splitA I.cm.sig I.J (toHA I hb (s, 1))).1

def HStepInf : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (hb : AdBridgeIso I) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (s : I.Ginf),
    (splitA I.cm.sig I.J (toHA I hb (s, 1))).1 ∈ Hsub (Ainf I.F) I.cm.sig I.J (⟨e, f, z⟩ : Frame I.E I.n r) ↔
      s ∈ Hset I (Set.range e ∪ Set.range f ∪ {z})

def HinfCompactBundle : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
    IsCompact ((PoincareSetting.Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf)

theorem hinfCompact_of (h0 : ∀ I : Formalism.MainNotions.S.AutInst, AdBridgeIso I) (h1 : InfHAHomeo) (h2 : HStepInf)
    (h3 : HinfCompactBundle) : MassDataMassesW.HinfCompact := by
  intro D X u
  obtain ⟨e, he⟩ := h1 X.B.I (h0 X.B.I)
  have key : ∀ s : X.B.I.Ginf, e s ∈ Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) ↔
      s ∈ (PoincareSetting.Hinf X u : Set X.B.I.Ginf) := by
    intro s
    rw [he s]
    exact h2 X.B.I (h0 X.B.I) D.R.rS (frameOf X u).e (frameOf X u).f (frameOf X u).z s
  have hset : (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
      Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) = e '' (PoincareSetting.Hinf X u : Set X.B.I.Ginf) := by
    ext x
    constructor
    · intro hx
      refine ⟨e.symm x, (key _).1 ?_, e.apply_symm_apply x⟩
      rwa [e.apply_symm_apply]
    · rintro ⟨s, hs, rfl⟩
      exact (key s).2 hs
  have hc : IsCompact (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
      Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) := by
    rw [hset]
    exact (h3 X u).image e.toHomeomorph.continuous
  exact isCompact_iff_compactSpace.mp hc

end PIW.MassDataColumns
