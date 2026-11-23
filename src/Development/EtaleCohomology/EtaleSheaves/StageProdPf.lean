module

public import Development.EtaleCohomology.EtaleSheaves.PartDiagCut
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
import Mathlib.Data.Nat.Choose.Multinomial
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
open GlobalTheory.EtC

namespace LateralTheory.E.StageProdPf
open LateralTheory.E.PartDiagCut

theorem zero_not_mem_S {B : Type} [CommRing B] (I : Ideal B) (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (e : P.1) :
    (0 : B) ∉ S I e.1 := by
  rintro ⟨t, ht⟩
  simp only [map_zero, zero_mul] at ht
  exact (P.idem e.1 e.2).2 ht.symm

theorem StageProd_of (hloc : LateralTheory.E.HensCut.LocAIC) : LateralTheory.E.PartDiagCut.StageProd := by
  intro q B _ _ I hB hq P
  let R : Fin P.1.card → Type := fun k => Localization (S I (P.1.equivFin.symm k).1)
  refine ⟨P.1.card, R, fun k => inferInstance, fun k => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hloc B (S I (P.1.equivFin.symm k).1) (zero_not_mem_S I P _) hB
    refine ⟨h1, h2, ?_⟩
    have := hq.map (algebraMap B (R k))
    rwa [map_natCast] at this
  · exact ⟨(RingEquiv.piCongrLeft (fun e : P.1 => Localization (S I e.1)) P.1.equivFin.symm).symm⟩

end LateralTheory.E.StageProdPf
