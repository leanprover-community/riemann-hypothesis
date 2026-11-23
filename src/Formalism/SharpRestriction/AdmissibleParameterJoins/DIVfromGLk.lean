module

public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV NumberField

variable {D : D7} {L : SizeData₂ D}

theorem ETDef_of {X : ErrX D} {K : Formalism.MainNotions.G.Consts} {c : ErrC} (P : ParameterChoice' D L) (hF : L.FDef) (hE : L.EDef X K c)
    (hTg : ∀ u (i : Fin 2), D.host.g i ≠ (D.mem u).A.T) : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.ETDef D u L := by
  intro u w hw
  have hw' : D.what₂.places.resChar w = (D.mem u).A.T := hw
  have hs : D.host.cls (D.what₂.places.resChar w) = PrimeClass.splitK := by
    rw [hw']; exact P.level_split _ (D.T_level u)
  obtain ⟨hg, ht, _⟩ := L.not_inert w (by rw [hs]; exact fun h => by cases h) (by rw [hs]; exact fun h => by cases h)
  refine ⟨ht, fun j hj => ⟨hg j, ?_, ?_⟩⟩
  · rw [hF j hj w]
    unfold Fval FvalP
    have h1 : D.what₂.places.resChar w ∉ L.gTypes := by
      rw [hw']
      simp only [SizeData₂.gTypes, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hTg u 0 h.symm, fun h => hTg u 1 h.symm⟩
    have h2 : D.host.cls (D.what₂.places.resChar w) ≠ PrimeClass.ramD := by rw [hs]; exact fun h => by cases h
    have h3 : ¬ ((Formalism.MainNotions.G.IsResidueClassZero D (D.what₂.places.resChar w) ∨ Formalism.MainNotions.G.IsSg D (D.what₂.places.resChar w)) ∧
        (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n) := by
      rintro ⟨h | h, _⟩
      · exact absurd (hs.symm.trans h) (fun h => by cases h)
      · exact absurd (hs.symm.trans h) (fun h => by cases h)
    rw [if_neg h1, if_neg h2, if_neg h3]
  · rw [hE u j hj w]
    unfold Eval
    simp only [hw', if_true]

end Formalism.MainNotions.J

end
