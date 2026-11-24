module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem qmap_comp {l : ℕ} {R : Type} [CommRing R] {B C D : Obj l R} (h : Hom B C) (h₂ : Hom C D) (m : ℕ) :
    qmap (h₂.comp h) m = (qmap h₂ m).comp (qmap h m) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem stable_comp : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C D : Obj l R) (h : Hom B C)
    (h₂ : Hom C D), Stable h → Stable h₂ → Stable (h₂.comp h) := by
  intro l _ R _ B C D h h₂ s s₂
  refine ⟨fun m => ?_, fun B' k => ?_⟩
  · rw [qmap_comp]
    exact RingHom.Flat.comp (s.flat m) (s₂.flat m)
  · obtain ⟨C', k', h', p⟩ := s.po B' k
    obtain ⟨D', k'', h₂', p₂⟩ := s₂.po C' k'
    refine ⟨D', k'', h₂'.comp h', ⟨?_, fun m => ?_⟩⟩
    · apply Hom.ext'
      have e1 := congrArg Hom.f p.comm
      have e2 := congrArg Hom.f p₂.comm
      change k''.f.comp (h₂.f.comp h.f) = (h₂'.f.comp h'.f).comp k.f
      change k'.f.comp h.f = h'.f.comp k.f at e1
      change k''.f.comp h₂.f = h₂'.f.comp k'.f at e2
      rw [← RingHom.comp_assoc, e2, RingHom.comp_assoc, e1, RingHom.comp_assoc]
    · have := (p.po m).paste_horiz (p₂.po m)
      rw [qmap_comp, qmap_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp]
      exact this

end GlobalTheory.BSP
