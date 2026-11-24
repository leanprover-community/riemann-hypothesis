module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfFS
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TensorProduct.Pi
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

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct

theorem isReduced_tens_field (F E C : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [Field C] [Algebra F C] : IsReduced (C ⊗[F] E) := by
  have : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
  exact Algebra.FormallyUnramified.isReduced_of_field C (C ⊗[F] E)

theorem semisimpleTens_holds : SemisimpleTens := by
  intro F E _ _ _ _ _ σ _
  classical
  have : IsArtinianRing (Ainf F) :=
    inferInstanceAs (IsArtinianRing ((v : InfinitePlace F) → v.Completion))
  have : IsArtinianRing (Ainf F ⊗[F] E) := IsArtinianRing.of_finite (Ainf F) (Ainf F ⊗[F] E)
  let e1 : Ainf F ⊗[F] E ≃ₐ[F] E ⊗[F] Ainf F := Algebra.TensorProduct.comm F (Ainf F) E
  let e2 : E ⊗[F] ((v : InfinitePlace F) → v.Completion) ≃ₐ[F]
      ((v : InfinitePlace F) → E ⊗[F] v.Completion) :=
    Algebra.TensorProduct.piRight F F E (fun v : InfinitePlace F => v.Completion)
  have : ∀ v : InfinitePlace F, IsReduced (E ⊗[F] v.Completion) := fun v =>
    have := isReduced_tens_field F E v.Completion
    isReduced_of_injective (Algebra.TensorProduct.comm F E v.Completion).toRingHom
      (Algebra.TensorProduct.comm F E v.Completion).injective
  have : IsReduced (Ainf F ⊗[F] E) :=
    isReduced_of_injective ((e2.toRingHom).comp e1.toRingHom) (e2.injective.comp e1.injective)
  exact IsArtinianRing.isSemisimpleRing_of_isReduced _

theorem densInf_of_tensR (h : TensR) : DensInf := densInf_of_ss h semisimpleTens_holds

end PI.VolStabS
