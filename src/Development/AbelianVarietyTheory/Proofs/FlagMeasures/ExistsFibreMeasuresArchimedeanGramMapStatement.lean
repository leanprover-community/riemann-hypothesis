module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFibreMeasuresArchimedeanGramMap
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem _root_.GlobalTheory.T.exists_fibreMeasures_archimedeanGramMap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M a : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a)),
      μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
      ∃ fib : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
        IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val
          {X | LinearIndependent (Ainf F ⊗[F] E) X} ν Set.univ fib := by
  first | exact @GlobalTheory.ArchGramFibre.exists_fibreFamily | exact GlobalTheory.ArchGramFibre.exists_fibreFamily | (intros; apply GlobalTheory.ArchGramFibre.exists_fibreFamily <;> assumption)
