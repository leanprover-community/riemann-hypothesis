module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousUnitaryDiagonalEmbeddingDoubled
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.exists_continuous_unitaryDiagonalEmbedding_doubled : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
      ∃ ι : Formalism.IndefR.DatumF.GAF σ J →* Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J),
        Continuous ι ∧
        (∀ h, Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (ι h) =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ J h) 0 0 1)) ∧
        (∀ γ ∈ Formalism.IndefR.DatumF.GQF σ J, ι γ ∈ Formalism.IndefR.DatumF.GQF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J)) ∧
        (∀ e h, Formalism.IndefR.DatumF.SuppAtF σ e J h → Formalism.IndefR.DatumF.SuppAtF σ e (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (ι h)) ∧
        (∀ e h y, Formalism.IndefR.DatumF.IsDetAtF σ e J h y →
          Formalism.IndefR.DatumF.IsDetAtF σ e (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (ι h) y) := by
  first | exact @GlobalTheory.DiagEmbU.exists_diagEmb | exact GlobalTheory.DiagEmbU.exists_diagEmb | (intros; apply GlobalTheory.DiagEmbU.exists_diagEmb <;> assumption)
