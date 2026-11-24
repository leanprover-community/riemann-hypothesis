module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHasTemperateGrowth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMaximalCompactIntertwinesFockDerivati
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

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

theorem _root_.GlobalTheory.T.archimedeanMaximalCompact_intertwines_fockDerivativeOps : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ W B.emb,
    ∀ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) →
    ∀ a b : Fin n × Fin d → mixedEmbedding.mixedSpace F, ∃ a' b' : Fin n × Fin d → mixedEmbedding.mixedSpace F,
      ∀ f : SInf F (Fin n × Fin d), A (GlobalTheory.ThK.EvAt0.PolD.dOp a b f) = GlobalTheory.ThK.EvAt0.PolD.dOp a' b' (A f) := by
  first | exact @GlobalTheory.KInfComm.main | exact GlobalTheory.KInfComm.main | (intros; apply GlobalTheory.KInfComm.main <;> assumption)
