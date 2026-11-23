module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership

open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling

section Matrices

variable {n : ℕ} (ε : Fin n → Bool)

def IsInP (X : Matrix (Fin n) (Fin n) ℂ) : Prop := X.IsHermitian ∧ ∀ i j, ε i = ε j → X i j = 0

def realRank : ℕ := min (Fintype.card {i // ε i = true}) (Fintype.card {i // ε i = false})

end Matrices

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E) {w : InfinitePlace F}

def IsSignFrame (ε : Fin n → Bool) (b : GL (Fin n) (w.Completion ⊗[F] E)) : Prop :=
  cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) b.1 * JR w.Completion J * b.1 =
    Matrix.diagonal fun i => if ε i then 1 else -1

def inFrame (τ : EmbOver E w) (b : GL (Fin n) (w.Completion ⊗[F] E)) (g : GArch σ J w) : Matrix (Fin n) (Fin n) ℂ :=
  (b⁻¹ * AdelicU.matHom w.Completion σ J g * b).1.map (infEmb τ)

end Place

end GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership

end
