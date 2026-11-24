module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianLattices.StatementLat
import Formalism.PeriodIntegrals.UJClassFin
import Formalism.PeriodIntegrals.UJClassMass

@[expose] public section

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def LocInt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) (z : F) (c : 𝓞 F)
    (u : t.adicCompletion F), u ∈ t.adicCompletionIntegers F →
    algebraMap F (t.adicCompletion F) z = algebraMap F (t.adicCompletion F) (c : F) * u →
    ∃ d ∈ t.asIdeal.primeCompl, ∃ a : 𝓞 F, z * (d : F) = (c : F) * (a : F)

def tcoord {F E : Type} [Field F] [Field E] [Algebra F E] {ι : Type} (B : Module.Basis ι F E)
    (k : ι) (R : Type) [CommRing R] [Algebra F R] : E ⊗[F] R →ₗ[F] R :=
  (TensorProduct.lid F R).toLinearMap ∘ₗ TensorProduct.map (B.coord k) LinearMap.id

theorem tcoord_tmul {F E : Type} [Field F] [Field E] [Algebra F E] {ι : Type} (B : Module.Basis ι F E)
    (k : ι) (R : Type) [CommRing R] [Algebra F R] (x : E) (y : R) :
    tcoord B k R (x ⊗ₜ[F] y) = B.coord k x • y := by
  simp [tcoord]

end PI.UnitaryGroupMassFormula.UJClassMass

end
