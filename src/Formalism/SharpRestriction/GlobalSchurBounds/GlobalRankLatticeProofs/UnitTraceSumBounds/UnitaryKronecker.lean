module

public import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
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

open NumberField IsDedekindDomain TensorProduct Formalism.MainNotions.UnusedSlot33 Matrix ComplexOrder

namespace Formalism.MainNotions.Ext

def FinOrdG : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  (∀ φ : F →+* ℂ, ∃ r : F →+* ℝ, ∀ x, φ x = (r x : ℂ)) →
  ∀ (σ : E →ₐ[F] E) (k : ℕ) (J : Matrix (Fin k) (Fin k) E), IsHerm (σ : E →+* E) J → IsDef σ J →
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  ∀ U : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
    U ≤ UPts σ J (FiniteAdeleRing (𝓞 F) F) →
    IsCompact (U : Set (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) →
  ∀ y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F),
  ∀ γ ∈ UJ (σ : E →+* E) J,
    bc (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) γ ∈ U.map (MulAut.conj y).toMonoidHom →
    IsOfFinOrder γ

end Formalism.MainNotions.Ext
