module

public import Formalism.LocalToGlobal.Divisibility.Tuples
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling

namespace Formalism.L2.DIV

section Proved

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem mem_tupGrp {S : Set ℕ} (ξ : Chr F E L) : ξ ∈ tupGrp F E L S ↔
    ((ratId F E).range ≤ ξ.ker ∧ (∃ N : ℕ, 0 < N ∧ congN F E N ≤ ξ.ker) ∧ IsOfFinOrder ξ) ∧
      (idF F E).range ≤ ξ.ker ∧ (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ¬ GoodPl E S v → inertAt E v ≤ ξ.ker := by
  simp only [tupGrp, finChar, Subgroup.mem_inf, Subgroup.mem_iInf, mem_kills, CommGroup.mem_torsion]
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    exact ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
    exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

end Proved

section ProvedK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {K : Type} [Field K] [NumberField K] [StarRing K] {S : Set ℕ}

end ProvedK

theorem Tup.good {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
    {S : Set ℕ} (ξ : Tup F E L S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ Qprime (ξ : Chr F E L)) : GoodPl E S v := by
  by_contra hg
  exact hv (((mem_tupGrp (ξ : Chr F E L)).mp ξ.2).2.2.2 v hg)

def IsConjOf {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) : Prop :=
  σ ≠ AlgHom.id F E ∧ (∀ e, σ (σ e) = e) ∧ ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e

def DetInUnitaryOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E), IsUnit J.det →
    ∀ g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), Matrix.GeneralLinearGroup.det g ∈ U1 σ

def QprimeFinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (ξ : Chr F E L), ξ ∈ openChr F E L → (Qprime ξ).Finite

def ResCharEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]
    (ξ : Chr F E L), (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) →
    ∀ P : HeightOneSpectrum (𝓞 E), ∃! χ, IsResChar ξ P χ

end Formalism.L2.DIV

end
