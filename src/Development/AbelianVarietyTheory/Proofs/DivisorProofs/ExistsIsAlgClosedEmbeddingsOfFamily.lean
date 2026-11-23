module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

@[expose] public section

namespace GlobalTheory

open MvPolynomial

theorem exists_isAlgClosed_embeddings_of_family :
    ∀ (F : Type) [Field F] (I : Type) (k : I → Type) [∀ i, Field (k i)] (f : ∀ i, F →+* k i),
      ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (g : ∀ i, k i →+* L) (h : F →+* L),
        ∀ i, (g i).comp (f i) = h := by
  intro F _ I k _ f
  let K := FractionRing (MvPolynomial (Σ i, k i) F)
  let Ω := AlgebraicClosure K
  have key : ∀ i, ∃ g : k i →+* Ω, g.comp (f i) = algebraMap F Ω := by
    intro i
    letI : Algebra F (k i) := (f i).toAlgebra
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F (k i)
    let x : (Σ i, k i) → Ω := fun j => algebraMap K Ω (algebraMap (MvPolynomial (Σ i, k i) F) K (X j))
    have hx : AlgebraicIndependent F x := by
      have h0 := MvPolynomial.algebraicIndependent_X (Σ i, k i) F
      have h1 : Function.Injective (IsScalarTower.toAlgHom F (MvPolynomial (Σ i, k i) F) K) :=
        IsFractionRing.injective _ _
      have h2 : Function.Injective (IsScalarTower.toAlgHom F K Ω) :=
        (algebraMap K Ω).injective
      have := (h0.map' h1).map' h2
      exact this
    have hv : AlgebraicIndependent F (fun b : s => x ⟨i, b.1⟩) :=
      hx.comp (fun b : s => (⟨i, b.1⟩ : Σ i, k i)) (by
        intro a b hab
        exact Subtype.ext (by simpa using hab))
    let φ0 : IntermediateField.adjoin F (Set.range ((↑) : s → k i)) →ₐ[F] Ω :=
      (IntermediateField.val _).comp (hv.aevalEquivField.toAlgHom.comp hs.1.reprField)
    have halg := hs.isAlgebraic_field
    obtain ⟨φ, -⟩ := IntermediateField.exists_algHom_of_splits' φ0
      (fun (y : k i) => ⟨(Algebra.IsAlgebraic.isAlgebraic
        (R := IntermediateField.adjoin F (Set.range ((↑) : s → k i))) y).isIntegral,
        IsAlgClosed.splits _⟩)
    refine ⟨φ.toRingHom, ?_⟩
    ext y
    exact φ.commutes y
  choose g hg using key
  exact ⟨Ω, inferInstance, inferInstance, g, algebraMap F Ω, hg⟩

end GlobalTheory
