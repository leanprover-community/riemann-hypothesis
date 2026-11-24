module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
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
public import Formalism.SharpRestriction.FamCore
public import Formalism.SharpRestriction.ParConsts

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

section LocalTheory

open Formalism.MainNotions.S.Loc MeasureTheory ComplexConjugate


def FamilyVolumeFourth {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r k n : ℕ) (C : ℝ) : Prop :=
  ∀ (ϖ : 𝒪[F]), Irreducible ϖ →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  (∀ (t : Term V M r), H.IsGeneric t →
    |H.dens ϖ t.abelian₂ (H.gram (H.MMfam t)) - 1| ≤
      C * (2 * (r : ℝ) + 2) * (Nat.card 𝓀[F] : ℝ) ^ (-((k : ℤ) - 2 * r - 2))) ∧
  (∀ (t₁ t₂ : Term V M r), H.IsGeneric t₁ → H.IsGeneric t₂ → H.IsScalarPair t₁ t₂ →
    H.dens ϖ t₁.abelian₂ (H.gram (H.MMfam t₁)) = H.dens ϖ t₂.abelian₂ (H.gram (H.MMfam t₂)))

end LocalTheory

def adm6 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ U : ∀ p : PlF D, AddSubgroup (D.s.atP p).Ep, (∀ p, IsOpen (U p : Set (D.s.atP p).Ep)) →
    {p | (U p : Set (D.s.atP p).Ep) ≠ ((D.s.atP p).O : Set (D.s.atP p).Ep)}.Finite →
    ∀ x : ∀ p, (D.s.atP p).Ep, {p | x p ∉ (D.s.atP p).O}.Finite →
      ∃ t : D.host.E, ∀ p, (D.s.atP p).ιE t - x p ∈ U p

def adm7 (D : Formalism.BasicNotions.D7) : Prop :=
  (∀ M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep, (∀ p, (M p).OK) →
    ∀ x : D.host.E, x ≠ 0 →
      (Function.mulSupport fun p => (M p).modK ((D.s.atP p).ιE x)).Finite ∧
      ∏ᶠ p, (M p).modK ((D.s.atP p).ιE x) = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹) ∧
  (∀ x : D.host.E,
    (Function.mulSupport fun p : PlF D => (D.s.atP p).psiE ((D.s.atP p).ιE x)).Finite ∧
    ∏ᶠ p : PlF D, (D.s.atP p).psiE ((D.s.atP p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ D.host.E x : ℚ) : ℂ))))

def Gfin (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (T T' : ℕ) : Prop :=
  (∀ (n : ℕ) (w w' : Point D.host.E n), n ≤ D.R.rS + 1 →
    (Function.mulSupport fun p => locK M δ T T' p n w w').Finite) ∧
  (∀ (n : ℕ) (h : Point D.host.E n), n ≤ D.R.rS + 1 →
    (Function.mulSupport fun p => detNrmP M δ T T' p h).Finite) ∧
  (∀ (a s : ℕ) (t : D.host.E), t ≠ 0 → 1 ≤ a → 1 ≤ s → a + s - 1 ≤ D.R.rS + 1 →
    (Function.mulSupport fun p => (M p).modK (blkMod δ T T' p a s t)).Finite) ∧
  (∀ w w' : Point D.host.E (D.R.rS + 1), (Function.mulSupport fun p => KtopP M δ T T' p w w').Finite)

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {Y : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)}

end Family

end Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum
