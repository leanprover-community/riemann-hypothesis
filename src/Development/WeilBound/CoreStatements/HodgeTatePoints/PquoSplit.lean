module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.HtPt.Pquo

theorem split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (r : V →+* ℂ) (tV : SAB H (Sp V)), Function.Surjective r → RingHom.ker r = IsLocalRing.maximalIdeal V → ∀ P : AbPart tV (spMap r), GlobalTheory.LN.SplitOver tV.G (IsLocalRing.maximalIdeal V) := by
  intro E _ _ _ H V _ _ _ r tV hs hk P
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ →+* V ⧸ IsLocalRing.maximalIdeal V,
      ψ.comp r = Ideal.Quotient.mk (IsLocalRing.maximalIdeal V) :=
    ⟨r.liftOfRightInverse _ (Function.rightInverse_surjInv hs)
      ⟨Ideal.Quotient.mk (IsLocalRing.maximalIdeal V), by rw [hk, Ideal.mk_ker]⟩,
      RingHom.liftOfRightInverse_comp _ _ _ _⟩
  letI : Field (V ⧸ IsLocalRing.maximalIdeal V) := Ideal.Quotient.field _
  have e : spMap ψ ≫ spMap r = spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
  obtain ⟨T⟩ := GlobalTheory.SS.nonempty_torusExtension_pullback (Ω := V ⧸ IsLocalRing.maximalIdeal V) (spMap ψ) P.tK.G ⟨P.τ⟩
  obtain ⟨i, hi, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback P.tK.G (spMap ψ)).comp P.m.cart).congr e rfl)
    (isGrpPullback_pullback tV.G (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V))))
  exact GlobalTheory.exists_splitExt_isGt_of_torusExtension (V ⧸ IsLocalRing.maximalIdeal V) _ ⟨torusExtOfIso i T⟩

end PositivityTheory.HtPt.Pquo
