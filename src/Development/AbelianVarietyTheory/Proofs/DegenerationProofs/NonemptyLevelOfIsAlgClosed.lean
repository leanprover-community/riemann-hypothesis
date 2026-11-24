module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelHasConstantThetaPt
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem GlobalTheory.nonempty_level_of_isAlgClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (M : ℕ) (ze : kˣ), (M : k) ≠ 0 → IsPrimitiveRoot ze M → Nonempty (Out.Level P M (unitOn ze)) := by
  intro k _ _ P M ze hM hz
  have hz0 : IsPrimitiveRoot (ze : k) M := IsPrimitiveRoot.coe_units_iff.mpr hz

  have hinj : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ Sp k),
      Function.Injective ((Scheme.Hom.appTop s).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) := by
    intro K _ s
    exact Function.Injective.of_comp
      ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp
        ((Scheme.Hom.appTop s).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).injective
  have hinv : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
    fun a b h => hinj k (𝟙 _) (by rw [RingHom.comp_apply, RingHom.comp_apply, h])

  have hu : IsPrimitiveRoot (unitOn ze) M := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    exact hz0.map_of_injective hinv
  obtain ⟨hL, -⟩ := GlobalTheory.abelianSchemeLaws_all

  obtain ⟨x, hx1, hx2⟩ := GlobalTheory.ConstThetaLevel.exists_symplectic_points hL k P rfl M hM (unitOn ze) hu

  obtain ⟨lev, -⟩ := GlobalTheory.exists_level_of_pairing GlobalTheory.globalFns_holds hL.weil hL.mulN (Sp k) P M (unitOn ze) hu
    (fun K _ s => by
      refine ⟨fun h0 => hM ?_, ?_⟩
      · have hf := ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp
          ((Scheme.Hom.appTop s).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).injective
        exact hf (by rw [map_natCast, map_zero]; exact h0)
      · rw [← IsPrimitiveRoot.coe_units_iff]
        exact hz0.map_of_injective (hinj K s))
    x hx1 hx2
  exact ⟨lev⟩
