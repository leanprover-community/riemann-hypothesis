module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem SplitAll.fieldPoint {Z : Scheme.{0}} {G : Over Z} [GrpObj G] (h : SplitAll G) (K : Type) [Field K]
    (t : Sp K ⟶ Z) : ∃ E : SplitExt (Sp K), E.IsGt ((Over.pullback t).obj G) := by
  obtain ⟨z, r, rfl⟩ : ∃ (z : Z) (r : Sp K ⟶ Sp (Z.residueField z)), t = r ≫ Z.fromSpecResidueField z :=
    ⟨_, _, (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z t).symm⟩
  obtain ⟨E, ⟨d⟩⟩ := h z
  have : IsMonHom (pullCompIso r (Z.fromSpecResidueField z) G).symm.hom :=
    inferInstanceAs (IsMonHom (pullCompIso r (Z.fromSpecResidueField z) G).inv)
  obtain ⟨E', _, _, _, _, hE'⟩ := gtBaseChange _ _ r E _ ⟨d⟩
  exact ⟨E', isGt_of_iso (pullCompIso r (Z.fromSpecResidueField z) G).symm hE'⟩

theorem isSemiAbelian_of_splitAll : ∀ (Z : Scheme.{0}) (G : Over Z) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom], SplitAll G → IsSemiAbelian G ∧ (∀ (K : Type) [Field K] (t : Sp K ⟶ Z), ∃ E : SplitExt (Sp K), E.IsGt ((Over.pullback t).obj G)) ∧ ∀ x : Z, ∃ (k : Type) (_ : Field k) (_ : Algebra (Z.residueField x) k), FiniteDimensional (Z.residueField x) k ∧ Algebra.IsSeparable (Z.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField x) k)) ≫ Z.fromSpecResidueField x)).obj G) := by
  intro Z G _ hc hs hsep hq h
  refine ⟨⟨hc, hs, hsep, hq, ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ q => ?_⟩,
    fun Ω _ _ q => ?_⟩, h.fieldPoint, fun x => ⟨Z.residueField x, inferInstance, inferInstance, inferInstance,
      inferInstance, h.fieldPoint _ _⟩⟩
  · obtain ⟨E, hE⟩ := h.fieldPoint K q
    have hg : GeometricallyConnected (pullback.snd G.hom q) :=
      (UnitRigidity.smooth_geometricallyConnected_of_isGt E _ hE).2
    rw [← (pullbackLeftPullbackSndIso G.hom q (𝟙 _) ≪≫ pullback.congrHom rfl (Category.id_comp q)).hom.homeomorph.connectedSpace_iff]
    exact pullback_of_geometrically hg.1 K (𝟙 _)
  · obtain ⟨E, hE⟩ := h.fieldPoint Ω q
    exact nonempty_torusExtension_of_isGt E _ hE

end GlobalTheory.ZJ
