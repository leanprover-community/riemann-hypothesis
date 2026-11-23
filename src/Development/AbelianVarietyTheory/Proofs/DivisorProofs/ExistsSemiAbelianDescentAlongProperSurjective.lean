module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedCommGroupOfPullbackProperSurjectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedOfIsPullbackSurjectiveLftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupInverseDescendsProperSurjectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupMultiplicationDescendsProperSurjectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupUnitDescendsProperSurjectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeparatedOfIsPullbackUniversallyClosedSurjectiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionGeometricFibresOfDescendedGroupStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.DescGrp

theorem quasiCompact_of_isPullback {R : Type} [CommRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) [Surjective π]
    (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left) (h : IsPullback β G'.hom G.hom π) [QuasiCompact π]
    [QuasiCompact G'.hom] : QuasiCompact G.hom := by
  have hs : Surjective β := MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹_›
  have hc : QuasiCompact (β ≫ G.hom) := by rw [h.w]; infer_instance
  rw [quasiCompact_iff] at hc ⊢
  intro U hU hK
  have := (hc U hU hK).image β.continuous
  rwa [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq _ hs.surj] at this

theorem exists_semiAbelian_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ (_ : GrpObj G) (_ : IsCommMonObj G), IsSemiAbelian G ∧ IsGrpPullback G' G π β := by
  intro R _ _ _ _ S π hp hs hi G' _ _ hG G β hsm hpb φ hφ hc
  obtain ⟨m, hm⟩ := GlobalTheory.T.group_multiplication_descends_proper_surjection R S π hp hs hi G' G β hsm hpb φ hφ hc
  obtain ⟨e, he⟩ := GlobalTheory.T.group_unit_descends_proper_surjection R S π hp hs hi G' G β hpb φ hφ hc
  obtain ⟨i, hiv⟩ := GlobalTheory.T.group_inverse_descends_proper_surjection R S π hp hs hi G' G β hsm hpb φ hφ hc
  obtain ⟨g, c, hP⟩ := GlobalTheory.T.descended_comm_group_of_pullback_proper_surjection R S π hp hs hi G' G β hsm hpb m e i hm he hiv
  haveI := hG.quasiCompact
  refine ⟨g, c, ⟨c, hsm, GlobalTheory.T.isSeparated_of_isPullback_universallyClosed_surjective' R S π inferInstance hs G' G β hpb hG.separated,
    quasiCompact_of_isPullback π G' G β hpb,
    GlobalTheory.T.geometricallyConnected_of_isPullback_surjective_lft R S π inferInstance hs G' G β hpb hG.geomConnected,
    GlobalTheory.T.torusExtension_geometricFibres_of_descended_group R S π inferInstance hs G' G β hP hG.fibres⟩, hP⟩

end GlobalTheory.DescGrp
