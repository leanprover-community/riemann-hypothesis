module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.CommonGen

theorem exists_common (F : Type) [Field F] [NumberField F] (Y : Var F) (V₁ V₂ : Mean4O.Cover Y) :
    ∃ (G : Scheme.{0}) (_ : IsIntegral G) (_ : GlobalTheory.IsNormalScheme G) (g : G ⟶ V₁.G) (k : G ⟶ V₂.G),
      IsFinite g ∧ IsDominant g ∧ k ≫ V₂.π = g ≫ V₁.π := by
  have : IsProper V₁.p := CommonModel.isProper_of_isProjOver V₁.ar.isProjOver
  have : IsProper (V₁.π ≫ Y.str) := MorphismProperty.of_isPullback V₁.pb ‹IsProper V₁.p›
  let Q : Scheme.{0} := pullback V₁.π V₂.π
  let a : Q ⟶ V₁.G := pullback.fst V₁.π V₂.π
  let b : Q ⟶ V₂.G := pullback.snd V₁.π V₂.π
  have : IsFinite a := inferInstanceAs (IsFinite (pullback.fst V₁.π V₂.π))
  have hs : Surjective a := inferInstanceAs (Surjective (pullback.fst V₁.π V₂.π))
  obtain ⟨η, hη⟩ := hs.surj (genericPoint V₁.G)
  let s : Q ⟶ Spec (.of F) := a ≫ V₁.π ≫ Y.str
  have : IsProper s := inferInstanceAs (IsProper (a ≫ V₁.π ≫ Y.str))
  have : CharZero (Q.residueField η) := charZero_of_injective_ringHom
    ((Scheme.ΓSpecIso (.of F)).inv ≫ s.appTop ≫ Q.Γevaluation η).hom.injective
  let u : Spec (.of (Q.residueField η)) ⟶ Q := Spec.map (Q.residue η) ≫ Q.fromSpecStalk η
  have hfin : IsFinite u.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk s η (L := Q.residueField η) (Q.residue η)
      (RingHom.FiniteType.of_surjective _ (Q.residue_surjective η)).essFiniteType
  have hu : u (IsLocalRing.closedPoint (Q.residueField η)) = η :=
    Scheme.fromSpecResidueField_apply η _
  have : IsDominant (u ≫ a) := ⟨(dense_iff_closure_eq.2 (genericPoint_spec V₁.G)).mono
    (Set.singleton_subset_iff.2 ⟨IsLocalRing.closedPoint (Q.residueField η), by
      change a (u _) = _
      rw [hu, hη]⟩)⟩
  have hd : IsDominant (u.fromNormalization ≫ a) := by
    have : IsDominant (u.toNormalization ≫ u.fromNormalization ≫ a) := by
      rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization]; infer_instance
    exact IsDominant.of_comp u.toNormalization _
  refine ⟨u.normalization, inferInstance, GlobalTheory.IsNormalScheme.normalization_of_isIntegral u,
    u.fromNormalization ≫ a, u.fromNormalization ≫ b, inferInstance, hd, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition]

end GlobalTheory.Mean4O.CommonGen
