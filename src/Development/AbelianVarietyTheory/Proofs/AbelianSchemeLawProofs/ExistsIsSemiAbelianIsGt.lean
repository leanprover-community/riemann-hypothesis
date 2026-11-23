module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGrpObjSplitExtensionOfGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GeneratorSchemeProperties
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_isSemiAbelian_isGt :
    GlobalFnsSt → ∀ (S : Scheme.{0}) (E : SplitExt S),
      ∃ (G : Over S) (_ : GrpObj G), IsSemiAbelian G ∧ E.IsGt G := by
  intro hG S E
  letI := E.free
  letI := E.finite
  have hN : ∀ k, (E.O (E.basis k)).L.IsLB := fun k => (E.O (E.basis k)).isLB
  obtain ⟨G, q, u, hu⟩ := exists_generatorScheme E.B.left _ (fun k => (E.O (E.basis k)).L) hN
  obtain ⟨h₁, h₂, h₃, -, -⟩ :=
    generatorScheme_properties E.B.left _ (fun k => (E.O (E.basis k)).L) hN G q u hu
  obtain ⟨inst, hc, d, -⟩ := GlobalTheory.T.exists_grpObj_splitExtension_of_generators hG S E G q u hu h₁ inferInstance h₃
  exact ⟨Over.mk (q ≫ E.B.hom), inst, isSemiAbelian_of_isGt S E _ ⟨d⟩, ⟨d⟩⟩

end GlobalTheory
