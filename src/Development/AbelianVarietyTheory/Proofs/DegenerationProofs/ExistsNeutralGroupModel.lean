module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGrpObjOfStrictBirationalLawStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrictModelOfBirationalStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeakNeronModelBirationalGroupLawStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeakNeronModelStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelMapGenericallyOpenImmersionCalculusStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS

theorem exists_neutral_group_model : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom → ∃ (G : Model R A) (_ : GrpObj G.Y), SmConn G.Y ∧ IsMonHom G.e.hom ∧ ∃ c : ℕ, 1 ≤ c ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), ∃ s : 𝟙_ (Over (Sp R)) ⟶ G.Y, spMap (algebraMap R K) ≫ s.left = (a ^ c).left ≫ G.j := by
  intro R K _ _ _ _ _ hS A _ _ hA hP
  have h1 := hS.1
  have h3 := hS.2.2.1
  have h4 := hS.2.2.2
  obtain ⟨n, M, hI, hW⟩ := GlobalTheory.T.exists_weak_neron_model R K inferInstance A hA.smooth hA.proper hP
  obtain ⟨N, hN, c, hc, hT⟩ := GlobalTheory.T.exists_weakNeronModel_birational_groupLaw R K hS A hA n M hI hW
  obtain ⟨N', hN', hle⟩ := GlobalTheory.T.exists_strict_model_of_birational R K hS A hA N hN
  obtain ⟨G, inst, hG, he, hs⟩ := GlobalTheory.T.exists_grpObj_of_strictBirationalLaw R K hS A hA N' hN'
  obtain ⟨b1, b2, b3, -, -⟩ := GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hS
  refine ⟨G, inst, hG, he, c, hc, fun a => hs (a ^ c) ?_⟩
  have e1 : GenIso N' N (𝟙 A) := b1 A N' N hN'.1.1 hle
  have e2 : GenIso N N' (𝟙 A) := (b3 A A N' N (Iso.refl A)).1 e1
  have e3 := b2 A A A N' N N _ _ hN.1 e1 (hT a)
  have e4 := b2 A A A N' N N' _ _ hN.1 e3 e2
  simpa only [Category.id_comp, Category.comp_id] using e4

end GlobalTheory.SS
