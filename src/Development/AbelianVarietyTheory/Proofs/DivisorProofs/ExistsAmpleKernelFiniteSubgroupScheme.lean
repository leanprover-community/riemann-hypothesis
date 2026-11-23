module

public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSymmetricVeryAmple
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRelAmpleOfIsProjBy
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteClosedSubschemeRepresentsKernelAmple
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelSubgroup

theorem exists_finite_subgroup_kernel : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ (L : LB A.left) (H : Over (Sp K)) (_ : GrpObj H) (j : H ⟶ A), L.IsLB ∧ IsProjBy A.hom ∧ (∃ t : LB.Gen (Theta A L), t.IsGen) ∧ IsMonHom j ∧ IsClosedImmersion j.left ∧ IsFinite H.hom ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ j = x := by
  intro K _ _ A _ hA
  have hG : GlobalFnsSt := GlobalTheory.laws_without_cohomology.1
  obtain ⟨H₀, m, s, hH₀, hva, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple K A hA
  have hP : IsProjBy A.hom := ⟨H₀, hH₀, m, s, hva⟩
  obtain ⟨L, hL, hR⟩ := GlobalTheory.ProjFinite.exists_relAmple_of_isProjBy hP
  obtain ⟨H, j, hj, hf, hH⟩ := GlobalTheory.KernelRep.exists_finite_closed_kernel hG K A hA L hL hR
  haveI : Mono j.left := inferInstance
  haveI : Mono j := (Over.forget _).mono_of_mono_map this
  have hjK : GlobalTheory.MemKL A L j := (hH H j).2 ⟨𝟙 _, Category.id_comp _⟩
  have h1 := (hH _ (1 : 𝟙_ (Over (Sp K)) ⟶ A)).1 (GlobalTheory.memKL_one hL _)
  have hm := (hH _ ((fst H H ≫ j) * (snd H H ≫ j))).1
    (GlobalTheory.UU.InK.mul hL (hjK.comp (fst H H)) (hjK.comp (snd H H)))
  have hn := (hH _ j⁻¹).1 (GlobalTheory.UU.InK.inv hL hjK)
  obtain ⟨g, hg⟩ := GlobalTheory.PointQuot.exists_grpObj_of_mono j h1.choose hm.choose hn.choose
    h1.choose_spec hm.choose_spec hn.choose_spec
  exact ⟨L, H, g, j, hL, hP, GlobalTheory.exists_gen_theta_of_isAbelianScheme K A hA L hL, hg, hj, hf, hH⟩

end GlobalTheory.KernelSubgroup
