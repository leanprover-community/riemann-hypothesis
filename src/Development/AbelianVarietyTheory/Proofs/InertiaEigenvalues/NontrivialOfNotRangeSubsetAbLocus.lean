module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfUnifOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)

namespace GlobalTheory.BadReductionLattice

theorem nontrivial_of_not_range_subset_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (S : Scheme.{0}) (t₀ : SAB H S) (T T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (y : Sp T.V ⟶ S) (t : SAB H (Sp T'.V)) (_ : SABMap t t₀ (spMap g ≫ y)) (P : PELUnif (IsLocalRing.maximalIdeal T'.V) t), Function.Injective g → g.Finite → ¬ Set.range y ⊆ abLocus t₀.G → Nontrivial P.D.toPre.X := by
  intro E _ _ _ H S t₀ T T' g y t m P gi gf hy
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  have hab := GlobalTheory.isAbelianScheme_of_unif_of_subsingleton GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 T'.V inferInstance
    P.D P.A t.G t.semi P.U hn
  have hp : IsProper t.G.hom := hab.proper
  apply hy
  rintro _ ⟨x, rfl⟩
  obtain ⟨x', rfl⟩ := gf.to_isIntegral.comap_surjective gi x
  exact GlobalTheory.ModelSum.range_subset_abLocus m hp ⟨x', rfl⟩

end GlobalTheory.BadReductionLattice
