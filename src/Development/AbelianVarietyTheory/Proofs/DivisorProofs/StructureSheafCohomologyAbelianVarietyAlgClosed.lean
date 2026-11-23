module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyH1AxesPrimitiveRankStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyWedgeNoPrimitiveH2Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyStructureSheafIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyTrivialBundleAbelianStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem exists_fin_affineOpen_cover_of_compactSpace (X : Scheme.{0}) [CompactSpace X] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  obtain ⟨Us, hUs, hfin, hU⟩ :=
    X.isBasis_affineOpens.exists_finite_of_isCompact (U := ⊤) isCompact_univ
  let s := hfin.toFinset
  refine ⟨s.card, fun i => (s.equivFin.symm i).1, fun i => ?_, ?_⟩
  · have h := (s.equivFin.symm i).2
    exact hUs (hfin.mem_toFinset.mp h)
  · apply le_antisymm le_top
    rw [hU]
    refine sSup_le fun u hu => ?_
    have hs : u ∈ s := hfin.mem_toFinset.mpr hu
    refine le_iSup_of_le (s.equivFin ⟨u, hs⟩) ?_
    simp

theorem structureSheafCoh_abelianVariety_algClosed :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ),
      IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      Module.Finite K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g ∧
        GlobalTheory.AbCoh.WedgeO (OAff A.hom) ∧ GlobalTheory.AbCoh.NoPrimitiveStructureSheafH2 A ∧ GlobalTheory.AbCoh.AxesVanishingStructureSheafDegOne A := by
  intro K _ _ A _ g hA hg
  obtain ⟨hax, -, hrk⟩ := GlobalTheory.T.abelian_variety_h1_axes_primitive_rank K A g hA hg
  obtain ⟨hw, hno⟩ := GlobalTheory.T.abelian_variety_wedge_no_primitive_h2 K A g hA hg
  refine ⟨?_, hrk, hw, hno, hax⟩
  haveI : IsProper A.hom := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨n, D, hD, hcov⟩ := exists_fin_affineOpen_cover_of_compactSpace A.left
  obtain ⟨⟨e⟩, -⟩ := GlobalTheory.T.cech_cohomology_structure_sheaf_iso K A.left A.hom (Fin n) D inferInstance hD hcov
  obtain ⟨hfin, -, -⟩ := GlobalTheory.T.cech_cohomology_trivial_bundle_abelian K A g hA hg (Fin n) D hD hcov
  exact Module.Finite.equiv e.symm

end GlobalTheory.AbCoh
