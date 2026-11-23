module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ZH.RatModel.exists_isAffineOpen_noetherian_integrallyClosed : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω), Geo.Tor.IsNormalScheme M.Z → ∀ (V : M.Z.Opens) (z : M.Z), z ∈ V → ∃ W : M.Z.Opens, IsAffineOpen W ∧ z ∈ W ∧ W ≤ V ∧ IsNoetherianRing (M.ringOn W) ∧ IsIntegrallyClosed (M.ringOn W) := by
  intro k Ω _ _ _ _ M hn V z hz
  obtain ⟨W, hW, hzW, hWV⟩ := exists_isAffineOpen_mem_and_subset (U := V) hz
  have hWV' : W ≤ V := hWV
  have hne : ((W : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hzW⟩
  refine ⟨W, hW, hzW, hWV', ?_, ?_⟩
  · have h1 : (M.s.appLE ⊤ W le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType M.s M.lft ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
    have h4 := h1.comp h2
    letI := ((M.s.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra
    haveI : Algebra.FiniteType k Γ(M.Z, W) := h4
    haveI : IsNoetherianRing Γ(M.Z, W) := Algebra.FiniteType.isNoetherianRing k _
    exact isNoetherianRing_of_ringEquiv _ (M.sectionsEquiv W hne)
  · haveI := GlobalTheory.ZH.RatModel.isFractionRing_ringOn hW hne
    refine (isIntegrallyClosed_iff Ω).2 fun {x} hx => ?_
    have hmem : x ∈ M.ringOn W := GlobalTheory.ZH.RatModel.mem_ringOn.2 fun z' hz' => by
      haveI := GlobalTheory.ZH.RatModel.isIntegrallyClosed_O hn z'
      have hle := GlobalTheory.ZH.RatModel.ringOn_le_O (M := M) hz'
      letI : Algebra (M.ringOn W) (M.O z') := (Subalgebra.inclusion hle).toRingHom.toAlgebra
      haveI : IsScalarTower (M.ringOn W) (M.O z') Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have hx' : IsIntegral (M.O z') x := hx.tower_top
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx'
      rw [← hy]
      exact y.2
    exact ⟨⟨x, hmem⟩, rfl⟩
