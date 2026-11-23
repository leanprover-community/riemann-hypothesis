module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.HodgeTateCharacterSystems
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section

namespace GlobalTheory.CoordsOrigin
variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]

theorem constO_eq_strMap : constO G = (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.strMap G).hom := by
  ext r
  rw [GlobalTheory.HodgeTateCompare.strMap_eq]
  have h1 : (StructureSheaf.toStalk R (G.hom (origin G))).hom r =
      ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (G.hom (origin G)) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [Scheme.ΓSpecIso_inv]
    rfl
  have h2 := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.Hom.germ_stalkMap G.hom ⊤ (origin G) trivial)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  change _ = (G.hom.stalkMap (origin G)).hom ((StructureSheaf.toStalk R (G.hom (origin G))).hom r)
  rw [h1, h2]
  simp [constO, Scheme.Hom.appLE]
  first
    | (erw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]; done)
    | (erw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]; rfl)
    | (rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]; rfl)
    | (simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]; rfl)

theorem free_finite_cotangent_of_eq [Smooth G.hom] (φ : R →+* G.left.presheaf.stalk (origin G))
    (hφ : φ = (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.strMap G).hom) :
    letI : Algebra R (G.left.presheaf.stalk (origin G)) := φ.toAlgebra
    Module.Free R (RingHom.ker (evO G)).Cotangent ∧ Module.Finite R (RingHom.ker (evO G)).Cotangent := by
  subst hφ
  obtain ⟨h1, h2⟩ := GlobalTheory.HodgeTateCompare.finite_projective_of_smooth (G := G)
  change Module.Free R (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Cotangent G) ∧ Module.Finite R (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Cotangent G)
  exact ⟨Module.free_of_flat_of_isLocalRing, h1⟩

end GlobalTheory.CoordsOrigin

theorem GlobalTheory.CoordsOrigin.noetherian_free_cotangent : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (G : Over (Sp R)) [GrpObj G], Smooth G.hom → IsNoetherianRing (G.left.presheaf.stalk (origin G)) ∧
      (letI : Algebra R (G.left.presheaf.stalk (origin G)) := (constO G).toAlgebra;
        Module.Free R (RingHom.ker (evO G)).Cotangent ∧ Module.Finite R (RingHom.ker (evO G)).Cotangent) := by
  intro R _ _ _ G _ hs
  haveI := hs
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  exact ⟨inferInstance, GlobalTheory.CoordsOrigin.free_finite_cotangent_of_eq G _ (GlobalTheory.CoordsOrigin.constO_eq_strMap G)⟩
