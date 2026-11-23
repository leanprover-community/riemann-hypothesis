module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfCompEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteModificationIntegralElementsRegular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_finiteModification_integral_elements_regular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (n : ℕ) (U : Fin n → M.S.Opens) (b : ∀ m, Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U m)), (∀ m, IsAffineOpen (U m)) → (∀ m, (M.gp.app (U m)).hom.IsIntegralElem (b m)) → ∃ (M' : Modif R) (h : M'.S ⟶ M.S) (hgp : M'.gp ≫ h = M.gp), IsFinite h ∧ h ≫ M.π = M'.π ∧ ∀ m, ∃ c : Γ(M'.S, h ⁻¹ᵁ U m), (M'.gp.appLE (h ⁻¹ᵁ U m) (M.gp ⁻¹ᵁ U m) (le_preimage_of_comp_eq M.gp M'.gp h hgp (U m))).hom c = b m := by
  first | exact @GlobalTheory.Mum.finiteModif_regular | exact GlobalTheory.Mum.finiteModif_regular | (intros; apply GlobalTheory.Mum.finiteModif_regular <;> assumption)
