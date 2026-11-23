module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfCompEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueIsIntegralOfIntegralAtPointsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtClosedFibreOfRegularAtAllTraitsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralElementAffineSectionGeneratedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageGenericBaseChangeModificatioStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSectionEverywhereOfClosedFibreStatement
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

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem locInt_of_traitReg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (k : ℕ) (s : SecK L α k), TraitReg M G L s → LocInt M G L α t hpb.w s := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s hs
  have h4 := GlobalTheory.T.integral_at_closedFibre_of_regular_at_all_traits R M G hsm hqc hgi L hL Y α t hpb k s hs
  have h5 := GlobalTheory.T.isIntegralSection_everywhere_of_closedFibre R M G hsm hqc hgi L hL Y α t hpb k s h4
  intro j W U hW hWU hWa hUa
  exact GlobalTheory.T.integral_element_affine_section_generated R M G hsm Y α t hpb W U hWU hWa hUa _
    (GlobalTheory.T.chartValue_isIntegral_of_integral_at_points L α k s j W hW hWa (GlobalTheory.T.isAffineOpen_preimage_genericBaseChange_modification R M G Y α t hpb W hWa) (fun x _ => h5 x))

end GlobalTheory.Mum
