module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaSectionsRatioCoordinatesOverlap
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.localThetaSections_ratio_coordinates_overlap : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (G : Over M.Z) [GrpObj G]
    (L : LB G.left) (n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (v : SecM G L 1 (Over.mk M.pt)),
    PCrd (M.pt ≫ h) c →
    (∀ (N N' : M.Z.Opens) (s : LocSec G L N) (s' : LocSec G L N') (w : SecM G L 1 (Over.mk M.pt)),
      GenIs M.pt s w → GenIs M.pt s' w → ∀ i,
        resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
          resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N') (s' i)) →
    ∀ (a b : Fin (n + 1)) (sa : LocSec G L (h ⁻¹ᵁ chart k n a)) (sb : LocSec G L (h ⁻¹ᵁ chart k n b)),
      (((h ⁻¹ᵁ chart k n a : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt sa ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • v)) →
      (((h ⁻¹ᵁ chart k n b : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt sb ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c b)⁻¹ • v)) →
      ∀ i, resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n a)) (sa i) =
        resG _ (fun _ hx => hx.2 : L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤
            G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)))
          ((G.hom.app _).hom ((h.app _).hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b))) *
        resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n b)) (sb i) := by
  first | exact @GlobalTheory.UMin.ThBdl.cross_ratio_sections | exact GlobalTheory.UMin.ThBdl.cross_ratio_sections | (intros; apply GlobalTheory.UMin.ThBdl.cross_ratio_sections <;> assumption)
