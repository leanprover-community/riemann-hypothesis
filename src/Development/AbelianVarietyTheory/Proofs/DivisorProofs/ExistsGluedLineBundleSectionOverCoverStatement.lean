module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedLineBundleSectionOverCover
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_glued_lineBundleSection_over_cover : ∀ (S : Scheme.{0}) (G : Over S) (L : LB G.left) (V : S.Opens) (κ : Type) (N : κ → S.Opens)
    (s : ∀ k, LocSec G L (N k)) (hN : ∀ k, N k ≤ V), (⨆ k, N k) = V → (∀ k, IsLocSec (s k)) →
    (∀ k k' i, resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k) (s k i) =
      resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k') (s k' i)) →
    ∃ s' : LocSec G L V, IsLocSec s' ∧ ∀ k i,
      resG _ (fun _ hx => ⟨hx.1, hN k hx.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V) (s' i) = s k i := by
  first | exact @GlobalTheory.UMin.ThBdl.locSec_glue | exact GlobalTheory.UMin.ThBdl.locSec_glue | (intros; apply GlobalTheory.UMin.ThBdl.locSec_glue <;> assumption)
