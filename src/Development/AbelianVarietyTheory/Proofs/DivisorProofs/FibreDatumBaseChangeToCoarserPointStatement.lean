module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDatumBaseChangeToCoarserPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.fibreDatum_baseChange_to_coarserPoint : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R R' K : Type) [CommRing R]
    [CommRing R'] [CommRing K] (ξ : Sp R ⟶ S) (r : R →+* R') (ξ' : Sp R' ⟶ S) (f : R' →+* K)
    (t : (KeyVals.bL L ξ).L.Sec) (y : Fin g → (epsR R ⟶ KeyVals.bG G ξ)) (t' : (KeyVals.bL L ξ').L.Sec)
    (y' : Fin g → (epsR R' ⟶ KeyVals.bG G ξ')) (x : KeyIn K) (hg : x.P.g = g),
    spMap r ≫ ξ = ξ' → ⊤ ≤ ξ ⁻¹ᵁ δ.U i → KeyVals.IsLocSec σ i ξ t → KeyVals.IsLocSec σ i ξ' t' →
    (∀ F : DualNumber R →+* DualNumber R', (∀ a, F (algebraMap R _ a) = algebraMap R' _ (r a)) →
      F DualNumber.eps = DualNumber.eps → ∀ j, (y' j).left ≫ pullback.fst G.hom ξ' = spMap F ≫ (y j).left ≫ pullback.fst G.hom ξ) →
    KeyOn f x (KeyVals.bG G ξ') (KeyVals.bL L ξ') t' (fun j => y' (j.cast hg)) →
    KeyOn (f.comp r) x (KeyVals.bG G ξ) (KeyVals.bL L ξ) t (fun j => y (j.cast hg)) := by
  first | exact @GlobalTheory.KeyValsTrans.keyOn_trans | exact GlobalTheory.KeyValsTrans.keyOn_trans | (intros; apply GlobalTheory.KeyValsTrans.keyOn_trans <;> assumption)
