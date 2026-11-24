module

public import Development.EtaleCohomology.EtaleSheaves.ChernClassExistence
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.E.ChernClassEvaluation

variable {R : Type} [CommRing R]

theorem chains_d (E : Spc) (p : ℕ) :
    ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (chainsXIso R E (p + 1)).hom ≫ (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  refine (HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := p + 1) (j := p) rfl rfl).trans ?_
  unfold chainsXIso
  congr 2
  simp [chainsN]

theorem freeGen_nat {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map f).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  unfold freeGen
  change ((((toSheafify _ ((freeP R).obj P)) ≫ sheafifyMap _ ((freeP R).map f)).app (op U)).hom _) = _
  rw [← toSheafify_naturality, NatTrans.comp_app, ModuleCat.hom_comp]
  exact congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom y)
    (by erw [ModuleCat.free_map_apply]; rfl)

def evH {A B : Shv R} (U : Scheme.{0}) (y : Sec A U) : (A ⟶ B) →+ Sec B U where
  toFun f := (f.hom.app (op U)).hom y
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evH_apply {A B : Shv R} (U : Scheme.{0}) (y : Sec A U) (f : A ⟶ B) :
    (f.hom.app (op U)).hom y = evH U y f := rfl

theorem evDelta_pf : ChernClassExistence.LeafEvDelta := by
  intro R _ E I n m hm α U
  constructor
  · intro x
    unfold ev
    rw [δ_v n m hm α (-((0 : ℕ) : ℤ)) m (by simp) n 1 (by omega) (by simp)]
    have hz : ((chains R).obj E).d (-((0 : ℕ) : ℤ)) 1 = 0 :=
      (HomologicalComplex.isZero_extend_X _ _ 1 (fun i => by show -(i : ℤ) ≠ 1; omega)).eq_of_tgt _ _
    rw [hz]
    simp [Sec.map]
  · intro p s t hs ht x
    unfold ev
    rw [δ_v n m hm α _ t ht s (-(p : ℤ)) (by omega) (by push_cast; omega), chains_d]
    simp only [Preadditive.comp_add, Category.assoc]
    simp [Sec.map, Units.smul_def, Preadditive.comp_sum, Preadditive.sum_comp, Sx.face]

    rw [evH_apply, map_zsmul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    congr 1
    rw [← evH_apply]
    simp [freeGen_nat]

theorem etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness (hmk : ChernClassExistence.LeafEvMk) (h1 : ChernClassExistence.EtaleKummerChernEdgeValuesExistNatural) (h2 : ChernClassExistence.EtaleKummerChernTriangleValuesExistNatural)
    (c1 : ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnEdges) (c2 : ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTriangles) (c3 : ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra) :
    LateralTheory.E.ChernCocycleExistenceAndUniqueness.EtaleKummerChernCocycleExists :=
  ChernClassExistence.etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness hmk evDelta_pf h1 h2 c1 c2 c3

end LateralTheory.E.ChernClassEvaluation
