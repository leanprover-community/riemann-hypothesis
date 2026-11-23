module

public import Development.EtaleCohomology.EtaleSheaves.LocSecPf
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LocSecPfA

variable (R : Type) [CommRing R]

def hEq (X : Scheme.{0}) : HomotopyEquiv ((chainsN R).obj (sch.obj X))
    ((ChainComplex.single₀ (Shv R)).obj ((free R).obj (yoneda.obj X))) :=
  ((SimplicialObject.Augmented.ExtraDegeneracy.const (yoneda.obj X)).map (free R)).homotopyEquiv

abbrev Q := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)

def isoQ (X : Scheme.{0}) : (Q R).obj ((chains R).obj (sch.obj X)) ≅ (Q R).obj (LateralTheory.E.LocSecPf.pt R X) :=
  ((ComplexShape.embeddingDownNat.extendHomotopyFunctorFactors (Shv R)).app _).symm ≪≫
  (ComplexShape.embeddingDownNat.extendHomotopyFunctor (Shv R)).mapIso (HomotopyCategory.isoOfHomotopyEquiv (hEq R X)) ≪≫
  (ComplexShape.embeddingDownNat.extendHomotopyFunctorFactors (Shv R)).app _ ≪≫
  (Q R).mapIso (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat _ 0 0 rfl)

def transIso {K K' L : Cx R} (i : (Q R).obj K ≅ (Q R).obj K') (n : ℤ) :
    CohomologyClass K L n ≃+ CohomologyClass K' L n :=
  (CohomologyClass.homAddEquiv (K := K) (L := L) (n := n)).trans
    ({ toFun := fun f => i.inv ≫ f, invFun := fun g => i.hom ≫ g,
       left_inv := fun f => by simp, right_inv := fun g => by simp,
       map_add' := fun f g => Preadditive.comp_add _ _ _ _ _ _ } : _ ≃+ _) |>.trans
    (CohomologyClass.homAddEquiv (K := K') (L := L) (n := n)).symm

theorem locSecA : LateralTheory.E.LocSecPf.LocSecA := fun R _ X F n => ⟨transIso R (isoQ R X) n⟩

end LateralTheory.E.LocSecPfA
