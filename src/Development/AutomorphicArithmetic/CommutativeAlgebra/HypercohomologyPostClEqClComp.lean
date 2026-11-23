module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

set_option backward.isDefEq.respectTransparency false in
theorem UpperTheory.hypercohomology_post_cl_eq_cl_comp :
    ∀ {M F G : Shv ℤ} (f : M ⟶ F) (g : F ⟶ G), HK.post ℤ (sgl M) g 0 (cl f) = cl (f ≫ g) := by
  intro M F G f g
  have hg : resAug F ≫ resMap ℤ g = (CochainComplex.singleFunctor (Shv ℤ) 0).map g ≫ resAug G :=
    ((GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).2.2.2.2.2.2.2 G g).1
  have key : ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F) ≫ resMap ℤ g =
      (CochainComplex.singleFunctor (Shv ℤ) 0).map (f ≫ g) ≫ resAug G := by
    rw [Category.assoc, hg, Functor.map_comp, Category.assoc]
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F))
    (Cocycle.ofHom (resMap ℤ g)) (add_zero 0)) = CohomologyClass.mk (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map (f ≫ g) ≫ resAug G))
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  rw [← key]
  simp [zcomp, Cochain.ofHom_comp]
