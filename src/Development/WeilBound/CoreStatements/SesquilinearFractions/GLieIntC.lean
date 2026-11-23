module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinearStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
public import Development.WeilBound.CoreStatements.SesquilinearFractions.GLieIntB
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
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace PositivityTheory.Xgf.isogeny_decomposition_product

variable {R : Type} [CommRing R]

theorem lc (C : Out.PolAV (Sp R)) (v : epsR R ⟶ C.A) (hv : IsLieBasis ![v]) (V : Type) [CommRing V] (f : R →+* V) :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module V E) (M : LieModel C.A (spMap f ≫ 𝟙 (Sp R)) E)
      (b : Module.Basis (Fin 1) V E), (M.pt (b 0)).left = spMap (dualMap f) ≫ v.left := by
  obtain ⟨E0, i0, m0, ⟨M0⟩⟩ := lieModel_exists (Sp R) C.A R (𝟙 (Sp R))
  obtain ⟨b0, hb0⟩ := basis_of_lieBasis v hv M0
  obtain ⟨E1, i1, m1, ⟨M1⟩⟩ := lieModel_exists (Sp R) C.A V (spMap f ≫ 𝟙 (Sp R))
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear (Sp R) C.A R V f (𝟙 _) E0 E1 M0 M1
  letI : Algebra R V := f.toAlgebra
  letI : Module R E1 := Module.compHom E1 f
  haveI : IsScalarTower R V E1 := ⟨fun r x e => by
    show (f r * x) • e = f r • (x • e)
    rw [mul_smul]⟩
  let jR : E0 →ₗ[R] E1 :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun r e => by
        show j (r • e) = f r • j e
        exact j.map_smulₛₗ r e }
  haveI : SmoothOfRelativeDimension C.g C.A.hom := C.smoothDim
  haveI : Smooth C.A.hom := by
    first
    | exact SmoothOfRelativeDimension.smooth C.g C.A.hom
    | exact SmoothOfRelativeDimension.smooth C.g
    | exact SmoothOfRelativeDimension.smooth (n := C.g)
  have hbc : IsBaseChange V jR := GlobalTheory.T.lie_model_isBaseChange (Sp R) C.A R V (𝟙 _) E0 E1 M0 M1 jR (fun e => hj e)
  refine ⟨E1, i1, m1, M1, hbc.basis b0, ?_⟩
  rw [IsBaseChange.basis_apply]
  have h := hj (b0 0)
  unfold LieModel.Lifts at h
  have h' := (Category.comp_id (M1.pt (j (b0 0))).left).symm.trans h
  show (M1.pt (j (b0 0))).left = _
  rw [h', hb0]

end PositivityTheory.Xgf.isogeny_decomposition_product

end
