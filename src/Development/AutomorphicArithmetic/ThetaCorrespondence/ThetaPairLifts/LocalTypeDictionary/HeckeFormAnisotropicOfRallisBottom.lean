module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAniso
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRightStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalFactorizationOfWeilDualPairStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeFormOfDoubling
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundNonsplitPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelicStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralSplitPlaceAdelicStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAnisoOfGlobalEuler
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlaceStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SiegelWeilFockAnisotropicUnconditional
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTowerCompatibility
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFormAniso
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
open GlobalTheory.Core.Rk.IP in
theorem GlobalTheory.RallisBottom.hecke_form_anisotropic_of_rallis_bottom : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ D : D7, GlobalTheory.RallisBottom.HeckeFormAniso D := by
  intro hP D
  have hU19 := GlobalTheory.T.unramifiedDoublingIntegral_inert_place
  have hPB := paramBoundOn_all_of_split_inert D (GlobalTheory.T.sphericalParameterBound_split_place D) (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU19 D)
  have hLZ := localZetaOn_all_of_split_inert D (GlobalTheory.T.unramifiedDoublingIntegral_splitPlace_adelic hP.unramifiedDoublingGL D)
    (GlobalTheory.T.unramified_doubling_integral_inert_adelic hU19 D (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU19 D))
  have hE : EulerRight D :=
    GlobalTheory.T.doubling_eulerProduct_farRight hP.cuspRapidDecay D (GlobalTheory.T.doublingSphericalFactorization_of_weilDualPair hP.weilRepresentationUnitaryPair D) hLZ hPB
  have hG : GlobalTheory.BottomRallis.GlobalFormAniso D :=
    _root_.GlobalTheory.T.theta_tower_compatibility hP.weilRepresentationUnitaryPair hP.cuspRapidDecay hP.doublingMethod D
      (_root_.UpperTheory.Lit.Sw47.siegelWeil_fock_anisotropic_unconditional D)
  exact GlobalTheory.BottomRallis.heckeFormAniso_of_global_euler D hG hE
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

theorem _root_.GlobalTheory.T.rallis_bottom_hecke_form_anisotropic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ D : D7, GlobalTheory.RallisBottom.HeckeFormAniso D := by
  first | exact @_root_.GlobalTheory.RallisBottom.hecke_form_anisotropic_of_rallis_bottom | exact _root_.GlobalTheory.RallisBottom.hecke_form_anisotropic_of_rallis_bottom | (intros; apply _root_.GlobalTheory.RallisBottom.hecke_form_anisotropic_of_rallis_bottom <;> assumption)
end
