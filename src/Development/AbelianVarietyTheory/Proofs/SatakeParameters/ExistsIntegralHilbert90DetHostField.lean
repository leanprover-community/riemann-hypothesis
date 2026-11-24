module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemMoveLevUloc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TwU.IntegralHilbert90
open GlobalTheory.AdeleBaseChange
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def evP (P : HeightOneSpectrum (𝓞 E)) : FiniteAdeleRing (𝓞 E) E →+* P.adicCompletion E where
  toFun z := z P
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem localComponent_apply₂ (P : HeightOneSpectrum (𝓞 E)) (z : FiniteAdeleRing (𝓞 E) E) : evP P z = z P := rfl

theorem localComponent_algebraMap (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    evP P (algebraMap E (FiniteAdeleRing (𝓞 E) E) x) = algebraMap E (P.adicCompletion E) x := rfl

variable [StarRing E]

end GlobalTheory.TwU.IntegralHilbert90
