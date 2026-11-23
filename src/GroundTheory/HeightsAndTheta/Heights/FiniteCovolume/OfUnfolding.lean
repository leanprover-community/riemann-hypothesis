module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Imports
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StArchCovolumeBound
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StComplementLattice
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StLineNormalForm
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StMajorantTransport
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StReducedBasisBound
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsAdelicLattices
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsArchUnimodular
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementExtension
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsHaarParabolicCoordinates
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineStabHaar
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsMajorantStabCompact
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsSemidirectCovering
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerCovolume
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
public import Mathlib.Topology.Algebra.Group.Units
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Assembly
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PAdelicLatticeDictionary
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchCovolumeBound
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchimedeanUnitaryEquiv
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementExtension
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementLattice
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCoordEmbedBasis
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCoordLatticeFullRank
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDoubleCosetCovolume
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDualLatticeMultiple
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHaarParabolicCoordinates
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIntegralFormCovolume
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLatticePointsBelowFinite
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineNormalForm
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMajorantTransport
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PReducedBasisBound
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerCovolume
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTraceHermNondegenerate
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldAlongSubgroup
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

universe u

theorem ReducedBasisBound.full : ReducedBasisBound.Statement := ReducedBasisBound.proof

section Closed

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

section OneSpace

variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : HermitianForm F E W) (v : Basis ι E W)


omit [NumberField F] [IsTotallyReal F] [DecidableEq ι] in
theorem ArchCovolumeBound.full : ArchCovolumeBound.Statement h v :=
  ArchCovolumeBound.proof h v (CoordEmbedBasis.proof E ι) (IntegralFormCovolume.proof _ _ _)
    (TraceHermNondegenerate.proof h v) (DualLatticeMultiple.proof h) (CoordLatticeFullRank.proof v)


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem MajorantTransport.full : MajorantTransport.Statement h v := MajorantTransport.proof h v


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem ComplementExtension.full : ComplementExtension.Statement h := ComplementExtension.proof h


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem LineNormalForm.full : LineNormalForm.Statement h := LineNormalForm.proof h


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem ComplementLattice.full [FiniteDimensional E W] : ComplementLattice.Statement h :=
  ComplementLattice.proof h


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem LatticePointsBelowFinite.full : LatticePointsBelowFinite.Statement h v :=
  LatticePointsBelowFinite.proof h v

theorem ArchimedeanUnitaryEquiv.full : ArchimedeanUnitaryEquiv.Statement h v :=
  ArchimedeanUnitaryEquiv.proof h v

theorem AdelicLatticeDictionary.full : AdelicLatticeDictionary.Statement h v :=
  AdelicLatticeDictionary.proof h v

end OneSpace

theorem LatticeOrbitsFiniteBelow.full (N : ℕ) : LatticeOrbitsFiniteBelow.{u} F E N :=
  LatticeOrbitsFiniteBelow.of_steps ReducedBasisBound.full
    (fun _ _ _ _ h _ v => ArchCovolumeBound.full h v) (fun _ _ _ _ h _ v => MajorantTransport.full h v)
    (fun _ _ _ _ h => ComplementExtension.full h) (fun _ _ _ _ h => LineNormalForm.full h)
    (fun _ _ _ _ h => ComplementLattice.full h) N

section Dimension

variable {W : Type u} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
variable (h : HermitianForm F E W)

theorem LatticeOrbitsFinite.full : LatticeOrbitsFinite.Statement h :=
  LatticeOrbitsFinite.step_of h (LatticeOrbitsFiniteBelow.full _) ReducedBasisBound.full
    (ArchCovolumeBound.full h _) (MajorantTransport.full h _) (ComplementExtension.full h)
    (LineNormalForm.full h) (ComplementLattice.full h)

theorem LinePairOrbitsFinite.full : LinePairOrbitsFinite.Statement h :=
  LinePairOrbitsFinite.full_of h (LatticeOrbitsFiniteBelow.full _) (ComplementExtension.full h)
    (LineNormalForm.full h) (ComplementLattice.full h)

theorem ScalingLaw.of_unfolding {ι : Type*} [Fintype ι] [DecidableEq ι] (v : Basis ι E W)
    (hU : UnfoldingIntegral.Statement h v) : ScalingLaw.Statement h v :=
  ScalingLaw.full_of h v (LinePairOrbitsFinite.full h) hU

end Dimension

end Closed

section Adelic

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AdelicCovolumeFinite.of_covolume (h : HermitianForm F E W) (v : Basis ι E W)
    (hC : ArithmeticCovolumeFinite.Statement h v) : AdelicCovolumeFinite.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  AdelicCovolumeFinite.full_of h v (LatticeOrbitsFinite.full h) hC (ArchimedeanUnitaryEquiv.full h v)
    (AdelicLatticeDictionary.full h v) (DoubleCosetCovolume.proof _ _ _)

theorem HaarParabolicCoordinates.of_open (h : HermitianForm F E W) (v : Basis ι E W)
    (hAU : ArchUnimodular.Statement h v) (hMS : MajorantStabCompact.Statement h v)
    (hLS : LineStabHaar.Statement h v) : HaarParabolicCoordinates.Statement h v :=
  HaarParabolicCoordinates.proof h v (ParabolicDecomposition.full h v) hAU hMS hLS

end Adelic

section Open

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

variable
    (hAU : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), ArchUnimodular.Statement h v)
    (hMS : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), MajorantStabCompact.Statement h v)
    (hLS : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), LineStabHaar.Statement h v)
    (hSD : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W) (x₀ w₀ : W)
      (h' : HermitianForm F E (hypComplement h x₀ w₀)) (m : ℕ)
      (v' : Basis (Fin m) E (hypComplement h x₀ w₀)),
      SemidirectCovering.Statement (vecFixGroup h v x₀) (archUnitary h' v') (unipRadical h v x₀))
    (hSL : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), StabilizerLevi.Statement h v)
    (hUM : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentModulus.Statement h v)
    (hUC : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentCocompact.Statement h v)
    (hCL : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), CongruenceLift.Statement h)

include hAU hMS hLS hSD hSL hUM hUC hCL

theorem CovolumeFiniteBelow.of_open (N : ℕ) : CovolumeFiniteBelow.{u} F E N :=
  CovolumeFiniteBelow.of_steps ReducedBasisBound.full
    (fun _ _ _ _ h _ v => ArchCovolumeBound.full h v) (fun _ _ _ _ h _ v => MajorantTransport.full h v)
    (fun _ _ _ _ h => ComplementExtension.full h) (fun _ _ _ _ h => LineNormalForm.full h)
    (fun _ _ _ _ h => ComplementLattice.full h) (fun _ _ _ _ _ _ _ _ => UnfoldAlongSubgroup.proof _ _)
    (fun W _ _ _ h n v => HaarParabolicCoordinates.of_open h v (hAU W h n v) (hMS W h n v)
      (hLS W h n v))
    (fun W _ _ _ h n v hB => StabilizerCovolumeFinite.proof h v hB (hSD W h n v) (hSL W h n v)
      (hUM W h n v) (hUC W h n v) (hCL W h))
    (fun _ _ _ _ h _ v => LatticePointsBelowFinite.full h v) N

variable {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : HermitianForm F E W) (v : Basis ι E W)

variable (hSD' : ∀ (x₀ w₀ : W) (h' : HermitianForm F E (hypComplement h x₀ w₀)) (m : ℕ)
      (v' : Basis (Fin m) E (hypComplement h x₀ w₀)),
      SemidirectCovering.Statement (vecFixGroup h v x₀) (archUnitary h' v') (unipRadical h v x₀))
    (hSL' : StabilizerLevi.Statement h v) (hUM' : UnipotentModulus.Statement h v)
    (hUC' : UnipotentCocompact.Statement h v)

include hSD' hSL' hUM' hUC'

theorem StabilizerCovolumeFinite.of_open : StabilizerCovolumeFinite.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  StabilizerCovolumeFinite.proof h v
    (CovolumeFiniteBelow.of_open hAU hMS hLS hSD hSL hUM hUC hCL _) hSD' hSL' hUM' hUC' (hCL W h)

variable (hAU' : ArchUnimodular.Statement h v) (hMS' : MajorantStabCompact.Statement h v)
    (hLS' : LineStabHaar.Statement h v)

include hAU' hMS' hLS'

theorem UnfoldingIntegral.of_open : UnfoldingIntegral.Statement h v :=
  UnfoldingIntegral.full_of h v (fun _ => UnfoldAlongSubgroup.proof _ _)
    (HaarParabolicCoordinates.of_open h v hAU' hMS' hLS')
    (StabilizerCovolumeFinite.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC')

theorem ScalingLaw.of_open : ScalingLaw.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  ScalingLaw.of_unfolding h v
    (UnfoldingIntegral.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC' hAU' hMS' hLS')

theorem ArithmeticCovolumeFinite.of_open : ArithmeticCovolumeFinite.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  ArithmeticCovolumeFinite.step_of h v (LatticeOrbitsFiniteBelow.full _) ReducedBasisBound.full
    (ArchCovolumeBound.full h v) (MajorantTransport.full h v) (ComplementExtension.full h)
    (LineNormalForm.full h) (ComplementLattice.full h) (fun _ => UnfoldAlongSubgroup.proof _ _)
    (HaarParabolicCoordinates.of_open h v hAU' hMS' hLS')
    (StabilizerCovolumeFinite.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC')
    (LatticePointsBelowFinite.full h v)

theorem AdelicCovolumeFinite.of_open : AdelicCovolumeFinite.Statement h v :=
  AdelicCovolumeFinite.of_covolume h v
    (ArithmeticCovolumeFinite.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC' hAU' hMS'
      hLS')

end Open

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
