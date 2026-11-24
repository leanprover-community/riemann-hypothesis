module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentCentral
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentHorizontal
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineEigenvalue
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsSemidirectHaar
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsTorusEmbedding
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsTorusModulus
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsUnitsInvHaar
public import Mathlib.Topology.Algebra.Group.Units
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Assembly
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.OfUnfolding
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchUnimodular
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCongruenceLift
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineStabHaar
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMajorantStabCompact
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PSemidirectCovering
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerLevi
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentCocompact
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulus
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

universe u

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

variable
    (hTE : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), TorusEmbedding.Statement h v)
    (hLE : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), LineEigenvalue.Statement h v)
    (hTM : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), TorusModulus.Statement h v)
    (hSH : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), SemidirectHaar.Statement (archUnitary h v) (InfinitePlace E → ℂˣ))
    (hUI : UnitsInvHaar.Statement (InfinitePlace E))
    (hCP : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentCoordProper.Statement h v)
    (hUH : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentHorizontal.Statement h v)
    (hUZ : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentCentral.Statement h v)

variable {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : HermitianForm F E W) (v : Basis ι E W)
variable (hTE' : TorusEmbedding.Statement h v) (hLE' : LineEigenvalue.Statement h v)
    (hTM' : TorusModulus.Statement h v)
    (hSH' : SemidirectHaar.Statement (archUnitary h v) (InfinitePlace E → ℂˣ))
    (hCP' : UnipotentCoordProper.Statement h v) (hUH' : UnipotentHorizontal.Statement h v)
    (hUZ' : UnipotentCentral.Statement h v)

include hTE hLE hTM hSH hUI hCP hUH hUZ hTE' hLE' hTM' hSH' hCP' hUH' hUZ'

theorem ScalingLaw.of_remaining : ScalingLaw.Statement h v :=
  ScalingLaw.of_open
    (fun _ _ _ _ h _ v => ArchUnimodular.proof h v)
    (fun _ _ _ _ h _ v => MajorantStabCompact.proof h v)
    (fun W _ _ _ h n v => LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v)
      (hTE W h n v) (hLE W h n v) (hTM W h n v) (hSH W h n v) hUI)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => SemidirectCovering.proof _ _ _)
    (fun _ _ _ _ h _ v => StabilizerLevi.proof h v)
    (fun _ _ _ _ h _ v => UnipotentModulus.proof h v)
    (fun W _ _ _ h n v => UnipotentCocompact.proof h v (hCP W h n v) (hUH W h n v) (hUZ W h n v))
    (fun _ _ _ _ h => CongruenceLift.proof h)
    h v (fun _ _ _ _ _ => SemidirectCovering.proof _ _ _) (StabilizerLevi.proof h v)
    (UnipotentModulus.proof h v) (UnipotentCocompact.proof h v hCP' hUH' hUZ')
    (ArchUnimodular.proof h v) (MajorantStabCompact.proof h v)
    (LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v) hTE' hLE' hTM' hSH' hUI)

theorem ArithmeticCovolumeFinite.of_remaining : ArithmeticCovolumeFinite.Statement h v :=
  ArithmeticCovolumeFinite.of_open
    (fun _ _ _ _ h _ v => ArchUnimodular.proof h v)
    (fun _ _ _ _ h _ v => MajorantStabCompact.proof h v)
    (fun W _ _ _ h n v => LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v)
      (hTE W h n v) (hLE W h n v) (hTM W h n v) (hSH W h n v) hUI)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => SemidirectCovering.proof _ _ _)
    (fun _ _ _ _ h _ v => StabilizerLevi.proof h v)
    (fun _ _ _ _ h _ v => UnipotentModulus.proof h v)
    (fun W _ _ _ h n v => UnipotentCocompact.proof h v (hCP W h n v) (hUH W h n v) (hUZ W h n v))
    (fun _ _ _ _ h => CongruenceLift.proof h)
    h v (fun _ _ _ _ _ => SemidirectCovering.proof _ _ _) (StabilizerLevi.proof h v)
    (UnipotentModulus.proof h v) (UnipotentCocompact.proof h v hCP' hUH' hUZ')
    (ArchUnimodular.proof h v) (MajorantStabCompact.proof h v)
    (LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v) hTE' hLE' hTM' hSH' hUI)

theorem AdelicCovolumeFinite.of_remaining : AdelicCovolumeFinite.Statement h v :=
  AdelicCovolumeFinite.of_open
    (fun _ _ _ _ h _ v => ArchUnimodular.proof h v)
    (fun _ _ _ _ h _ v => MajorantStabCompact.proof h v)
    (fun W _ _ _ h n v => LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v)
      (hTE W h n v) (hLE W h n v) (hTM W h n v) (hSH W h n v) hUI)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => SemidirectCovering.proof _ _ _)
    (fun _ _ _ _ h _ v => StabilizerLevi.proof h v)
    (fun _ _ _ _ h _ v => UnipotentModulus.proof h v)
    (fun W _ _ _ h n v => UnipotentCocompact.proof h v (hCP W h n v) (hUH W h n v) (hUZ W h n v))
    (fun _ _ _ _ h => CongruenceLift.proof h)
    h v (fun _ _ _ _ _ => SemidirectCovering.proof _ _ _) (StabilizerLevi.proof h v)
    (UnipotentModulus.proof h v) (UnipotentCocompact.proof h v hCP' hUH' hUZ')
    (ArchUnimodular.proof h v) (MajorantStabCompact.proof h v)
    (LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v) hTE' hLE' hTM' hSH' hUI)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
