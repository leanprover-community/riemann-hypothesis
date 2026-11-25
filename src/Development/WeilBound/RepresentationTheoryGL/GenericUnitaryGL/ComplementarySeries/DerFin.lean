module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLength
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspProdCharTransport
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestDerivativeOfProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.WhittakerModels.WhitCuspOfSegCuspGeneric
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Mathlib.RingTheory.PicardGroup
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.DerFin
@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.BZMir
open scoped TensorProduct

namespace PositivityTheory.RgGu.NR.DerFin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Base

variable (ψ : AddChar k Circle) {n t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def phi (n t : ℕ) : Levi k (fun a : Fin 2 => Fin (![n, t] a)) →* GL (Fin n) k × GL (Fin t) k :=
  (Pi.evalMonoidHom (fun a : Fin 2 => GL (Fin (![n, t] a)) k) 0).prod
    (Pi.evalMonoidHom (fun a : Fin 2 => GL (Fin (![n, t] a)) k) 1)

def lift2 {n t : ℕ} (g : GL (Fin n) k) (h : GL (Fin t) k) : Levi k (fun a : Fin 2 => Fin (![n, t] a)) :=
  fun a => match a with
    | ⟨0, _⟩ => g
    | ⟨1, _⟩ => h
    | ⟨i + 2, hi⟩ => absurd hi (by omega)

theorem phi_lift2 {n t : ℕ} (g : GL (Fin n) k) (h : GL (Fin t) k) : phi n t (lift2 g h) = (g, h) := rfl

theorem phi_surjective (n t : ℕ) : Function.Surjective (phi (k := k) n t) := by
  rintro ⟨g, h⟩
  exact ⟨lift2 g h, phi_lift2 g h⟩

theorem phi_continuous (n t : ℕ) : Continuous (phi (k := k) n t) :=
  (continuous_apply 0).prodMk (continuous_apply 1)

theorem finLen (hc : Continuous ψ) (h1 : ψ ≠ 1) (Mr : Representation ℂ (GL (Fin n) k × GL (Fin t) k) V)
    (hMs : IsSmooth Mr) (hM : HasFiniteLength Mr) :
    HasFiniteLength (twAct Mr (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _) (inl_stab ψ n t)) :=
  by apply _root_.CompanionTheory.RgGu.NR.DerFin.finLen <;> assumption

end Base

end PositivityTheory.RgGu.NR.DerFin

namespace PositivityTheory.RgGu.NR

open PositivityTheory.RgGu.NR.DerFin

theorem derFin_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h : DerEquiv k) : DerFin k := by
  intro ψ hc h1 n j V _ _ π hs hi
  obtain ⟨E⟩ := h ψ n j V π
  have hfl : HasFiniteLength π := GlobalTheory.SmGL.hasFiniteLength_of_isIrreducible hi
  have hJ : HasFiniteLength (jac (two (stdSum (show n + (j + 1) = n + j + 1 from rfl))) π) :=
    (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).2.1 _ _ _ _ V π hs hfl
  have hJU : HasFiniteLength (jacU₂ (stdSum (show n + (j + 1) = n + j + 1 from rfl)) π) :=
    (hasFiniteLength_comp_iff _ _ (leviTwo k (Fin n) (Fin (j + 1))).surjective).2
      ((GlobalTheory.JacquetBlocks.hasFiniteLength_twist_iff _ _).1 hJ)
  have hJs : IsSmooth (jacU₂ (stdSum (show n + (j + 1) = n + j + 1 from rfl)) π) :=
    isSmooth_comp (isSmooth_jacU _ hs) _ (continuous_leviTwo k)
  exact HasFiniteLength.of_equiv (finLen ψ hc h1 _ hJs hJU) E.symm

end PositivityTheory.RgGu.NR
