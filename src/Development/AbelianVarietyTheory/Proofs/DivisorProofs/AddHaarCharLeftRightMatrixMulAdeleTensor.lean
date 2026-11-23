module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingNormAdditive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompGlInvHaar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSkewA
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

noncomputable section
namespace GlobalTheory.ResidueEisenstein.ModMat

theorem addEquivAddHaarChar_lrCE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j m : ℕ) [LocallyCompactSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [MeasurableSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] (g : GL (Fin j) (AF F ⊗[F] E)) (a : GL (Fin m) (AF F ⊗[F] E)), addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE g a) = absE F E (Matrix.GeneralLinearGroup.det g) ^ m * absE F E (Matrix.GeneralLinearGroup.det a) ^ j := by
  intro F E _ _ _ _ _ σ _ j m _ _ _ _ g a
  obtain ⟨κ, _, _, Λ, hΛ, hdet, hchar⟩ := GlobalTheory.ModuLR.exists_matrix_restrictScalars_lrCE F E j m g a
  rw [hchar, GlobalTheory.SiegelCov.addEquivAddHaarChar_mulVecCE_adele]
  have hu : hΛ.unit = Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
      (Matrix.GeneralLinearGroup.det g ^ m * Matrix.GeneralLinearGroup.det a ^ j) := by
    ext
    simp [hdet]
  rw [hu]
  apply NNReal.eq
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GlobalTheory.NormScaleHaar.ideleModule_norm, map_mul, map_pow, map_pow]

end GlobalTheory.ResidueEisenstein.ModMat
