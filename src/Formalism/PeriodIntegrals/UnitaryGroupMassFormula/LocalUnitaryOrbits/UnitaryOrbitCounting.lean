module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OBas1OfUnitV
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfNorm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfRes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.NormOneUnitFixedPoints
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.OmLocU.UnitaryOrbitCounting

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem orbAll_of_res (a : ℕ) (Y : TupV (E := E) v n a) (hRes : PI.OmLocU.Red.ResAlg σ J ψ v)
    (hUN : PI.OmLocU.Orb.UnitNorm σ J ψ v Λ) : PI.OmLocU.OrbAll σ J ψ v Λ a Y :=
  PI.OmLocU.Orb.orbAll_of_norm σ J ψ v Λ a Y (PI.OmLocU.NormOneUnitFixedPoints.normOne_of σ J ψ v hRes) hUN

theorem countU_of_res' (a : ℕ) (Y : TupV (E := E) v n a) (hRes : PI.OmLocU.Red.ResAlg σ J ψ v)
    (hUN : PI.OmLocU.Orb.UnitNorm σ J ψ v Λ) : PI.OmLocU.CountU σ J ψ v Λ a Y :=
  PI.OmLocU.Red.countU_of_res σ J ψ v Λ (PI.OmLocU.NormOneUnitFixedPoints.normOne_of σ J ψ v hRes) hUN hRes a Y

end PI.OmLocU.UnitaryOrbitCounting
