module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.UnitChoice
public import CompanionTheory.AutomorphicTheory.ThetaDilations.HfSubSmul
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsNormOneUnitShift
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
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

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.WittDiag

theorem trans_diag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R], PIW.AdelicOrbitU.UnitChoice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (D : Fin n → Rˣ) (X Y : Fin n → Fin M → R ⊗[F] E), gramR R σ J X = Matrix.diagonal (fun i => algebraMap R (R ⊗[F] E) (D i : R)) → gramR R σ J Y = gramR R σ J X → ∃ h : HA R σ J, actW R σ J h X = Y := by
  intro F E _ _ _ _ _ σ hcm R _ _ hU M J hJ n D X Y hX hY
  obtain ⟨g, hg, e⟩ := CompanionTheory.PlacePermOperatorBicommutantSpan.witt_diag (GlobalTheory.GaussMean.OneVec.sigR_sigR R hcm) (CompanionTheory.PlacePermOperatorBicommutantSpan.cT_JR' R hJ) _
    (fun i => (D i).isUnit.map _)
    (fun i t => LamUnit.exists_norm_one_sub_isUnit F E σ hcm R hU t (D i)) X Y
    (fun a b => congrFun (congrFun hX a) b)
    fun a b => congrFun (congrFun (hY.trans hX) a) b
  exact ⟨⟨g, hg⟩, funext e⟩

end GlobalTheory.CompanionTheory.SW.WittDiag
