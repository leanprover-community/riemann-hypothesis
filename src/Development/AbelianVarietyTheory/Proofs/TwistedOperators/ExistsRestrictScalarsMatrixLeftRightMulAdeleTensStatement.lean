module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

theorem _root_.GlobalTheory.T.exists_restrictScalars_matrix_leftRightMul_adeleTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ) [LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [MeasurableSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] (g : GL (Fin m) (AF F ⊗[F] E)) (a : GL (Fin n) (AF F ⊗[F] E)), ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (Λ : Matrix κ κ (AF F)) (hΛ : IsUnit Λ.det), Λ.det = Algebra.norm (AF F) ((Matrix.GeneralLinearGroup.det g ^ n * Matrix.GeneralLinearGroup.det a ^ m : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) ∧ addEquivAddHaarChar (lrCE g a) = addEquivAddHaarChar (mulVecCE Λ hΛ) := by
  first | exact @GlobalTheory.ModuLR.exists_matrix_restrictScalars_lrCE | exact GlobalTheory.ModuLR.exists_matrix_restrictScalars_lrCE | (intros; apply GlobalTheory.ModuLR.exists_matrix_restrictScalars_lrCE <;> assumption)
