module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderConjugationStable
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory


theorem _root_.GlobalTheory.T.local_order_conjugation_stable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ O : Subring (Fv F v ⊗[F] E), IsCompact (O : Set (Fv F v ⊗[F] E)) → IsOpen (O : Set (Fv F v ⊗[F] E)) → (∀ x ∈ O, HeckeCharacterZeroLocus.SiegelWeilU.sigR (Fv F v) σ x ∈ O) → ∀ (n M : ℕ) (l : Fin n) (a : Fin n → (Fv F v ⊗[F] E)), (∀ i, a i ∈ O) → a l = 1 → MeasurePreserving (fun X : (Fin n → Fin M → (Fv F v ⊗[F] E)) => GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) l a)) (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.shear_measurePreserving | exact GlobalTheory.CompanionTheory.AvgFree.shear_measurePreserving | (intros; apply GlobalTheory.CompanionTheory.AvgFree.shear_measurePreserving <;> assumption)
