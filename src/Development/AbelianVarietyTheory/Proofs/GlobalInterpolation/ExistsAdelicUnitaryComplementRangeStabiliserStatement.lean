module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelicUnitaryComplementRangeStabiliser
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele

@[expose] public section

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

theorem _root_.GlobalTheory.T.exists_adelic_unitary_complement_range_stabiliser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M M' : ℕ) (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E) (B : Matrix (Fin M) (Fin M') E) (x : Fin 1 → Fin M → E), M' + 1 = M → IsHermND σ J → IsHermND σ J' → Formalism.UG.cT (σ : E →+* E) B * J * B = J' → (∀ j, hE σ J (x 0) (fun i => B i j) = 0) → hE σ J (x 0) (x 0) ≠ 0 → ∃ φ : HA (AF F) σ J' →* HA (AF F) σ J, Continuous φ ∧ Function.Injective φ ∧ φ.range = Hstab (AF F) σ J x ∧ (∀ g, FrameRel J J' B (φ g) g) ∧ ∀ g, φ g ∈ ratPts (AF F) σ J ↔ g ∈ ratPts (AF F) σ J' := by
  first | exact @GlobalTheory.StabiliserOfVector.exists_hom_range_stabiliser | exact GlobalTheory.StabiliserOfVector.exists_hom_range_stabiliser | (intros; apply GlobalTheory.StabiliserOfVector.exists_hom_range_stabiliser <;> assumption)
