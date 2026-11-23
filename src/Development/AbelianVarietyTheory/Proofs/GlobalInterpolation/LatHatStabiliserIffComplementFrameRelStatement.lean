module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatHatStabiliserIffComplementFrameRel
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold

@[expose] public section

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

theorem _root_.GlobalTheory.T.latHat_stabiliser_iff_complement_frameRel : StabTransitive → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E → ∀ (M M' : ℕ) (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E) (B : Matrix (Fin M) (Fin M') E) (x : Fin 1 → Fin M → E), M' + 1 = M → IsHermND σ J → IsHermND σ J' → Formalism.UG.cT (σ : E →+* E) B * J * B = J' → (∀ j, hE σ J (x 0) (fun i => B i j) = 0) → hE σ J (x 0) (x 0) ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin M → E)) (L' : Set (Fin M' → E)), IsSelfDualLat σ J L → ∀ β : F, (β = 1 ∨ β = -1) → x 0 ∈ L → hE σ J (x 0) (x 0) = algebraMap F E β → (∀ y, y ∈ L' ↔ B *ᵥ y ∈ L) → ∀ (g : HA (AF F) σ J) (g' : HA (AF F) σ J'), g ∈ Hstab (AF F) σ J x → FrameRel J J' B g g' → (g ∈ stab σ J (L : Set (Fin M → E)) ↔ g' ∈ stab σ J' L') := by
  first | exact @GlobalTheory.StabFrame.stab_iff_of_frameRel | exact GlobalTheory.StabFrame.stab_iff_of_frameRel | (intros; apply GlobalTheory.StabFrame.stab_iff_of_frameRel <;> assumption)
