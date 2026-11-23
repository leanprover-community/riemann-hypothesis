module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticePropertiesTransportByIsometry
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

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowLattice_properties_transport_by_isometry : ∀ (D : D7) (T : D.host.E) (F0 G' : FlagG (VS D) D.R.rS T) (g : GV D), g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ a, g (F0.fvec a) = G'.fvec a) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ → G'.z ∈ Λ → XLam Λ (lf D G') = XS D G' → (∀ c : D.host.E, c • G'.z ∈ Lsub Λ (lf D G') → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) → Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0 ∧ Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ∧ Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ∧ F0.z ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ∧ XLam (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0) = XS D F0 ∧ (∀ c : D.host.E, c • F0.z ∈ Lsub (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) := by
  first | exact @GlobalTheory.RowLatTransport.rowLat_transport | exact GlobalTheory.RowLatTransport.rowLat_transport | (intros; apply GlobalTheory.RowLatTransport.rowLat_transport <;> assumption)
