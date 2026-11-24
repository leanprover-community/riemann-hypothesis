module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion
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

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_adelic_lattice_iff_local_selfDual_completion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (V : HSpace E) (y : Fin V.rank → Af F ⊗[F] E), y ∈ Formalism.MainNotions.StandardLattice.latHat F E {x : Fin V.rank → E | ∑ i, x i • V.frame i ∈ V.L0} ↔ ∀ v : HeightOneSpectrum (𝓞 F), (fun i => Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (y i)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := by
  first | exact @GlobalTheory.LatticeLocalGlobal.mem_latHat_iff | exact GlobalTheory.LatticeLocalGlobal.mem_latHat_iff | (intros; apply GlobalTheory.LatticeLocalGlobal.mem_latHat_iff <;> assumption)
