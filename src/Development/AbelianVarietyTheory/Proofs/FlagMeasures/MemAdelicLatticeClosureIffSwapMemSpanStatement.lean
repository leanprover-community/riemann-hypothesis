module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemAdelicLatticeClosureIffSwapMemSpan
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

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_adelicLatticeClosure_iff_swap_mem_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → Af F ⊗[F] E), y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔ (fun i => Algebra.TensorProduct.comm F (Af F) E (y i)) ∈ Formalism.MainNotions.S.lamAf (F := F) L := by
  first | exact @GlobalTheory.AdelicLatticeSwap.mem_latHat_iff_comm_mem_lamAf | exact GlobalTheory.AdelicLatticeSwap.mem_latHat_iff_comm_mem_lamAf | (intros; apply GlobalTheory.AdelicLatticeSwap.mem_latHat_iff_comm_mem_lamAf <;> assumption)
