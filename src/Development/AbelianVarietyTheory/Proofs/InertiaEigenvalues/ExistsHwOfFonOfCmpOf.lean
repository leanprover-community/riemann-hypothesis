module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicKernelTiltInvariantsFaithfulStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalWachFunctorStatement
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

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL

theorem exists_hwOf_fonOf_cmpOf : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)), (∀ (l : ℕ) [Fact l.Prime], LocTied l (L l) (A l)) → (∀ (l : ℕ) [Fact l.Prime], WachEx (A l)) → ∃ (H : HWOf L) (F : FonOf L A H), Nonempty (CmpOf L A H F) := by
  intro L A hT hW
  have key : ∀ (l : ℕ) [Fact l.Prime], ∃ H : LocHW l (L l), ∃ F : LocFon l (L l) (A l) H,
      Nonempty (LocCmpT l (L l) (A l) H F) := fun l _ =>
    GlobalTheory.T.exists_local_wach_functor l (L l) (A l) (hT l) (GlobalTheory.T.cyclotomicKernel_tilt_invariants_faithful l (L l) (A l)) (hW l)
  choose H F hC using key
  exact ⟨fun l _ => H l, fun l _ => F l, ⟨fun l _ => (hC l).some⟩⟩

end GlobalTheory.HWL
