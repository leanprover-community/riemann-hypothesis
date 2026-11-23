module

public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
public import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel

@[expose] public section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.UG Formalism.UG.CS Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Herm Formalism.L2.GlobalTheoryTheory.Comp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def K0 (D : D7) : Coord D.sp.cm (D.sp.X 0) (Fin D.R.k) := ⟨D.sp.crd0, D.sp.gram0, D.sp.hermitianForm_base_coordinates⟩

theorem dualSub_eq {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (L : Submodule (𝓞 E) S.V) :
    flipTwoThree.dualSub S L = (Formalism.HermitianLatticesTheory.dual S.hT L).toAddSubgroup := by
  ext x
  show (∀ y ∈ L, S.hT y x ∈ (algebraMap (𝓞 E) E).range) ↔ x ∈ Formalism.HermitianLatticesTheory.dual S.hT L
  rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
  simp only [Submodule.mem_one, RingHom.mem_range]

theorem card_ringOfIntegers_quot_natCast_eq_pow (D : D7) (T : ℕ) :
    Nat.card (𝓞 D.host.E ⧸ Ideal.span {((T : ℕ) : 𝓞 D.host.E)}) = T ^ (2 * D.R.f) := by
  have h1 := Ideal.absNorm_span_singleton (((T : ℕ) : 𝓞 D.host.E))
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
  rw [h1]
  have h2 : ((T : ℕ) : 𝓞 D.host.E) = algebraMap ℤ (𝓞 D.host.E) (T : ℤ) := by simp
  rw [h2, Algebra.norm_algebraMap, RingOfIntegers.rank, Formalism.MainNotions.StandardLattice.finrank_host D]
  simp [Int.natAbs_pow]

end Formalism.L2.GlobalTheoryTheory

end
