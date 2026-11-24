module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.QuadSubfield

namespace GlobalTheory.PlaceComponents

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem emb_mem (σ : D.host.E →+* ℂ) (x : D.host.E) : σ x ∈ Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map σ.toRatAlgHom).isAlgebraic

variable (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}

end GlobalTheory.PlaceComponents
