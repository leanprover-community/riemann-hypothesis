module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDJNice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectral_pairing_orbital_membership : RDSPJFMem := by
  intro k r Wp Wq _ _ _ _ _ _ D F hF hcs hts
  have hpos : ∀ g ∈ tsupport F, (0 : ℝ) < Gf k r D.z D.z' g := fun g hg => (hts hg).2.2
  obtain ⟨ε, hε, hεle⟩ := hcs.isCompact.exists_forall_le' (PositiveOrbitOpen.gf_cont D.z D.z').continuousOn hpos
  have hnice : NiceAll D F := by
    refine ⟨ε, hε, hF, fun A m => compact_support_finite_class k r _ F (tsupport F) hF hcs.isCompact ?_ A m, ?_⟩
    · intro g hg
      by_contra h
      exact hg (subset_tsupport _ h)
    · intro g _ hg
      exact hεle g (subset_tsupport _ hg)
  refine ⟨(radial_orbital_niceness k r Wp Wq D F hnice).1, ?_⟩
  intro g _ hne
  by_contra hno
  push_neg at hno
  apply hne
  show ∫ p, _ ∂D.μSS = 0
  refine integral_eq_zero_of_ae ?_
  filter_upwards [B5.ae_inSS D] with p hp
  have h0 : F (B.sgs p g) = 0 := by
    by_contra h
    exact hno p hp (subset_tsupport _ h)
  show _ • _ = (0 : Wq →L[ℂ] Wp)
  simp only [B.sgs] at h0
  rw [h0]
  simp

end Formalism.FourierDecayAlt.P.CutSE
