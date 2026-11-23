module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellOpenDomain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

open MeasureTheory Topology
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem averaging_bump_holds : ACBump := by
  intro k r Wp Wq _ _ _ _ D K hK hKQ
  have : LocallyCompactSpace (B.Mat k r) :=
    (inferInstance : LocallyCompactSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  have hcont : ContinuousOn (fun q => B.gq D q) (JF.QDom k r D.z D.z') :=
    (Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn D 0).continuousOn
  have hgK : IsCompact ((fun q => B.gq D q) '' K) := hK.image_of_continuousOn (hcont.mono hKQ)
  have hsub : (fun q => B.gq D q) '' K ⊆ Q.OmPlus k r D.z D.z' := by
    rintro _ ⟨q, hq, rfl⟩
    exact (Formalism.FourierDecayAlt.P.big_cell_domain k r Wp Wq D q (hKQ hq)).2
  obtain ⟨L, hLc, hKL, hLO⟩ := exists_compact_between hgK (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open D.z D.z') hsub
  obtain ⟨φ₀, hsupp, hsmooth, hrange⟩ :=
    (isOpen_interior : IsOpen (interior L)).exists_contDiff_support_eq (n := ⊤)
  have hts : tsupport φ₀ ⊆ L := by
    unfold tsupport
    rw [hsupp]
    exact closure_minimal interior_subset hLc.isClosed
  refine ⟨φ₀, hsmooth, fun g => (hrange ⟨g, rfl⟩).1, hLc.of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans hLO, fun q hq => ?_⟩
  have hin : B.gq D q ∈ Function.support φ₀ := by
    rw [hsupp]; exact hKL ⟨q, hq, rfl⟩
  exact lt_of_le_of_ne (hrange ⟨_, rfl⟩).1 (Ne.symm hin)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
