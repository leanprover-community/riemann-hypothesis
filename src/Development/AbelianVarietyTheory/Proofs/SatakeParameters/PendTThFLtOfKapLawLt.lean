module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.HkLatTupUpdate
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.TwU

theorem pendT_ThF_lt_of_kapLawLt : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (g : GL3Theta.G1 p) (hLT : LTIso g) (T : Type) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T) (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]), letI := wittFractionAlgebraCp p; letI := algKfC E.toCEmb; KapLawLt X ℂ_[p] (thFOf X pos F) → (∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → (pendT X E hfin hst hLT pos F).ThF j La La' = thFOf X pos F j La La') ∧ ∀ v, ∀ j < X.mm, XiEx X ℂ_[p] (thFOf X pos F) v j → XiEx X ℂ_[p] (pendT X E hfin hst hLT pos F).ThF v j := by
  intro p _ X _ E hfin hst g hLT T pos F
  intro hK
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  have h1 : ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
      (pendT X E hfin hst hLT pos F).ThF j La La' = thFOf X pos F j La La' := by
    rintro j hj ⟨c, L⟩ La' hL hL'
    change thFN X ℂ_[p] hfin (thGeo X ℂ_[p] hfin (thFOf X pos F)) j (c, L) La' = _
    rw [thN_eq]
    generalize delt X hfin j c L = δ
    have hL2 : (X.Pj j).IsLatTup ((X.Lv.lev j c).smul δ⁻¹ L) := (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ δ⁻¹ L).2 hL
    have := hK j hj c _ La' δ hL2 hL'
    rw [lsmul_lsmul_inv] at this
    exact this.symm
  refine ⟨h1, ?_⟩
  rintro v j hj ⟨Ξ, u, u', hu, hu', hΞ⟩
  refine ⟨Ξ, u, u', hu, hu', fun La La' hL hL' => ?_⟩
  rw [h1 j hj La La' hL hL']
  exact hΞ La La' hL hL'

end GlobalTheory.TwU
