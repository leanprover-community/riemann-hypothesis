module

public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.NumericalIdentityScalar
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.AdmissibleGeneralLatticeTuple
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
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

@[expose] public section

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])

theorem pending_tuple_admissible_of_shape (hS : XShape) (hBrS : XBrS) (hBrT : XBrT) (hInj : XInj) (hSp : XSpanN) (hMid : XMid) (hU : XUnit)
    (hE : XEdge) (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.FormalGroupSystem.adm7 D X (pendT X E hfin hst hLT pos F) := by
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  intro j _ La c' L' L'' i0 h1 h2 h3 h4
  exact admissible_general_lattice_tuple X ℂ_[p] hS hBrS hBrT hInj hSp hMid hU hE (OcC p) OcC_val
    (fun o => ((pendT X E hfin hst hLT pos F).Oc_K _).2 ⟨o, rfl⟩) j La c' L' L'' i0 h1 h2 h3 h4

end Formalism.L2.PairingIndexBounds.Ent
