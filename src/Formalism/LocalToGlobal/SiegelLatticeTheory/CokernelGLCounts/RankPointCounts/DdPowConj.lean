module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalSplitTypeMixedSecond
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AaF
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfSk
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfLocGlob
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXOfMemXS
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical Matrix
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem ddPow_conj (Zd : LocDat D) {k : ℕ} (hk : k ≤ D.R.rS) {y : D.host.E} (h : y ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k) :
    D.conjF y ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D k := by
  have hne := (Formalism.L2.SG.Pf.StabIntSh.shapeNZ (D := D)).1 k
  exact (Formalism.L2.SG.Pf.StabIntSh.locGlob _ hne _).1 fun p =>
    Formalism.L2.SG.Pf.StabIntSh.locMem_conj Zd.δ Zd.M Zd.agree p hk
      ((Formalism.L2.SG.Pf.StabIntSh.locGlob _ hne _).2 h p)

theorem mem_aaF {c b : Fin (D.R.rS + 1)} (hcb : c < b) {x y : D.host.E} (hx : x ∈ FibQ.aaF D b)
    (hy : y ∈ Formalism.L2.SG.Pf.StabIntSh.ddPow D (b.val - c.val)) : x * y ∈ FibQ.aaF D c := by
  have h := FractionalIdeal.mul_mem_mul hx hy
  unfold FibQ.aaF Formalism.L2.SG.Pf.StabIntSh.ddPow at *
  rw [← zpow_add₀ (PI.NRCW.ddS_ne_zero D)] at h
  have e : -((D.R.rS : ℤ) - ((b : ℕ) : ℤ)) + -(((b.val - c.val : ℕ)) : ℤ) = -((D.R.rS : ℤ) - ((c : ℕ) : ℤ)) := by
    have : c.val ≤ b.val := le_of_lt hcb
    push_cast [this]
    ring
  rwa [e] at h

theorem sg_entry (B : Formalism.L2.SG.PairVal.MatR D) (c b : Fin (D.R.rS + 1)) :
    (Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS * B * Formalism.L2.SG.Pf.AtPt.Sg D.host.E D.R.rS) c b =
      Formalism.L2.SG.Pf.StabIntSh.bt D B c b := by
  simp [Formalism.L2.SG.Pf.AtPt.Sg, Formalism.L2.SG.Pf.StabIntSh.bt, Matrix.mul_diagonal, Matrix.diagonal_mul]

end Formalism.L2.SG.Pf.FibD
