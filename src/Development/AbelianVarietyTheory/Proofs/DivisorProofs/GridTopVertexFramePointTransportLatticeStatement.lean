module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridTopVertexFramePointTransportLattice
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.gridTopVertex_frame_point_transport_lattice : ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : Consts) (G : GridData L sc) (S : Finset ℕ)
    (fr₀ : GL (Fin (G.V (.grid D.R.m D.R.m)).rank) D.host.E) (u₀ : FinPt G (.grid D.R.m D.R.m)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr₀.1 * (G.V (.grid D.R.m D.R.m)).gram * fr₀.1 = 1 →
    (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u₀.1 ∧ ∀ w ∈ P, Off S w) →
    (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr₀) ↔
        (Formalism.IndefR.Lev.finE (G.V (.grid D.R.m D.R.m)) u₀.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.grid D.R.m D.R.m))) →
    ∃ (fr : GL (Fin (G.V (.top D.R.m)).rank) D.host.E) (u : FinPt G (.top D.R.m)),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * (G.V (.top D.R.m)).gram * fr.1 = 1 ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u.1 ∧ ∀ w ∈ P, Off S w) ∧
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE (G.V (.top D.R.m)) u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.top D.R.m))) ∧
      (∀ i (k : Fin (G.V (.grid D.R.m D.R.m)).rank), fr.1 i (Formalism.L2.Col.Br.iC G.sp.topDec.rank.symm k) =
        (frameMat _ _ G.sp.topDec.ι * fr₀.1) i k) ∧
      (∀ i, fr.1 i (Formalism.L2.Col.Br.iL G.sp.topDec.rank.symm) = G.sp.topDec.a i 0) ∧
      HMul.hMul (mt (G.V (.top D.R.m)) u.1) (topEmb G) = HMul.hMul (topEmb G) (mt (G.V (.grid D.R.m D.R.m)) u₀.1) ∧
      mt (G.V (.top D.R.m)) u.1 *ᵥ topVec G = topVec G := by
  first | exact @GlobalTheory.FunObj.top_transport | exact GlobalTheory.FunObj.top_transport | (intros; apply GlobalTheory.FunObj.top_transport <;> assumption)
