module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimePowSmulMemValueLatticeErase
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

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

theorem _root_.GlobalTheory.T.levelPrime_pow_smul_mem_valueLattice_erase : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (Co : M.Coord), Co.Ok → ∀ w, OverT X w → X.fm.seenP w = true → ∀ (V : Finset X.A.vT) (v : X.A.vT), v ∈ V → ∀ p, ∀ y ∈ Co.valB w V p, ((X.A.T : ℂ) ^ (PtModel.lamT X i (X.fm.tauOf w v)).w ⟨0, D.R.N_pos i⟩) • y ∈ Co.valB w (V.erase v) p := by
  first | exact @GlobalTheory.LvT.pow_smul_mem_valB_erase | exact GlobalTheory.LvT.pow_smul_mem_valB_erase | (intros; apply GlobalTheory.LvT.pow_smul_mem_valB_erase <;> assumption)
