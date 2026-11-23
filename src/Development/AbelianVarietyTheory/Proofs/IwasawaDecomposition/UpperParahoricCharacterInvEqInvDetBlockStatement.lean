module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperParahoricCharacterInvEqInvDetBlock
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.upperParahoric_character_inv_eq_inv_det_block : ∀ {κ K : Type} [CommRing κ] [Field K] {a n r b : ℕ} (h : a = n) (hn : n = r + b) (y : GL (Fin a) κ)
    (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) (χ : κˣ →* Kˣ)
    (hz : (LiftBrg.castGL h y)⁻¹ * 1 ∈ Formalism.L2.Col.HQ κ n r b),
    Formalism.L2.Col.lamQ χ n r b ⟨_, hz⟩ = (χ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 y))⁻¹ := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.LamQInv.lamQ_castGL_inv | exact GlobalTheory.Mem.R3.LiftBrg.LamQInv.lamQ_castGL_inv | (intros; apply GlobalTheory.Mem.R3.LiftBrg.LamQInv.lamQ_castGL_inv <;> assumption)
