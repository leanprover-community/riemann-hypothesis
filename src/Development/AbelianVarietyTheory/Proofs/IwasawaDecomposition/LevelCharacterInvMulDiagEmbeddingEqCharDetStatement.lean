module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterInvMulDiagEmbeddingEqCharDet
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

theorem _root_.GlobalTheory.T.levelCharacter_inv_mul_diagEmbedding_eq_char_det : ∀ {κ K : Type} [CommRing κ] [Field K] {a n r t : ℕ} (h : a = n) (hn : n = r + t) (hra : r ≤ a)
    (hrn : r ≤ n) (y : GL (Fin a) κ) (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) (χ : κˣ →* Kˣ)
    (hz : (LiftBrg.castGL h y)⁻¹ * Formalism.L2.Col.diagEmb κ hrn (Formalism.L2.DIV.upperLeftBlock hra y) ∈ Formalism.L2.Col.HKV κ n r t),
    Formalism.L2.Col.lamKV χ n r t ⟨_, hz⟩ = χ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 y) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.LamKV.lamKV_inv_mul_diagEmb | exact GlobalTheory.Mem.R3.LiftBrg.LamKV.lamKV_inv_mul_diagEmb | (intros; apply GlobalTheory.Mem.R3.LiftBrg.LamKV.lamKV_inv_mul_diagEmb <;> assumption)
