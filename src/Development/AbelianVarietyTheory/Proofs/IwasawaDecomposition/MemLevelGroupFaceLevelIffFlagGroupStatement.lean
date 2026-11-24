module

public import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLevelGroupFaceLevelIffFlagGroup
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.mem_level_group_face_level_iff_flag_group : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_red_R → ∀ (b : Bool) (t : T) (κ : GA D D.sp.X'), κ ∈ GfC D.sp.X' → ((κ ∈ levS _ R.βX (datXP R t (R.levR F b)) ↔ ∃ hq : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q, (R.B.R t).act_tie.red ⟨_, hq⟩ ∈ (F.lvl b).P) ∧ ∀ (hq : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hp : (R.B.R t).act_tie.red ⟨_, hq⟩ ∈ (F.lvl b).P), levChi _ R.βX (datXP R t (R.levR F b)) κ = ((levEnv D.sp.X' R.βX (R.datXt t)).ch ⟨_, hq⟩ : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hp⟩ : D.what₂.LLˣ) : D.what₂.LL)) := by
  first | exact @GlobalTheory.TopBridge.mem_levelSubgroup_localDatum_iff | exact GlobalTheory.TopBridge.mem_levelSubgroup_localDatum_iff | (intros; apply GlobalTheory.TopBridge.mem_levelSubgroup_localDatum_iff <;> assumption)
