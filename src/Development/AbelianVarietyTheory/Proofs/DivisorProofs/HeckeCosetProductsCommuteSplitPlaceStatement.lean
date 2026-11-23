module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCosetProductsCommuteSplitPlace
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.heckeCosetProducts_commute_splitPlace : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (i i' : (blk p j t).Pl × ℕ), 1 ≤ i.2 → i.2 ≤ (Vc D j).rank → 1 ≤ i'.2 → i'.2 ≤ (Vc D j).rank → (plOf p j t i.1).under (𝓞 D.host.F) = (plOf p j t i'.1).under (𝓞 D.host.F) → ∀ c : Bridge.Gf (Vc D j) ⧸ levJ p j t, ((hkA p j t i ×ˢ hkA p j t i').filter (fun x => ((x.1 * x.2 : Bridge.Gf (Vc D j)) : Bridge.Gf (Vc D j) ⧸ levJ p j t) = c)).card = ((hkA p j t i' ×ˢ hkA p j t i).filter (fun x => ((x.1 * x.2 : Bridge.Gf (Vc D j)) : Bridge.Gf (Vc D j) ⧸ levJ p j t) = c)).card := by
  first | exact @GlobalTheory.HeckePairCount.card_pairs_comm | exact GlobalTheory.HeckePairCount.card_pairs_comm | (intros; apply GlobalTheory.HeckePairCount.card_pairs_comm <;> assumption)
