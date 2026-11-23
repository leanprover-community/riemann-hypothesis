module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ECure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralRedivisionTermEquivKeepsTermData
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists

@[expose] public section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ t : RT Y u u', (Formalism.L2.SG.FourParts.termIsId t ↔ Formalism.L2.SG.FourParts.termIsId (eRT Z Y u u' t)) ∧ (Formalism.L2.SG.FourParts.termInS t ↔ Formalism.L2.SG.FourParts.termInS (eRT Z Y u u' t)) ∧ (t.relevant ↔ (eRT Z Y u u' t).relevant) ∧ (t.FeqF ↔ (eRT Z Y u u' t).FeqF) ∧ (t.generic ↔ (eRT Z Y u u' t).generic) ∧ t.G = (eRT Z Y u u' t).G ∧ (∀ p, Formalism.L2.SG.Saturated.termBBne t p ↔ Formalism.L2.SG.Saturated.termBBne (eRT Z Y u u' t) p) ∧ Formalism.L2.SG.PairVal.ptOf t = Formalism.L2.SG.PairVal.ptOf (eRT Z Y u u' t) ∧ Formalism.L2.SG.PairVal.massTerm t = Formalism.L2.SG.PairVal.massTerm (eRT Z Y u u' t) ∧ Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) t = Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) (reY Z Y).δ (reY Z Y).M) (eRT Z Y u u' t)) ∧ ∀ w, Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w = Formalism.L2.SG.PairVal.meanCount (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) w := by
  first | exact @GlobalTheory.Mem.SRe.eRT_keeps_term_data | exact GlobalTheory.Mem.SRe.eRT_keeps_term_data | (intros; apply GlobalTheory.Mem.SRe.eRT_keeps_term_data <;> assumption)
