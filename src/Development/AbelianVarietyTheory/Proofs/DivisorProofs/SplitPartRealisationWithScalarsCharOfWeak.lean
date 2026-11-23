module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReScalNonzeroIndexPlaceIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPartNonzeroIndexPlacesTwistedStatement
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

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

theorem splitPartRealisationWithScalars_char_of_weak : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.R.toRealDat.ExAt → SingleIndexPlacesAreTwisted p → (R2 p).Char (F2 p) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hE hW
  have hc := Formalism.IndefR.Links.RealDat3.characterisation_of_weak p.charW hE
  exact GlobalTheory.BigOn.char_charOf D _ _ _ p.P.A3.A _ p.R.toRealDat (F2 p) hc.lev ⟨hc.grp.red_R, hc.grp.red_L, hc.grp.levels, hc.grp.record, hc.grp.chiW⟩ hc.fam hc.models hc.chain hc.thP
    ⟨GlobalTheory.T.splitPart_nonzeroIndexPlaces_twisted D L hT Gi Gl Kc Y cX ex Csz p hW, hc.tup.mu_off, hc.tup.mu_used, hc.tup.mu_ne, hc.tup.mu_conj, hc.tup.mu_on⟩

end GlobalTheory.BigOn
