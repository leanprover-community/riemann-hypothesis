module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
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

namespace Formalism.L2.SG.Pf.FibPart

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Steps

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def RepIn (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) : Prop :=
  ∃ F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam Z,
    Rep γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') γ.cls F'

def Pre : Prop :=
  (∀ p, Agree δ M p) ∧ (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] ∧ PrimeHyp D u (Tu D u') ∧
    PairVal.NormRepExists D u u' F0 what₂ ∧ IsRowReps D F0 what₂ ∧ EligRel u u' F0 what₂

def TupFun : Prop :=
  Pre M δ u u' F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (Z : PairVal.MatR D),
    EligAt γ w → AtMat w Z → RepIn u u' F0 what₂ γ Z → locT M δ γ = tupZ M δ u u' Z

def RepAtTup : Prop :=
  Pre M δ u u' F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)),
    Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 → ∀ Z : PairVal.MatR D, AtMat w Z → EligAt γ w →
      locT M δ γ = tupZ M δ u u' Z → RepIn u u' F0 what₂ γ Z

def OrbZT : Prop :=
  Pre M δ u u' F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (Z : PairVal.MatR D),
    EligAt γ w → AtMat w Z → RepIn u u' F0 what₂ γ Z →
      (PairVal.orbT D u u' F0 what₂ γ (zT γ)).encard = (PairVal.orbT D u u' F0 what₂ γ Z).encard

end Steps

end Formalism.L2.SG.Pf.FibPart
