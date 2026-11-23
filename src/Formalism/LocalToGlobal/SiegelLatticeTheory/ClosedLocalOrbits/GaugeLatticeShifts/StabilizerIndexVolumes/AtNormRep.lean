module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StClosed
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

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
  (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
  (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)

def Hyps : Prop :=
  TermStable D u u' ∧ TermEqIff D u u' ∧ TermFun D u u' ∧ PrimeHyp D u (Tu D u') ∧ (VS D).SigOK ∧
    IsRowReps D F0 what₂

def AtNormRep (C : Term D u u' F0 what₂ → Point D.host.E (D.R.rS + 1) →
    LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) → MatR D → Prop) : Prop :=
  Hyps D u u' F0 what₂ → (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) →
    ∀ (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
      (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : MatR D),
      t.relevant → t.generic → NormRep t w F' L U → Gval (lf D F0) F' ≠ 0 → C t w F' L

def AinSt : Prop :=
  StClosed → AtNormRep D u u' F0 what₂ δ M fun _ w _ _ =>
    (stabInt D u u' δ M w : Set (GLR D)) ⊆ StSet (ptMat w)

def DeltaAE : Prop :=
  (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) →
    {p : Formalism.MainNotions.S.LocalSplitGroups.PlF D |
      Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) ∉ (D.s.atP p).O}.Finite

def ABddOf : Prop :=
  DeltaAE D δ M → AtNormRep D u u' F0 what₂ δ M fun _ w _ _ => BddDen (stabInt D u u' δ M w)

def ACong : Prop :=
  AtNormRep D u u' F0 what₂ δ M fun _ w _ _ => CongIn (ptMat w) (stabInt D u u' δ M w)

def BinSt : Prop :=
  StClosed → AtNormRep D u u' F0 what₂ δ M fun t w F' L =>
    (stabAut D u u' F0 what₂ t F' L : Set (GLR D)) ⊆ StSet (ptMat w)

def BBdd : Prop :=
  AtNormRep D u u' F0 what₂ δ M fun t _ F' L => BddDen (stabAut D u u' F0 what₂ t F' L)

def BCong : Prop :=
  AtNormRep D u u' F0 what₂ δ M fun t w F' L => CongIn (ptMat w) (stabAut D u u' F0 what₂ t F' L)

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
