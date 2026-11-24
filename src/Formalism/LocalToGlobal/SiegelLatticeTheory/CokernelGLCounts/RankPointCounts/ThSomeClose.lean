module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefNotInt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBAt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThSomePf
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem thSome_holds {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) {u u' : D.what₂.Word}
    (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    {F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hrows : IsRowReps D F0 what₂) (hNR : NormRepElig u u' F0 what₂) :
    ThSome M δ u u' F0 what₂ := by
  refine thSome_holds_of hA hNR fun γ w hγ p a b => ?_
  obtain ⟨Λ, hΛ, F', hF'⟩ := dnInDens_of hNR hrows γ w hγ
  exact PI.CntNotIntW.integral_on_pairs_holds D δ M hA u u' hT F0 what₂ hrows Λ hΛ (zT γ) F' hF' p a b

end Formalism.L2.SG.Pf
