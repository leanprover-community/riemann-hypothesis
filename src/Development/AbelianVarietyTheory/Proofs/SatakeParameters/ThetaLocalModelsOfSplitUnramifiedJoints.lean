module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointSiteChainComparedCarriesAdmittedSystemStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem modelsOK_of_joints : Lt.AdmAtEnt2 → Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex), (∀ μ, DV.Used D μ → JointsAt t μ) → (∀ u, ex.tw.e0 u D.what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _)) → OrbitPlaces.Stab0 D → 2 * rG L.sc ≤ D.R.k → GlobalTheory.TwU.ModelsOK D Gl ex.cmp Dx ex.tw := by
  intro hA hC D L hT Gi Gl Kc Dx cX ex t hJ h0 hS hk
  classical
  refine ⟨h0, fun μ u w hg => if h : DV.Used D μ ∧ D.what₂.places.resChar w ∉ Dx.Qp μ then
      ⟨Classical.choose (hJ μ h.1 u w hg h.2),
        chainAt (Classical.choose (Classical.choose_spec (Classical.choose_spec (hJ μ h.1 u w hg h.2)))) hT⟩
    else ⟨Gl.Lv u w hg, Gl.Ch u w hg⟩, ?_⟩
  intro μ hU u w hg hq
  have hP : DV.Used D μ ∧ D.what₂.places.resChar w ∉ Dx.Qp μ := ⟨hU, hq⟩
  dsimp only
  have key : ∀ x : (Σ Lv : Levels (Gl.Fl u w hg), Chain Lv),
      x = ⟨_, chainAt (Classical.choose (Classical.choose_spec (Classical.choose_spec (hJ μ hP.1 u w hg hP.2)))) hT⟩ →
      GlobalTheory.TwU.CmpLite D ex.cmp ex.tw u μ w hg x.2 ∧ GlobalTheory.TwU.SiteAdm D u w hg (Gl.Fl u w hg) x.1 x.2 := by
    rintro x rfl
    exact GlobalTheory.T.jointSite_chain_compared_carries_admittedSystem hA hC t
      (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hJ μ hP.1 u w hg hP.2))))).some
      hU hS hk
  exact key _ (dif_pos hP)

end GlobalTheory.TwV
