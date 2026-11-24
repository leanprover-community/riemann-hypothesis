module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingYAlt
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteLocalIdentificationsEqStepZero
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.site_localIdentifications_eq_stepZero : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD g.herm u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t), (∀ j hj β v, (((Z.inTw Fl ht Gt).at' j hj).st.loc β).iw v = (lev0At g u w hg).A.iw v) ∧ (∀ j hj β v, (((Z.inTw Fl ht Gt).at' j hj).st.loc β).pl v = (lev0At g u w hg).A.pl v) ∧ (∀ j hj β β', (((Z.inTw Fl ht Gt).at' j hj).st.loc β).B = (((Z.inTw Fl ht Gt).at' j hj).st.loc β').B) ∧ (∀ j hj, ((Z.inTw Fl ht Gt).at' j hj).st.pos = Gt.gat_pos u w hg) ∧ (∀ j hj β, GlobalTheory.TwV.SplAlg (((Z.inTw Fl ht Gt).at' j hj).st.loc β)) ∧ GlobalTheory.TwV.SplAlg (lev0At g u w hg).A := by
  exact @GlobalTheory.Proof.LocOfSite.loc_eq_step0
