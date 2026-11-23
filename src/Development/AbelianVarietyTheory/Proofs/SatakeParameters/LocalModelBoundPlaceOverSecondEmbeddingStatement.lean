module

public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalModelBoundPlaceOverSecondEmbedding
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem _root_.GlobalTheory.T.local_model_bound_place_over_second_embedding : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D), LatTied hT X Y → FillsAll hT Y → OrbitPlaces.OrbitLetterBoundsAll 11 1 → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge 11 1 K ce → ((D.what₂.places.resChar w) : ℝ) ≤ L.sc.X'' D.R.n → ∀ (Lv : Levels (Y.Fl u w hg)) (Ch : Chain Lv) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _) (Y5 : FormalGroupSystem.Pend (FormalGroupSystem.Sys.mk (D.gat u w hg) (Y.Fl u w hg) Lv Ch std vp unif eO eO_spec dG dG_spec om)), BeProp (D.what₂.places.resChar w) Y5.be → ∀ (v : Fin (D.gat u w hg).P.nV) (t : HH D), (D.gat u w hg).P.n' v = nP D (D.what₂.places.resChar w) → (∀ s : Fin ((D.gat u w hg).P.n' v), hT.gat_pos u w hg ⟨v, s⟩ = tauPl D (posPl D (D.what₂.places.resChar w) (true, t) s.val)) → ∀ i < D.R.m, Y5.LowAt i v (FOrb D (i + 1) (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce (i + 1) (D.what₂.places.resChar w) (true, t)) := by
  first | exact @GlobalTheory.TwU.LowF.lowAt_F | exact GlobalTheory.TwU.LowF.lowAt_F | (intros; apply GlobalTheory.TwU.LowF.lowAt_F <;> assumption)
