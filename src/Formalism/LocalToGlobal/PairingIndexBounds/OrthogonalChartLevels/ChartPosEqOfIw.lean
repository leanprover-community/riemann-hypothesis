module

public import Formalism.LocalToGlobal.HermitianForms.TiedStep
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.HermitianColumns.StarConj
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
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CoeffProdRename

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.Pend Formalism.MainNotions Formalism.MainNotions.G.CmpJ
open Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances

namespace Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (D : D7)
  (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem sigD_conj (x : D.host.E) : sigD D (D.host.conj x) = x := by
  have h3 : ∀ y : D.host.E, sigD D y = D.host.conj y := fun y => bridge_star_holds D.R D.host y
  rw [h3, ← Formalism.L2.Herm.star_conj, ← Formalism.L2.Herm.star_conj, star_star]

end Gen


variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))


end Formalism.L2.PairingIndexBounds.F

end

section
set_option pp.fullNames true
end
