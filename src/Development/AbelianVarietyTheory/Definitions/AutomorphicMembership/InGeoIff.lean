module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OrZeroOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
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
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.R3.Res

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.FWT Formalism.L2.Pj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T T' : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {f : T' → T} {μ : T'}
  {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D (A.comap id (f μ)) C.Q.c.F}
  (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T') (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL)))



def omDat {i : Fin D.R.m} (O : OMDat C.toCore R i Unit fun _ => (A.comap id (f μ)).μ0) :
    OMDat C.toCore (dat2 f μ R mu tw) i Unit fun _ => (A.comap f μ).μ0 := { O with }



def fwTie {κ v₀} (t : FWTie C R κ v₀) : FWTie C (dat2 f μ R mu tw) κ v₀ :=
  { alg_eq := t.alg_eq, e := t.e, ks := t.ks, kap := t.kap, pt := t.pt, nrm_eq := t.nrm_eq, laws := t.laws, chiR := t.chiR,
    hv₀ := t.hv₀, x0 := t.x0, ev0 := t.ev0, ev := t.ev }



theorem omPins {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (O : ∀ i, OMDat C.toCore R i Unit fun _ => (A.comap id (f μ)).μ0) (i : Fin D.R.m) (h : OMPins C R κ v₀ O i) :
    OMPins C (dat2 f μ R mu tw) κ v₀ (fun i => omDat mu tw (O i)) i := by
  refine ⟨h.1, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h.2
  obtain ⟨g, c, l, ht, hb⟩ := h1.c0
  refine ⟨⟨h1.field, h1.std, ?_, ⟨g, c, l, ⟨ht.ranks, ht.v0, ht.tauL_ok, ht.pl_inj, ht.q, ht.S_fin, fun t => ht.ok (f t), ht.gramR_eq,
    ht.mapR, ht.mapL, fun t => ht.coefR (f t), fun i t => ht.coefL i (f t)⟩, hb⟩, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact h1.v0



def geoHalf {ph : Fin D.R.m → ℂ} (g : GlobalTheory.RealGeo.GeoHalf C R ph) : GlobalTheory.RealGeo.GeoHalf C (dat2 f μ R mu tw) ph :=
  ⟨g.κ, g.v₀, fwTie mu tw g.fw, g.bar, fun i => omDat mu tw (g.O i), fun i => omPins mu tw g.O i (g.pins i), g.rhoGeo, g.equivAll,
    g.cTie, g.phase⟩



theorem inGeo {ph : Fin D.R.m → ℂ} {g : GlobalTheory.RealGeo.GeoHalf C R ph} (h : GlobalTheory.RealGeo.InGeo g) :
    GlobalTheory.RealGeo.InGeo (geoHalf mu tw g) :=
  ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩



theorem inGeo_iff {ph : Fin D.R.m → ℂ} {g : GlobalTheory.RealGeo.GeoHalf C R ph} :
    GlobalTheory.RealGeo.InGeo (geoHalf mu tw g) ↔ GlobalTheory.RealGeo.InGeo g :=
  ⟨fun h => ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩, inGeo mu tw⟩

end GlobalTheory.Mem.R3.Res

end
